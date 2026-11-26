"""Find the obligations in a Python source and write the checkers that test them.

An obligation is something PastaLean turns into a theorem: a *property function* (a body of `let`s and
one `assert`, optionally under an `if` guard — `def agree(xs): if len(xs) >= 1: assert f(xs) == g(xs)`)
or a *contract* (`Requires`/`Ensures` with `Result()`). For each one we write two ordinary Python
functions, `pl_pre_<name>` (the precondition) and `pl_chk_<name>` (the property, `Result()` replaced by
a call to the function). The same text then runs under CPython and is compiled into BOTH Lean twins, so
the three worlds judge the exact same predicate.
"""

from __future__ import annotations

import ast
import builtins
import re
import copy
from dataclasses import dataclass, field

from ..pysyntax import called_functions, strip_contract_decorators

CONTRACT_MARKERS = {"Requires", "Ensures", "Invariant", "Decreases", "Assume", "Assert"}
CHECKER_PREFIX = "pl_"


@dataclass
class Obligation:
    kind: str                      # "property" | "contract"
    name: str                      # the Python function
    params: list[tuple[str, str | None]]
    pre: str | None                # Python expression, or None
    chk: str                       # Python expression (contract: over `pl_result`)
    lets: list[str] = field(default_factory=list)
    theorem: str | None = None     # the Lean theorem PastaLean emits, when it has one
    ensures: list[tuple[str, str]] = field(default_factory=list)   # (as written, over `pl_result`)
    raises: list[str] = field(default_factory=list)   # exceptions the contract allows (`raises:` in a docstring)
    post_src: str | None = None    # `pl_post_<name>`: the function returning its postcondition (see `_post_copy`)

    @property
    def pre_fn(self) -> str:
        return f"{CHECKER_PREFIX}pre_{self.name}"

    @property
    def chk_fn(self) -> str:
        return f"{CHECKER_PREFIX}chk_{self.name}"


def _marker(stmt: ast.stmt) -> str | None:
    """The contract marker a statement is (`Requires(...)` etc.), if any."""
    if isinstance(stmt, ast.Expr) and isinstance(stmt.value, ast.Call) and isinstance(stmt.value.func, ast.Name):
        if stmt.value.func.id in CONTRACT_MARKERS:
            return stmt.value.func.id
    return None


def _strip_docstring(body: list[ast.stmt]) -> list[ast.stmt]:
    if body and isinstance(body[0], ast.Expr) and isinstance(body[0].value, ast.Constant) \
            and isinstance(body[0].value.value, str):
        return body[1:]
    return body


def _params(fn: ast.FunctionDef) -> list[tuple[str, str | None]]:
    args = fn.args.posonlyargs + fn.args.args
    return [(a.arg, ast.unparse(a.annotation) if a.annotation is not None else None) for a in args]


class _ResultToVar(ast.NodeTransformer):
    def visit_Call(self, node: ast.Call):
        self.generic_visit(node)
        if isinstance(node.func, ast.Name) and node.func.id == "Result" and not node.args:
            return ast.copy_location(ast.Name("pl_result", ast.Load()), node)
        return node


def _mentions_result(e: ast.AST) -> bool:
    return any(isinstance(n, ast.Call) and isinstance(n.func, ast.Name) and n.func.id == "Result"
               for n in ast.walk(e))


def _property(fn: ast.FunctionDef) -> Obligation | None:
    """`lets…; assert E` or `lets…; if G: assert E` — PastaLean's property-function shape."""
    body = _strip_docstring(fn.body)
    if not body or fn.args.vararg or fn.args.kwarg:
        return None
    *lets, last = body
    if not all(isinstance(s, ast.Assign) and len(s.targets) == 1 and isinstance(s.targets[0], ast.Name)
               for s in lets):
        return None
    pre = None
    if isinstance(last, ast.If) and not last.orelse and len(last.body) == 1 and isinstance(last.body[0], ast.Assert):
        pre, last = ast.unparse(last.test), last.body[0]
    if not isinstance(last, ast.Assert):
        return None
    return Obligation("property", fn.name, _params(fn), pre, ast.unparse(last.test),
                      [ast.unparse(s) for s in lets], theorem=fn.name)


def _contract(fn: ast.FunctionDef) -> Obligation | None:
    body = _strip_docstring(fn.body)
    requires = [s.value.args[0] for s in body if _marker(s) in ("Requires", "Assume") and s.value.args]
    # plain assignments before the last `Requires` (`n = len(graph)`) are the precondition's context
    last_req = max((i for i, s in enumerate(body) if _marker(s) in ("Requires", "Assume")), default=-1)
    lets = [ast.unparse(s) for s in body[:max(last_req, 0)] if isinstance(s, ast.Assign) and _marker(s) is None]
    ensures = [s.value.args[0] for s in ast.walk(fn)
               if isinstance(s, ast.stmt) and _marker(s) in ("Ensures", "Assert")
               and s.value.args and _mentions_result(s.value.args[0])]
    if not ensures:
        return None
    pre = _conj([ast.unparse(r) for r in requires])
    clauses = [(ast.unparse(e), ast.unparse(_ResultToVar().visit(copy.deepcopy(e)))) for e in ensures]
    chk = _conj([c for _, c in clauses])
    thm = f"{fn.name}_spec" if fn.name.startswith("_") else f"{fn.name}_correct"
    return Obligation("contract", fn.name, _params(fn), pre, chk, lets=lets, theorem=thm, ensures=clauses)


class _Rename(ast.NodeTransformer):
    """Rename variables (`{"self": "p"}`; `__return__`/`_`/`result` → `pl_result` for a contract's result)."""

    def __init__(self, mapping: dict[str, str]):
        self.mapping = mapping

    def visit_Name(self, node):
        new = self.mapping.get(node.id)
        return ast.copy_location(ast.Name(new, node.ctx), node) if new else node


def _conj(exprs: list[str]) -> str | None:
    """`(a) and (b)`, or `None` when there is nothing to conjoin."""
    return " and ".join(f"({e})" for e in exprs) if exprs else None


def _foreign_contract(fn: ast.FunctionDef) -> Obligation | None:
    """CrossHair's other contract syntaxes: docstring `pre:` / `post:` / `raises:` lines (PEP 316, with
    `__return__` or `_` for the result) and icontract's `@require(lambda ...)` / `@ensure(lambda ...)`."""
    pres, posts, raises = [], [], []
    doc = ast.get_docstring(fn) or ""
    for line in doc.splitlines():
        head, sep, rest = line.strip().partition(":")
        if not sep or not rest.strip():
            continue
        if head == "pre":
            pres.append(rest.strip())
        elif head == "post":
            e = ast.parse(rest.strip(), mode="eval").body
            posts.append((rest.strip(), ast.unparse(_Rename({"__return__": "pl_result", "_": "pl_result"}).visit(e))))
        elif head == "raises":
            raises += [r.strip() for r in rest.split(",") if r.strip()]
    for d in fn.decorator_list:
        if isinstance(d, ast.Call) and d.args and isinstance(d.args[0], ast.Lambda):
            name = d.func.attr if isinstance(d.func, ast.Attribute) else getattr(d.func, "id", "")
            body = d.args[0].body
            if name == "require":
                pres.append(ast.unparse(body))
            elif name == "ensure":
                posts.append((ast.unparse(body), ast.unparse(_Rename({"result": "pl_result"}).visit(copy.deepcopy(body)))))
    if not posts:
        return None
    pre = _conj(pres)
    chk = _conj([c for _, c in posts])
    return Obligation("contract", fn.name, _params(fn), pre, chk, ensures=posts, raises=raises)


class _ReturnPost(ast.NodeTransformer):
    """`return e` → `pl_result = e; return <post>`, outside nested functions and lambdas."""

    def __init__(self, post: ast.expr):
        self.post = post

    def visit_FunctionDef(self, node):
        return node

    visit_AsyncFunctionDef = visit_FunctionDef

    def visit_Lambda(self, node):
        return node

    def visit_Return(self, node):
        value = node.value or ast.Constant(None)
        return [ast.copy_location(ast.Assign([ast.Name("pl_result", ast.Store())], value), node),
                ast.copy_location(ast.Return(copy.deepcopy(self.post)), node)]


def _post_copy(fn: ast.FunctionDef, ob: Obligation, module_names: set[str]) -> str | None:
    """A postcondition that reads the function's locals (`Ensures(base ** Result() >= n)`) cannot be checked
    after the call. Then the checker calls `pl_post_<f>`: `f` with its contracts stripped and each
    `return e` replaced by the postcondition evaluated at that point, locals in scope."""
    post = ast.parse(ob.chk, mode="eval").body
    bound = {n.id for n in ast.walk(post) if isinstance(n, ast.Name) and isinstance(n.ctx, ast.Store)}
    free = {n.id for n in ast.walk(post) if isinstance(n, ast.Name) and isinstance(n.ctx, ast.Load)}
    free -= bound | {p for p, _ in ob.params} | {"pl_result"} | module_names | set(dir(builtins))
    assigned = {t.id for n in ast.walk(fn) for t in ast.walk(n)
                if isinstance(n, (ast.Assign, ast.AugAssign, ast.AnnAssign, ast.For)) and isinstance(t, ast.Name)
                and isinstance(t.ctx, ast.Store)}
    if not free or not free <= assigned:
        return None
    g = _StripMarkers().visit(copy.deepcopy(fn))
    g.name = f"{CHECKER_PREFIX}post_{fn.name}"
    g.decorator_list = []
    g.returns = ast.Name("bool", ast.Load())
    rewrite = _ReturnPost(post)
    body = []
    for st in _strip_docstring(g.body):
        r = rewrite.visit(st)
        body += r if isinstance(r, list) else [r]
    g.body = body or [ast.Pass()]
    if not isinstance(g.body[-1], ast.Return):
        g.body += [ast.Assign([ast.Name("pl_result", ast.Store())], ast.Constant(None)), ast.Return(copy.deepcopy(post))]
    return ast.unparse(ast.fix_missing_locations(g))


def _class_invariants(tree: ast.Module) -> dict[str, list[str]]:
    """PEP 316 class invariants (`inv:` lines in a class docstring), by class name."""
    out: dict[str, list[str]] = {}
    for node in tree.body:
        if isinstance(node, ast.ClassDef):
            invs = [line.strip()[4:].strip() for line in (ast.get_docstring(node) or "").splitlines()
                    if line.strip().startswith("inv:") and line.strip()[4:].strip()]
            if invs:
                out[node.name] = invs
    return out


def collect(source: str) -> list[Obligation]:
    """Every testable obligation among the module's top-level functions. A parameter whose class has
    invariants (`inv:`) is only tested on instances that satisfy them, as CrossHair does."""
    tree = ast.parse(source)
    invariants = _class_invariants(tree)
    module_names = {n.name for n in tree.body if isinstance(n, (ast.FunctionDef, ast.ClassDef))}
    module_names |= {t.id for n in tree.body if isinstance(n, ast.Assign) for t in n.targets if isinstance(t, ast.Name)}
    module_names |= {(a.asname or a.name).split(".")[0] for n in tree.body if isinstance(n, (ast.Import, ast.ImportFrom))
                     for a in n.names}
    called = called_functions(tree)
    out: list[Obligation] = []
    for node in tree.body:
        if not isinstance(node, ast.FunctionDef) or node.name.startswith(CHECKER_PREFIX):
            continue
        # a property-shaped function the module calls is a helper (PastaLean emits a `def`, not a theorem)
        ob = (None if node.name in called else _property(node)) or _contract(node) or _foreign_contract(node)
        if ob is None:
            continue
        if ob.kind == "contract":
            ob.post_src = _post_copy(node, ob, module_names)
        extra = [ast.unparse(_Rename({"self": n}).visit(ast.parse(inv, mode="eval").body))
                 for n, a in ob.params if a in invariants for inv in invariants[a]]
        if extra:
            ob.pre = _conj(([ob.pre] if ob.pre else []) + extra)
        out.append(ob)
    return out


def _signature(ob: Obligation) -> str:
    return ", ".join(f"{n}: {a}" if a else n for n, a in ob.params)


_BARE_ANNOTATIONS = {None, "dict", "list", "set", "tuple", "Dict", "List", "Set", "Tuple"}


def refine_params(program: str, obs: list[Obligation]) -> None:
    """Complete missing or bare (`d: dict`) parameter annotations with the types TypeInfer infers for the
    function or its checkers, so the checkers (which only pass the parameters on) are typed too."""
    from ..typeinfer.engine import infer_source
    try:
        funcs = {f.qualname: f.params for f in infer_source(lean_module(program, obs)).functions}
    except Exception:
        return
    def refined(n: str, a: str | None, views: list[dict[str, str]]) -> str | None:
        inferred = next((v[n] for v in views if n in v and "Any" not in v[n]), None)
        if a is None and inferred is None and any(v.get(n) == "Any" for v in views):
            # the function takes a dynamic value (`len(string)` fits a str or a list): so do its checkers
            return "Any"
        if a in _BARE_ANNOTATIONS:
            return inferred or a
        # `head: ListNode` whose body tests `head is None`: the function takes `Optional[ListNode]`, and
        # every checker must take what the function takes
        return inferred if inferred in (f"Optional[{a}]", f"{a} | None") else a

    for ob in obs:
        views = [funcs.get(n, {}) for n in (ob.name, ob.pre_fn, ob.chk_fn)]
        ob.params = [(n, refined(n, a, views)) for n, a in ob.params]


_OLD = re.compile(r"\b__old__\.([A-Za-z_][A-Za-z0-9_]*)")


def checker_source(obs: list[Obligation], cpython: bool = False) -> str:
    """`pl_pre_*` / `pl_chk_*` for each obligation, as Python appended to the module. `__old__.p` (PEP 316's
    pre-call snapshot) reads a copy of `p` taken before the call: a deep copy under CPython, a plain
    binding in the Lean twins, whose values are not shared."""
    blocks = []
    for ob in obs:
        sig = _signature(ob)
        lets = "".join(f"    {l}\n" for l in ob.lets)
        blocks.append(f"def {ob.pre_fn}({sig}) -> bool:\n{lets}    return {ob.pre or 'True'}\n")
        if ob.kind == "contract":
            args = ", ".join(n for n, _ in ob.params)
            olds = sorted(set(_OLD.findall(ob.chk)))
            chk = _OLD.sub(r"pl_old_\1", ob.chk)
            snap = "".join(f"    pl_old_{n} = {'__import__("copy").deepcopy(' + n + ')' if cpython else n}\n"
                           for n in olds)
            if ob.post_src:
                blocks.append(ob.post_src + "\n")
                pre, stmt, tail = "", f"return {CHECKER_PREFIX}post_{ob.name}({args})", ""
            else:
                pre, stmt, tail = snap, f"pl_result = {ob.name}({args})", f"    return {chk}\n"
            # A `raises:` exception is allowed behaviour, in both twins as under CPython.
            run = (f"    try:\n        {stmt}\n    except ({', '.join(ob.raises)},):\n        return True\n"
                   if ob.raises else f"    {stmt}\n")
            blocks.append(f"def {ob.chk_fn}({sig}) -> bool:\n{pre}{run}{tail}")
        else:
            blocks.append(f"def {ob.chk_fn}({sig}) -> bool:\n{lets}    return {ob.chk}\n")
    return "\n\n" + "\n\n".join(blocks)


class _StripMarkers(ast.NodeTransformer):
    """Remove contract marker statements (CPython cannot evaluate `Ensures(… Result() …)`)."""

    def _clean(self, body):
        kept = [s for s in body if _marker(s) is None]
        return kept or [ast.Pass()]

    def generic_visit(self, node):
        super().generic_visit(node)
        for attr in ("body", "orelse", "finalbody"):
            # an empty `orelse` stays empty (a `pass` there would turn a loop into `while … else`)
            block = getattr(node, attr, None)
            if isinstance(block, list) and block:
                setattr(node, attr, self._clean(block))
        return node


def _any_import(obs: list[Obligation]) -> str:
    """`from typing import Any` when a checker parameter is typed `Any` (see `refine_params`)."""
    return "from typing import Any\n" if any(a == "Any" for ob in obs for _, a in ob.params) else ""


def cpython_module(source: str, obs: list[Obligation]) -> str:
    """The module as CPython should run it: markers stripped, a stub `contracts`, plus the checkers."""
    tree = _StripMarkers().visit(ast.parse(source))
    strip_contract_decorators(tree)   # CPython calls the function itself, not icontract's wrapper
    tree.body = [s for s in tree.body
                 if not (isinstance(s, ast.ImportFrom) and s.module in ("contracts", "contract_passta"))]
    ast.fix_missing_locations(tree)
    return _any_import(obs) + ast.unparse(tree) + "\n" + checker_source(obs, cpython=True)


def _called_names(nodes) -> set[str]:
    return {c.func.id for n in nodes for c in ast.walk(n) if isinstance(c, ast.Call) and isinstance(c.func, ast.Name)}


def asserts_raise(source: str, obs: list[Obligation]) -> str:
    """`assert c, m` as `if not (c): raise AssertionError(m)` in the functions the preconditions call: a
    precondition is evaluated, not proved, and both Lean twins otherwise drop the check (the provable
    one keeps it as a proof obligation). Edited line by line, so comments (`# type:`) survive."""
    tree = ast.parse(source)
    defs = {n.name: n for n in tree.body if isinstance(n, ast.FunctionDef)}
    own = {ob.name for ob in obs}
    todo = _called_names(ast.parse(e, mode="eval") for ob in obs for e in [ob.pre or "True"])
    todo |= _called_names(ast.parse(line) for ob in obs for line in ob.lets)
    reach: set[str] = set()
    while todo:
        f = todo.pop()
        if f in defs and f not in reach and f not in own:
            reach.add(f)
            todo |= _called_names([defs[f]])
    asserts = [a for f in reach for a in ast.walk(defs[f]) if isinstance(a, ast.Assert)]
    if not asserts:
        return source
    lines = source.splitlines()
    for a in sorted(asserts, key=lambda a: a.lineno, reverse=True):
        first, last = lines[a.lineno - 1], lines[a.end_lineno - 1]
        # `assert` sharing a line with other statements (`x = 1; assert x`): left alone
        if first[:a.col_offset].strip() or last[a.end_col_offset:].strip():
            continue
        msg = ast.get_source_segment(source, a.msg) if a.msg else ""
        test = ast.get_source_segment(source, a.test)
        pad = first[:a.col_offset]
        lines[a.lineno - 1:a.end_lineno] = [f"{pad}if not ({test}):", f"{pad}    raise AssertionError({msg})"]
    return "\n".join(lines)


def lean_module(program: str, obs: list[Obligation]) -> str:
    """The module PastaLean translates: the program (`asserts_raise` of the original, so its theorems are
    emitted) plus the checkers."""
    return _any_import(obs) + program.rstrip() + "\n" + checker_source(obs)


def reads_stdin(source: str) -> bool:
    """Whether the module reads standard input (`input()` or `sys.stdin`)."""
    tree = ast.parse(source)
    return any((isinstance(n, ast.Call) and isinstance(n.func, ast.Name) and n.func.id == "input")
               or (isinstance(n, ast.Attribute) and n.attr == "stdin") for n in ast.walk(tree))


def equiv_source(source: str, f: str, g: str) -> str:
    """A property function `equiv_f_g` asserting `f(x) == g(x)` on `f`'s parameters, under `f`'s
    `Requires` when it has any (`g` should agree wherever `f` is specified)."""
    fns = {n.name: n for n in ast.parse(source).body if isinstance(n, ast.FunctionDef)}
    for name in (f, g):
        if name not in fns:
            raise ValueError(f"no top-level function `{name}`")
    fn = fns[f]
    params = _params(fn)
    sig = ", ".join(f"{n}: {a}" if a else n for n, a in params)
    args = ", ".join(n for n, _ in params)
    requires = [ast.unparse(s.value.args[0]) for s in _strip_docstring(fn.body)
                if _marker(s) in ("Requires", "Assume") and s.value.args]
    check = f"assert {f}({args}) == {g}({args})"
    body = (f"    if {' and '.join(f'({r})' for r in requires)}:\n        {check}\n" if requires
            else f"    {check}\n")
    return f"\n\ndef equiv_{f}_{g}({sig}):\n{body}"

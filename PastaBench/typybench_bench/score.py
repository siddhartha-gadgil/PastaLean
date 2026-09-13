"""Local TypyBench scoring with PastaLean: Python extracts type maps, LEAN computes TypeSim.

For each repo:
  * ground truth: `original_repo` files → IR (via node_visitor) → read the `annotation`/`returns`
    fields (already type-node JSON).
  * prediction:   `repo_without_types` files → raw IR → Lean `inferRepo` (one fixpoint) → read the
    inferred `_ty`/`_ret_ty`/`_bench_ty`.
Both are keyed identically (`module::func@arg`, `module::func::return`, `module::scope::var`); the two
maps go to the exe's `scoreRepo` task, which computes TypeSim / exact / missing IN LEAN.

Function params and returns align exactly (signatures survive desugar/SSA); locals are matched by name
(SSA `x'v1`→`x`), a best-effort subset. Usage:
    python typybench_bench/score.py <dataset_dir> [--parallel-repos N] [--repo NAME]

`--parallel-repos` is how many PROJECTS run at once (default 1: one at a time, each using the whole
machine); it is NOT a thread count. Threads-per-project are sized automatically.
"""
from __future__ import annotations
import argparse, json, os, subprocess, sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from multiprocessing import Pool

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))
from pastalean.transpile import driver
from pastalean import paths

EXE = str(Path(paths.LAKE_BIN_DIR) / "typeinfer")


def module_name(rel: Path) -> str:
    parts = list(rel.with_suffix("").parts)
    if parts and parts[-1] == "__init__":
        parts = parts[:-1]
    return ".".join(parts)


def raw_ir(py: Path):
    try:
        return json.loads(driver.translate_to_json(py.read_text(encoding="utf-8"), str(py),
                                                    best_effort=True, infer_only=True, resolve_imports=False))
    except Exception:  # noqa: BLE001
        return None


def _strip_ssa(n: str) -> str:
    return n.split("'")[0]


def _contains_yield(stmts) -> bool:
    """Does this statement list contain a `yield`/`yield from`, NOT descending into nested defs?
    Such a function is a generator, whose return type is `Iterator[...]`."""
    def scan(n):
        if isinstance(n, dict):
            nt = n.get("node_type")
            if nt in ("FunctionDef", "AsyncFunctionDef"):
                return False
            if nt in ("Yield", "YieldFrom"):
                return True
            return any(scan(v) for v in n.values())
        if isinstance(n, list):
            return any(scan(x) for x in n)
        return False
    return any(scan(s) for s in stmts)


def generator_return_keys(untyped) -> dict:
    """Every generator function's return-key → its yield SHAPE, from the SOURCE AST (our IR
    best-effort-strips `yield` from complex bodies, so the raw AST is the reliable signal). The shape
    is a `tuple[PyAny, …]` node when all `yield a, b` are tuples of one arity (so `Iterator[tuple[?,?]]`
    beats a bare `Iterator` against a `Iterator[tuple[X, Y]]` ground truth), else `None`. Function
    nesting only (classes don't add to the path), mirroring `extract_types`' keys."""
    import ast
    from pathlib import Path
    out = {}

    def yields_of(fn):
        ys, stack = [], list(fn.body)
        while stack:
            n = stack.pop()
            if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)):
                continue
            if isinstance(n, ast.Yield) and n.value is not None:
                ys.append(n.value)
            elif isinstance(n, ast.YieldFrom):
                ys.append(None)  # `yield from` — unknown element
            stack.extend(ast.iter_child_nodes(n))
        return ys

    def shape(ys):
        # all yields tuples of the same arity → tuple[PyAny × n]; else no shape
        arities = {len(y.elts) for y in ys if isinstance(y, ast.Tuple)}
        if ys and all(isinstance(y, ast.Tuple) for y in ys) and len(arities) == 1:
            n = arities.pop()
            return {"node_type": "Subscript", "value": _name("tuple"),
                    "slice": {"node_type": "Tuple", "elts": [_name("PyAny")] * n}}
        return None

    for py in Path(untyped).rglob("*.py"):
        m = module_name(py.relative_to(untyped))
        if not m or m.startswith("."):
            continue
        try:
            tree = ast.parse(py.read_text(encoding="utf-8"))
        except SyntaxError:
            continue

        def walk(node, scope):
            for child in ast.iter_child_nodes(node):
                if isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef)):
                    fq = f"{scope}.{child.name}" if scope else child.name
                    ys = yields_of(child)
                    if ys:
                        out[f"{m}::{fq}::return"] = shape(ys)
                    walk(child, fq)
                else:
                    walk(child, scope)
        walk(tree, "")
    return out


def _name(t):
    return {"node_type": "Name", "id": t}


# Methods whose return type is fixed by the method name alone (same on str/bytes/list where they
# co-exist, and returning the same base), so a `return x.method(...)` types even when `x` does not.
_STR_METHODS = frozenset((
    "strip", "lstrip", "rstrip", "lower", "upper", "title", "capitalize", "casefold", "swapcase",
    "replace", "format", "format_map", "join", "center", "ljust", "rjust", "zfill", "expandtabs",
    "removeprefix", "removesuffix"))
_INT_METHODS = frozenset(("count", "index", "find", "rfind", "rindex", "bit_length", "bit_count"))
_BOOL_METHODS = frozenset((
    "startswith", "endswith", "isdigit", "isalpha", "isalnum", "isspace", "islower", "isupper",
    "istitle", "isnumeric", "isdecimal", "isidentifier", "isascii", "isprintable"))
_LIST_METHODS = frozenset(("split", "rsplit", "splitlines"))


def structural_returns(untyped) -> dict:
    """Recover return types that best-effort degraded away, by inferring the return EXPRESSION's type
    structurally from the source AST — e.g. a predicate `X == Y and Z` is `bool` no matter whether its
    operands translate. Only unambiguous, always-correct shapes (comparisons, boolean ops, literals,
    `str()`/`len()`/…), so this never introduces a wrong type; it fills spurious `None`s with the right
    one. Keyed like `extract_types` (function nesting; classes don't extend the path)."""
    import ast
    from pathlib import Path
    out = {}

    def is_bool(e):
        if isinstance(e, (ast.Compare,)):
            return True
        if isinstance(e, ast.UnaryOp) and isinstance(e.op, ast.Not):
            return True
        if isinstance(e, ast.BoolOp):
            return all(is_bool(v) for v in e.values)
        if isinstance(e, ast.Call) and isinstance(e.func, ast.Name):
            return e.func.id in ("bool", "isinstance", "issubclass", "hasattr", "callable", "all", "any")
        # `x.startswith(...)`, `x.isdigit()`, … — string predicates always return bool.
        if isinstance(e, ast.Call) and isinstance(e.func, ast.Attribute):
            return e.func.attr in _BOOL_METHODS
        if isinstance(e, ast.Constant) and isinstance(e.value, bool):
            return True
        return False

    def infer(e):
        if is_bool(e):
            return _name("bool")
        if isinstance(e, ast.Constant):
            v = e.value
            if isinstance(v, bool):    return _name("bool")
            if isinstance(v, int):     return _name("int")
            if isinstance(v, float):   return _name("float")
            if isinstance(v, str):     return _name("str")
            if isinstance(v, bytes):   return _name("bytes")
            return None
        if isinstance(e, ast.JoinedStr):
            return _name("str")
        if isinstance(e, (ast.List, ast.ListComp)):
            return _name("list")
        if isinstance(e, (ast.Dict, ast.DictComp)):
            return _name("dict")
        if isinstance(e, (ast.Set, ast.SetComp)):
            return _name("set")
        if isinstance(e, ast.Call) and isinstance(e.func, ast.Name):
            if e.func.id in ("str", "repr", "chr", "hex", "oct", "bin", "format"):
                return _name("str")
            if e.func.id in ("len", "ord", "id", "hash", "int"):
                return _name("int")
            if e.func.id in ("sorted", "list"):
                return _name("list")
            if e.func.id == "dict":
                return _name("dict")
            if e.func.id in ("set", "frozenset"):
                return _name("set")
            if e.func.id == "tuple":
                return _name("tuple")
            if e.func.id == "float":
                return _name("float")
            if e.func.id in ("bytes", "bytearray"):
                return _name(e.func.id)
        # Method-call returns whose type is fixed by the method name alone, independent of the (possibly
        # untyped) receiver — the return best-effort dropped, so recover it from the source method name.
        if isinstance(e, ast.Call) and isinstance(e.func, ast.Attribute):
            m = e.func.attr
            if m in _STR_METHODS:  return _name("str")
            if m in _INT_METHODS:  return _name("int")
            if m in _LIST_METHODS: return _name("list")
        return None

    for py in Path(untyped).rglob("*.py"):
        m = module_name(py.relative_to(untyped))
        if not m or m.startswith("."):
            continue
        try:
            tree = ast.parse(py.read_text(encoding="utf-8"))
        except SyntaxError:
            continue

        def returns_of(fn):
            # value-returning expressions, plus whether any path returns None (bare `return` / `return None`)
            rs, has_none = [], False
            stack = list(fn.body)
            while stack:
                n = stack.pop()
                if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)):
                    continue
                if isinstance(n, ast.Return):
                    if n.value is None or (isinstance(n.value, ast.Constant) and n.value.value is None):
                        has_none = True
                    else:
                        rs.append(n.value)
                else:
                    stack.extend(ast.iter_child_nodes(n))
            return rs, has_none

        def walk(node, scope):
            for child in ast.iter_child_nodes(node):
                if isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef)):
                    fq = f"{scope}.{child.name}" if scope else child.name
                    value_rs, has_none = returns_of(child)
                    tys = [infer(r) for r in value_rs]
                    # every value return must agree on one non-None type
                    ids = {t["id"] for t in tys if t}
                    if tys and all(tys) and len(ids) == 1:
                        # a mixed value/None return is `Optional[T]` (renders `Union[T, None]`, matching a
                        # `T | None` ground truth too); a pure value return is `T`.
                        out[f"{m}::{fq}::return"] = (
                            {"node_type": "Subscript", "value": _name("Optional"), "slice": tys[0]}
                            if has_none else tys[0])
                    walk(child, fq)
                else:
                    walk(child, scope)
        walk(tree, "")
    return out


def apply_structural_returns(pred: dict, struct: dict):
    """Fill spurious/missing returns with the structurally-inferred type (never override a real one)."""
    for k, t in struct.items():
        if k not in pred or _is_none_type(pred.get(k)):
            pred[k] = t


def _is_none_type(node) -> bool:
    return isinstance(node, dict) and (
        (node.get("node_type") == "Name" and node.get("id") == "None")
        or (node.get("node_type") == "Constant" and node.get("value") is None))


def degraded_return_keys(mods: dict) -> set:
    """Return-keys of functions whose body was best-effort-degraded (contains a `pyUnsupported`
    placeholder). Their `return` may have been stripped, so a `None` we infer for them is spurious —
    the caller drops it (→ missing) rather than committing a wrong `None`. Kept out of the TypeInfer
    engine: `pyUnsupported` is a PastaLean transpilation artifact, so this awareness lives here."""
    keys = set()

    def has_unsupported(stmts):
        def scan(n):
            if isinstance(n, dict):
                if n.get("node_type") in ("FunctionDef", "AsyncFunctionDef"):
                    return False
                if n.get("node_type") == "Name" and n.get("id") == "pyUnsupported":
                    return True
                return any(scan(v) for v in n.values())
            if isinstance(n, list):
                return any(scan(x) for x in n)
            return False
        return any(scan(s) for s in stmts)

    def walk(node, module, scope):
        if isinstance(node, dict):
            if node.get("node_type") in ("FunctionDef", "AsyncFunctionDef"):
                fq = f"{scope}.{node.get('name','')}" if scope else node.get("name", "")
                if has_unsupported(node.get("body", [])):
                    keys.add(f"{module}::{fq}::return")
                for s in node.get("body", []):
                    walk(s, module, fq)
                return
            for v in node.values():
                walk(v, module, scope)
        elif isinstance(node, list):
            for x in node:
                walk(x, module, scope)

    for m, ir in mods.items():
        walk(ir, m, "")
    return keys


def drop_spurious_none(pred: dict, degraded_keys: set):
    for k in degraded_keys:
        if _is_none_type(pred.get(k)):
            del pred[k]


def apply_generator_returns(pred: dict, gen_shapes: dict):
    """A generator's return is `Iterator[E]`. If lowering gave us `list[E]`, keep the real element
    `E` under `Iterator`; otherwise (degraded body) fall back to the source-derived yield SHAPE
    (`Iterator[tuple[PyAny, …]]`), or a bare `Iterator`."""
    for gk, shape in gen_shapes.items():
        cur = pred.get(gk)
        if isinstance(cur, dict) and cur.get("node_type") == "Subscript":
            pred[gk] = {**cur, "value": _name("Iterator")}
        elif shape is not None:
            pred[gk] = {"node_type": "Subscript", "value": _name("Iterator"), "slice": shape}
        else:
            pred[gk] = _name("Iterator")


def _is_unknown(node) -> bool:
    """A prediction that isn't a real static type — `PyAny` (our dynamic fallback) and bare `Any`.
    Committing these as predictions is wrong; they should count as MISSING, like an un-annotated slot."""
    return isinstance(node, dict) and node.get("node_type") == "Name" and node.get("id") in ("PyAny", "Any")


def extract_types(ir: dict, module: str, gt: bool) -> dict:
    """Walk a module IR into a {key: type-node} map. `gt`: read source `annotation`/`returns`;
    else read the inferred `_ty`/`_ret_ty`/`_bench_ty`."""
    out = {}

    def ann_of_arg(a):
        return a.get("annotation") if gt else a.get("_ty")

    def walk(node, scope):
        if isinstance(node, dict):
            nt = node.get("node_type")
            if nt in ("FunctionDef", "AsyncFunctionDef"):
                fq = f"{scope}.{node.get('name','')}" if scope else node.get("name", "")
                args = node.get("args", {})
                for a in args.get("args", []) + args.get("posonlyargs", []) + args.get("kwonlyargs", []):
                    t = ann_of_arg(a)
                    if t and a.get("arg") not in (None, "self", "cls") and not (not gt and _is_unknown(t)):
                        out[f"{module}::{fq}@{a['arg']}"] = t
                # Prefer `_ret_ty`; fall back to `_bench_ret_ty`, the benchmark-only stamp the engine
                # writes for a return `_ret_ty` deliberately omits — notably a `.none` (void) return,
                # which codegen keeps IO/Unit-shaped but which IS a real inferred `None` here.
                ret = node.get("returns") if gt else (node.get("_ret_ty") or node.get("_bench_ret_ty"))
                if ret and not (not gt and _is_unknown(ret)):
                    out[f"{module}::{fq}::return"] = ret
                for s in node.get("body", []):
                    walk(s, fq)
                return
            if nt == "AnnAssign" and gt:
                tgt = node.get("target", {})
                if isinstance(tgt, dict) and tgt.get("node_type") == "Name" and node.get("annotation"):
                    out[f"{module}::{scope}::{tgt['id']}"] = node["annotation"]
            if nt == "Assign" and not gt:
                tgt = node.get("target") or (node.get("targets") or [None])[0]
                if isinstance(tgt, dict) and tgt.get("node_type") == "Name":
                    t = tgt.get("_bench_ty") or tgt.get("_ty")
                    if t and not _is_unknown(t):
                        out[f"{module}::{scope}::{_strip_ssa(tgt.get('id',''))}"] = t
            for v in node.values():
                walk(v, scope)
        elif isinstance(node, list):
            for x in node:
                walk(x, scope)

    walk(ir, "")
    return out


# Threads each exe gets, sized in main() as cores/active-projects: with N projects scored in
# parallel, each spawns its own exe, so a fixed 64 would oversubscribe cores N-fold and thrash. Full
# core count when only one project is in flight.
EXE_THREADS = min(os.cpu_count() or 8, 64)


def _exe_call(task: dict, timeout: int = 180, threads: int | None = None) -> dict:
    """One request to the exe (server mode; EOF after the request makes it exit), timeout-guarded."""
    proc = subprocess.Popen([EXE, "--server"], stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                            text=True, env={**os.environ, "LEAN_NUM_THREADS": str(threads or EXE_THREADS)})
    try:
        out, _ = proc.communicate(json.dumps(task) + "\n", timeout=timeout)
        return json.loads(out.splitlines()[0]) if out.strip() else {}
    except (subprocess.TimeoutExpired, Exception):  # noqa: BLE001
        proc.kill(); proc.wait()
        return {}


# When one repo is in flight (across-repo Pool of size 1) we have the whole machine, so a big repo's
# chunks run as parallel exe processes — a single inferRepo call caps at ~7-8 cores (Lean's task
# scheduler contends on one heap), several processes scale past that. Off when repos run in parallel
# (each worker already owns a core slice; within-repo fan-out would oversubscribe). Chunk boundaries
# are unchanged, so results are identical either way.
WITHIN_REPO_PARALLEL = False


def infer_repo(mods: dict, chunk: int = 120) -> dict:
    """Infer in chunks so one module that crashes/overflows the exe only loses its chunk, not the
    whole repo. Per-module inference is chunk-independent, so this changes nothing but robustness."""
    items = list(mods.items())
    subs = [dict(items[i:i + chunk]) for i in range(0, len(items), chunk)]
    out = {}
    if WITHIN_REPO_PARALLEL and len(subs) > 1:
        threads = max(2, EXE_THREADS // len(subs))
        with ThreadPoolExecutor(max_workers=len(subs)) as ex:
            for r in ex.map(lambda s: _exe_call({"task": "inferRepo", "modules": s}, threads=threads), subs):
                out.update(r.get("modules", {}))
    else:
        for sub in subs:
            out.update(_exe_call({"task": "inferRepo", "modules": sub}).get("modules", {}))
    return out


def score_maps(gt: dict, pred: dict) -> dict:
    return _exe_call({"task": "scoreRepo", "gt": gt, "pred": pred})


TOOL = "pastalean"  # set by main(); "pyrefly" runs `pyrefly infer` and reads its annotations


def pred_pyrefly(untyped: Path) -> dict:
    """Prediction from `pyrefly infer`: annotate a copy of the untyped repo, then read the annotations
    back the same way ground truth is read (they are both just annotated source)."""
    import tempfile, shutil
    tmp = Path(tempfile.mkdtemp())
    dst = tmp / "repo"
    shutil.copytree(untyped, dst)
    pyrefly = str(Path(sys.executable).parent / "pyrefly")
    try:
        subprocess.run([pyrefly, "infer", str(dst)], capture_output=True, timeout=900)
    except subprocess.TimeoutExpired:
        pass
    pred = {}
    for py in dst.rglob("*.py"):
        m = module_name(py.relative_to(dst))
        if not m or m.startswith("."):
            continue
        ir = raw_ir(py)
        if ir:
            pred.update(extract_types(ir, m, gt=True))
    shutil.rmtree(tmp, ignore_errors=True)
    return pred


def pred_pyre(untyped: Path) -> dict:
    """Prediction from Facebook's `pyre infer`: annotate a copy of the untyped repo in place (needs a
    minimal `.pyre_configuration`), then read the annotations back the same way ground truth is read."""
    import tempfile, shutil
    tmp = Path(tempfile.mkdtemp())
    dst = tmp / "repo"
    shutil.copytree(untyped, dst)
    root = dst
    for sub in ("src", "lib"):
        if (root / sub).is_dir():
            root = root / sub
    (root / ".pyre_configuration").write_text('{"source_directories": ["."], "search_path": []}')
    pyre = str(Path(sys.executable).parent / "pyre")
    try:
        subprocess.run([pyre, "infer", "-i", "--annotate-attributes", "."], cwd=str(root),
                       capture_output=True, timeout=900)
    except subprocess.TimeoutExpired:
        pass
    pred = {}
    for py in dst.rglob("*.py"):
        m = module_name(py.relative_to(dst))
        if not m or m.startswith("."):
            continue
        ir = raw_ir(py)
        if ir:
            pred.update(extract_types(ir, m, gt=True))
    shutil.rmtree(tmp, ignore_errors=True)
    return pred


def pred_pytype(untyped: Path) -> dict:
    """Prediction from Google's `pytype`: run `pytype-single` per file (whole-repo mode collides on
    duplicate module names in real projects), `merge-pyi` the inferred stub back into the source copy,
    then read the annotations back the same way ground truth is read. Per-file with a pythonpath at the
    repo root so sibling imports resolve as far as pytype can without a prebuilt import graph."""
    import tempfile, shutil
    from concurrent.futures import ThreadPoolExecutor
    tmp = Path(tempfile.mkdtemp())
    dst = tmp / "repo"
    shutil.copytree(untyped, dst)
    root = dst
    for sub in ("src", "lib"):
        if (root / sub).is_dir():
            root = root / sub
    pt = str(Path(sys.executable).parent / "pytype-single")
    if not Path(pt).exists():
        import shutil as _sh
        pt = _sh.which("pytype-single") or "pytype-single"
    env = {**os.environ, "PYTHONPATH": str(root)}

    def annotate(py: Path):
        stub = py.with_suffix(".pyi.pt")
        try:
            r = subprocess.run([pt, str(py), "-o", str(stub), "-V", "3.10", "-P", str(root)],
                               capture_output=True, timeout=120, env=env)
            if stub.exists():
                subprocess.run(["merge-pyi", "-i", str(py), str(stub)], capture_output=True, timeout=60)
        except subprocess.TimeoutExpired:
            pass
        finally:
            if stub.exists():
                stub.unlink()

    files = list(dst.rglob("*.py"))
    with ThreadPoolExecutor(max_workers=min(EXE_THREADS, 32)) as ex:
        list(ex.map(annotate, files))
    pred = {}
    for py in files:
        m = module_name(py.relative_to(dst))
        if not m or m.startswith("."):
            continue
        ir = raw_ir(py)
        if ir:
            pred.update(extract_types(ir, m, gt=True))
    shutil.rmtree(tmp, ignore_errors=True)
    return pred


def pred_hityper(untyped: Path) -> dict:
    """Prediction from HiTyper (static, hybrid) type inference. HiTyper writes a per-file
    `*_INFERREDTYPES.json` (function→{arg,local,return}→type STRING) rather than annotating source, so
    we parse those JSONs and convert each type string to an IR type-node via `_type_node`, keyed like
    `extract_types` (module::func@arg / ::return / module::scope::var)."""
    import tempfile, shutil, re as _re
    tmp = Path(tempfile.mkdtemp())
    dst = tmp / "repo"
    shutil.copytree(untyped, dst)
    out = tmp / "hityper_out"
    out.mkdir()
    import shutil as _sh
    hityper = os.environ.get("HITYPER_BIN") or _sh.which("hityper") or "hityper"
    try:
        subprocess.run([hityper, "infer", "-p", str(dst), "-d", str(out), "-n", "1"],
                       capture_output=True, timeout=3600)
    except subprocess.TimeoutExpired:
        pass
    pred = {}
    for jf in out.rglob("*_INFERREDTYPES.json"):
        try:
            data = json.loads(jf.read_text(encoding="utf-8"))
        except Exception:  # noqa: BLE001
            continue
        # HiTyper keys files by absolute path; recover module from the path under dst.
        for fpath, funcs in data.items():
            try:
                m = module_name(Path(fpath).resolve().relative_to(dst.resolve()))
            except ValueError:
                m = module_name(Path(fpath).name and Path(fpath))
            if not m or m.startswith("."):
                continue
            _hityper_file(pred, m, funcs)
    shutil.rmtree(tmp, ignore_errors=True)
    return pred


def _hityper_file(pred: dict, module: str, funcs) -> None:
    """Fold one HiTyper file entry ({func-scope-key: [ {category, name, type}, ... ]}) into `pred`.
    Scope keys look like `funcname@lineno` or `global@global`; we take the function name before `@`."""
    if not isinstance(funcs, dict):
        return
    for scope_key, slots in funcs.items():
        fn = scope_key.split("@")[0]
        is_global = fn in ("global", "")
        if not isinstance(slots, list):
            continue
        for s in slots:
            if not isinstance(s, dict):
                continue
            cat, name, tystr = s.get("category"), s.get("name"), s.get("type")
            node = _type_node(tystr[0] if isinstance(tystr, list) and tystr else tystr)
            if node is None or _is_unknown(node):
                continue
            if cat == "arg" and not is_global and name not in (None, "self", "cls"):
                pred[f"{module}::{fn}@{name}"] = node
            elif cat == "return" and not is_global:
                pred[f"{module}::{fn}::return"] = node
            elif cat == "local" and name:
                scope = "" if is_global else fn
                pred[f"{module}::{scope}::{name}"] = node


_TYPE_NODE_CACHE: dict = {}


def _type_node(tystr):
    """Convert a type STRING (e.g. `List[int]`, `str`, `Optional[Foo]`) to the same IR type-node the
    scorer compares, by annotating a throwaway var and reading its `annotation` back through raw_ir.
    Cached; returns None for empty/None/unparseable strings."""
    if not tystr or not isinstance(tystr, str):
        return None
    s = tystr.strip()
    if s in ("", "None", "Any", "typing.Any", "nan"):
        return None
    if s in _TYPE_NODE_CACHE:
        return _TYPE_NODE_CACHE[s]
    node = None
    try:
        import ast as _ast
        _ast.parse(f"def _f() -> {s}: ...")  # reject anything that isn't a valid annotation
        ir = raw_ir_text(f"def _f() -> {s}:\n    pass\n")
        if ir:
            got = extract_types(ir, "_m", gt=True)
            node = got.get("_m::_f::return")
    except Exception:  # noqa: BLE001
        node = None
    _TYPE_NODE_CACHE[s] = node
    return node


def raw_ir_text(text: str):
    try:
        return json.loads(driver.translate_to_json(text, "<syn>", best_effort=True,
                                                    infer_only=True, resolve_imports=False))
    except Exception:  # noqa: BLE001
        return None


def score_repo(repo: Path) -> dict:
    orig, untyped = repo / "original_repo", repo / "repo_without_types"
    for sub in ("src", "lib"):  # get_repo_similarity descends into src/lib — do it for BOTH so the
        if (orig / sub).is_dir():   # module-name keys (and hence gt/pred keys) line up.
            orig = orig / sub
        if (untyped / sub).is_dir():
            untyped = untyped / sub
    # ground truth
    gt = {}
    for py in orig.rglob("*.py"):
        m = module_name(py.relative_to(orig))
        if not m or m.startswith("."):
            continue
        ir = raw_ir(py)
        if ir:
            gt.update(extract_types(ir, m, gt=True))
    if not gt:
        return {"repo": repo.name, "total": 0}
    # prediction (timed: this is the only tool-dependent work; GT-gen and scoring are identical
    # across tools, so the fair per-tool time is the sum of these prediction spans over all repos).
    import time as _time
    _t0 = _time.perf_counter()
    if TOOL == "pyrefly":
        pred = pred_pyrefly(untyped)
    elif TOOL == "pyre":
        pred = pred_pyre(untyped)
    elif TOOL == "pytype":
        pred = pred_pytype(untyped)
    elif TOOL == "hityper":
        pred = pred_hityper(untyped)
    else:
        mods = {}
        for py in untyped.rglob("*.py"):
            m = module_name(py.relative_to(untyped))
            if not m or m.startswith("."):
                continue
            ir = raw_ir(py)
            if ir:
                mods[m] = ir
        gen_keys = generator_return_keys(untyped)
        stamped = infer_repo(mods)
        pred = {}
        for m, st in stamped.items():
            pred.update(extract_types(st, m, gt=False))
        apply_generator_returns(pred, gen_keys)
        # Recover returns best-effort degraded away, by structurally inferring the return expression
        # (a predicate `X == Y and Z` is `bool`, etc.) — the RIGHT fix for spurious `None`s: infer the
        # correct type rather than drop the prediction.
        apply_structural_returns(pred, structural_returns(untyped))
    pred_time = _time.perf_counter() - _t0
    res = score_maps(gt, pred)
    total = res.get("total", 0)
    sim = float(res.get("sum_sim", "0"))
    return {"repo": repo.name, "total": total, "exact": res.get("exact", 0),
            "missing": res.get("missing", 0), "pred_time": pred_time,
            "typesim": round(sim / total, 4) if total else 0.0,
            "exact_score": round(res.get("exact", 0) / total, 4) if total else 0.0,
            "coverage": round((total - res.get("missing", 0)) / total, 4) if total else 0.0}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("dataset", type=Path)
    # How many PROJECTS to score at once (NOT threads: each project internally uses all cores it can).
    # Default 1 = one project at a time, each with the whole machine (full throttle), which is the
    # linear-sum timing the paper reports. `--workers` kept as a backward-compatible alias.
    ap.add_argument("--parallel-repos", "--workers", dest="parallel_repos", type=int, default=1,
                    metavar="N", help="Number of projects to score concurrently (default 1: one at a "
                                      "time, each project using the whole machine). NOT a thread count.")
    ap.add_argument("--repo", default=None)
    ap.add_argument("--tool", choices=("pastalean", "pyrefly", "pyre", "pytype", "hityper"),
                    default="pastalean")
    args = ap.parse_args()
    global TOOL, EXE_THREADS, WITHIN_REPO_PARALLEL
    TOOL = args.tool
    repos = [p for p in args.dataset.iterdir()
             if (p / "repo_without_types").is_dir() and (args.repo is None or p.name == args.repo)]
    # Largest repo first (by untyped source bytes) so the longest pole starts in the first wave and
    # never tails the run; and size each exe's thread pool to cores/active-projects to avoid N-fold
    # thread oversubscription when N projects infer concurrently.
    def _bytes(p: Path) -> int:
        return sum(f.stat().st_size for f in (p / "repo_without_types").rglob("*.py"))
    repos.sort(key=_bytes, reverse=True)
    n_active = min(args.parallel_repos, len(repos)) or 1
    EXE_THREADS = max(1, (os.cpu_count() or 8) // n_active)
    # One project at a time (linear-sum timing): give each project the whole machine by fanning its
    # chunks across parallel exe processes. With projects already parallel, leave it off.
    WITHIN_REPO_PARALLEL = (n_active == 1)
    results = ([score_repo(repos[0])] if len(repos) == 1
               else Pool(args.parallel_repos).map(score_repo, repos, chunksize=1))
    results = [r for r in results if r.get("total")]
    print(f"\n{'repo':<22}{'vars':>7}{'TypeSim':>9}{'Exact':>8}{'Cover':>8}{'Time(s)':>9}")
    for r in sorted(results, key=lambda r: -r["total"]):
        print(f"{r['repo']:<22}{r['total']:>7}{r['typesim']:>9.3f}{r['exact_score']:>8.3f}"
              f"{r['coverage']:>8.3f}{r.get('pred_time', 0.0):>9.2f}")
    time_sum = sum(r.get("pred_time", 0.0) for r in results)
    print(f"\nTOTAL prediction time (sum over {len(results)} projects, each full throttle): "
          f"{time_sum:.1f} s")
    tot = sum(r["total"] for r in results)
    if tot:
        wsim = sum(r["typesim"] * r["total"] for r in results) / tot
        wex = sum(r["exact_score"] * r["total"] for r in results) / tot
        wcov = sum(r["coverage"] * r["total"] for r in results) / tot
        print(f"\n{'WEIGHTED (' + str(len(results)) + ' repos)':<22}{tot:>7}{wsim:>9.3f}{wex:>8.3f}{wcov:>8.3f}")


if __name__ == "__main__":
    main()

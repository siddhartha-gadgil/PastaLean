#!/usr/bin/env python3
"""`CPastaEval` — fetch, convert, evaluate, and plot competitive-programming datasets.

One object owns a dataset directory and drives the whole pipeline:

    from cpasta_eval import CPastaEval

    with CPastaEval("cp_harness/dataset_leetcode", source="leetcode") as ev:
        ev.fetch(num="max")          # once; downloading is the slow network step
        ev.convert()                 # Python -> Lean -> compile-check
        ev.evaluate()                # run Lean and CPython on the test cases
        ev.plot()                    # coverage-by-difficulty chart

Two TEST MODELS, recorded per problem in a `kind` file, so several sources coexist in one dataset:

    "stdio"     the solution reads stdin and prints stdout; tests are `test_<i>.in/.out`
                (CodeContests). Wrapped in a `__main__` guard, then compared per test.
    "function"  the solution is a callable; tests are `tests/tests.json`
                (LeetCode). The converted `fn'rn` is called and its return value compared.

Adding a source means writing one `_save_*` method and registering it in `SOURCES`; convert and
evaluate need no changes because they dispatch on `kind`.

CLI:
    python3 cp_harness/cpasta_eval.py run --source leetcode --num max
    python3 cp_harness/cpasta_eval.py run --skip-fetch --random 29
    python3 cp_harness/cpasta_eval.py convert --dataset cp_harness/dataset_leetcode
"""
from __future__ import annotations

import argparse
import ast
import concurrent.futures
import json
import multiprocessing as mp
import os
import queue
import random
import re
import subprocess
import shutil
import sys
import threading
import warnings
import time
from pathlib import Path

from pastalean import Session  # `uv pip install -e .`

REPO_ROOT = Path(__file__).resolve().parent.parent

KIND_FILE = "kind"
KIND_FUNCTION = "function"
KIND_STDIO = "stdio"

PYTHON3_LANG_ID = 3          # CodeContests language id for Python 3
ALLOWED_IMPORTS = {"math"}   # CodeContests pre-filter: keep math-only solutions

# `lean --run` prints diagnostics like `…/sol_0.lean:8:6: warning: …` to *stdout*, ahead of the
# program's own output, so they must be stripped before comparing.
_LEAN_DIAG_HEADER = re.compile(r"\.lean:\d+:\d+:\s+(warning|error|info|note)\b")
_PASSED_RE = re.compile(r"PASSED\s+(\d+)/(\d+)")
_FAIL_RE = re.compile(r"^FAIL (\d+): got (.*)$", re.MULTILINE)

CATS = ["didn't compile", "compiled · not all passed", "compiled · all passed"]
COLORS = ["#d9534f", "#f0ad4e", "#5cb85c"]
DIFF_ORDER = ["Easy", "Medium", "Hard"]

# The LeetCode dataset's `prompt` star-imports these; a solution execs standalone only with them.
_PRELUDE = (
    "from typing import *\nfrom math import *\nfrom collections import *\n"
    "from functools import *\nfrom itertools import *\nfrom heapq import *\n"
    "from bisect import *\nimport re\ninf = float('inf')\n"
)


# --------------------------------------------------------------------------------------
# Parsing / normalization helpers
# --------------------------------------------------------------------------------------

def parse_count(s):
    """`--num` value → an int limit, or None for no limit. `max`/`all`/`-1`/`inf` mean unlimited."""
    t = str(s).strip().lower()
    return None if t in ("max", "all", "-1", "inf", "") else int(t)


def parse_max_tests(s):
    """`--max-tests` value → int cap, or 0 (all) for `max`/`all`/`-1`/``."""
    t = str(s).strip().lower()
    return 0 if t in ("max", "all", "-1", "") else int(t)


def sanitize_problem_name(name):
    """The on-disk directory name for a problem."""
    return name.replace("/", "_").replace(" ", "_")


def strip_lean_diagnostics(text):
    """Drop the Lean compile diagnostics `lean --run` writes to stdout, leaving program output."""
    kept = []
    for line in text.splitlines():
        if _LEAN_DIAG_HEADER.search(line) or line.strip().startswith(("Note:", "Hint:")):
            continue
        kept.append(line)
    return "\n".join(kept)


def normalize(text):
    """CP-standard output normalization: strip trailing whitespace per line and overall."""
    return "\n".join(line.rstrip() for line in text.strip().splitlines()).strip()


# A convert failure that traces to a Python library PastaLean does not model (concurrency, regex,
# datetime, interactive judge APIs) is not a codegen shortcoming — it is out of scope. Detected from
# the source so it is reported as `skipped: <reason>` instead of polluting the `convert_fail` bucket.
# Patterns match USAGE (a call / method), never a bare import — the LeetCode preamble imports many
# modules (`import datetime`, `import re`) that a given solution never uses.
_OUT_OF_SCOPE = [
    (re.compile(r"\bThread\s*\(|\.acquire\s*\(\s*\)|\.release\s*\(\s*\)|threading\."),
     "threading / concurrency"),
    (re.compile(r"\bre\.(sub|match|search|findall|finditer|compile|split|fullmatch)\s*\("),
     "re (regular expressions)"),
    (re.compile(r"datetime\.date\s*\(|datetime\.datetime\s*\(|\.strftime\s*\(|\.weekday\s*\(|\.isoweekday\s*\("),
     "datetime"),
    (re.compile(r"\b(PriorityQueue|LifoQueue)\s*\(|Queue\s*\(\s*\)\.(put|get)\b"),
     "queue (Queue / PriorityQueue)"),
    # Interactive LeetCode judge objects expose opaque methods on a handler param (no source to model).
    (re.compile(r"\.haveSameCategory\s*\(|\.guess\s*\(|\.knows\s*\(|\.compareSub\s*\(|\.query\s*\("),
     "interactive judge API"),
]


def out_of_scope_reason(source):
    """If `source` uses a library/feature PastaLean deliberately does not model, the reason string;
    else None. Used to reclassify a convert failure as `skipped` rather than `convert_fail`. Matches
    against non-import lines only, so an unused preamble `import` never trips it."""
    body = "\n".join(ln for ln in source.splitlines()
                     if not re.match(r"\s*(import |from \S+ import )", ln))
    for rx, reason in _OUT_OF_SCOPE:
        if rx.search(body):
            return reason
    return None


def summarize_error(status, log_text):
    """A reason string from a failing stage's output. Keeps the FULL first Lean diagnostic — the
    error message AND its continuation lines (the offending type / instance / expression), which is
    what actually distinguishes one failure cluster from another (`PyGetItem (Option TreeNode × ℤ) ℤ`
    vs `PyGetItem (List ℤ) Bool`). One truncated headline line collapses unrelated bugs together."""
    lines = [ln.rstrip() for ln in (log_text or "").splitlines() if ln.strip()]
    if not lines:
        return "(no error output)"
    if status == "convert_fail":
        for ln in reversed(lines):
            if "Error generating code:" in ln:
                # Keep the innermost (most specific) codegen message, not the outer wrapper chain.
                return ln.rsplit("Error generating code:", 1)[-1].split(": ", 1)[-1].strip() \
                    if ": " in ln.rsplit("Error generating code:", 1)[-1] \
                    else ln.rsplit("Error generating code:", 1)[-1].strip()
        return lines[-1].strip()
    # compile_fail: the first Lean diagnostic (`file:line:col: error(kind): msg`) plus the indented
    # detail lines that follow it, up to the next diagnostic / `Hint:` / blank. Joined with " | ".
    DIAG = re.compile(r"^.*?:\d+:\d+:\s*(?:error|warning)")
    for i, ln in enumerate(lines):
        low = ln.lower()
        if "error" in low and DIAG.match(ln):
            head = ln[low.find("error"):]
            for sep in ("): ", "error: "):
                if sep in head:
                    head = head.split(sep, 1)[1].strip()
                    break
            detail = []
            for cont in lines[i + 1:]:
                if DIAG.match(cont) or cont.lstrip().startswith("Hint:"):
                    break
                detail.append(cont.strip())
                if len(detail) >= 4:
                    break
            return " | ".join([head, *detail]).strip()
    return lines[0].strip()


# --------------------------------------------------------------------------------------
# stdio model: wrap bare top-level code in a `__main__` guard so py2lean emits `def main`
# --------------------------------------------------------------------------------------

def has_main_entry(source):
    """True if the source already defines `main` or uses a `__main__` guard."""
    try:
        tree = ast.parse(source)
    except SyntaxError:
        return False
    for node in ast.walk(tree):
        if isinstance(node, ast.FunctionDef) and node.name == "main":
            return True
        if isinstance(node, ast.If):
            test = node.test
            if isinstance(test, ast.Compare) and isinstance(test.left, ast.Name) \
                    and test.left.id == "__name__":
                return True
    return False


def wrap_for_main(source):
    """Wrap bare top-level code under `if __name__ == "__main__":`, keeping imports at module
    scope (Lean and Python both need them there). No-op when a `main` entry already exists."""
    if has_main_entry(source):
        return source
    try:
        tree = ast.parse(source)
    except SyntaxError:
        return source
    import_lines = set()
    for node in tree.body:
        if isinstance(node, (ast.Import, ast.ImportFrom)):
            import_lines.update(range(node.lineno, (node.end_lineno or node.lineno) + 1))
    imports, body = [], []
    for i, line in enumerate(source.splitlines(), start=1):
        (imports if i in import_lines else body).append(line)
    indented = "\n".join(("    " + ln) if ln.strip() else ln for ln in body)
    parts = ([("\n".join(imports))] if any(l.strip() for l in imports) else []) \
        + ['if __name__ == "__main__":', indented]
    return "\n".join(parts) + "\n"


def imported_modules(source):
    """Top-level module names a source imports, or None if it does not parse."""
    try:
        tree = ast.parse(source)
    except SyntaxError:
        return None
    modules = set()
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            modules.update(a.name.split(".")[0] for a in node.names)
        elif isinstance(node, ast.ImportFrom) and node.module:
            modules.add(node.module.split(".")[0])
    return modules


# --------------------------------------------------------------------------------------
# function model (LeetCode): extract the entry method, render test cases, build a Lean harness
# --------------------------------------------------------------------------------------

def entry_method_name(entry_point):
    """`Solution().twoSum` (or `twoSum`) → `twoSum`."""
    return entry_point.strip().rstrip("()").split(".")[-1].strip()


def extract_function(completion_src, method_name):
    """The entry method as a standalone top-level `def` with `self` dropped, or None. Methods that
    touch `self.<x>` depend on siblings and are not isolatable."""
    try:
        tree = ast.parse(completion_src)
    except SyntaxError:
        return None
    target = next((n for n in ast.walk(tree)
                   if isinstance(n, ast.FunctionDef) and n.name == method_name), None)
    if target is None:
        return None
    for sub in ast.walk(target):
        if isinstance(sub, ast.Attribute) and isinstance(sub.value, ast.Name) \
                and sub.value.id == "self":
            return None
    target.args.args = [a for a in target.args.args if a.arg != "self"]
    target.decorator_list = []
    # The class is flattened to top-level defs, so a `Solution().m(...)` self-call (a common
    # LeetCode recursion idiom) becomes a plain `m(...)` call.
    class _DropSolutionSelf(ast.NodeTransformer):
        def visit_Call(self, node):  # noqa: N802
            self.generic_visit(node)
            f = node.func
            if isinstance(f, ast.Attribute) and isinstance(f.value, ast.Call) \
                    and isinstance(f.value.func, ast.Name) and f.value.func.id == "Solution":
                node.func = ast.Name(id=f.attr, ctx=ast.Load())
            return node
    target = ast.fix_missing_locations(_DropSolutionSelf().visit(target))
    try:
        return ast.unparse(target)
    except Exception:  # noqa: BLE001
        return None


def _bound_names(tree):
    """Names bound anywhere in `tree`: assign targets, params, def/class names, imports, excepts."""
    bound = set()
    for n in ast.walk(tree):
        if isinstance(n, ast.Name) and isinstance(n.ctx, ast.Store):
            bound.add(n.id)
        elif isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            bound.add(n.name)
        elif isinstance(n, ast.arg):
            bound.add(n.arg)
        elif isinstance(n, ast.alias):
            bound.add((n.asname or n.name).split(".")[0])
        elif isinstance(n, ast.ExceptHandler) and n.name:
            bound.add(n.name)
    return bound


def _free_names(src_or_node):
    """Names read without being bound first."""
    tree = ast.parse(src_or_node) if isinstance(src_or_node, str) else src_or_node
    bound = _bound_names(tree)
    return {n.id for n in ast.walk(tree)
            if isinstance(n, ast.Name) and isinstance(n.ctx, ast.Load) and n.id not in bound}


def _toplevel_binder_names(stmt):
    """The top-level names a prompt statement binds (`def f`, `class C`, `inf = ...`)."""
    if isinstance(stmt, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
        return {stmt.name}
    if isinstance(stmt, ast.Assign):
        return {t.id for t in stmt.targets if isinstance(t, ast.Name)}
    if isinstance(stmt, ast.AnnAssign) and isinstance(stmt.target, ast.Name):
        return {stmt.target.id}
    return set()


def _reachable_statements(stmts, seed_names):
    """The top-level statements of `stmts` that `seed_names` reaches transitively, in source order."""
    binders, order = {}, []
    for stmt in stmts:
        names = _toplevel_binder_names(stmt)
        if names:
            order.append(stmt)
            for nm in names:
                binders[nm] = stmt
    needed, worklist = set(), list(seed_names)
    while worklist:
        stmt = binders.get(worklist.pop())
        if stmt is None or id(stmt) in needed:
            continue
        needed.add(id(stmt))
        worklist.extend(_free_names(stmt))
    return [s for s in order if id(s) in needed]


def prompt_preamble(prompt_src, fn_src):
    """The dataset's `prompt`, verbatim, keeping every import plus only the top-level definitions
    `fn_src` reaches transitively.

    Keeps `inf = float('inf')` when the solution reads `inf`; drops the unreached `ListNode` /
    `tree_node` test scaffolding.
    """
    try:
        prompt_tree = ast.parse(prompt_src)
    except SyntaxError:
        return ""
    imports = [s for s in prompt_tree.body if isinstance(s, (ast.Import, ast.ImportFrom))]
    kept = imports + _reachable_statements(prompt_tree.body, _free_names(fn_src))
    return "\n".join(ast.unparse(s) for s in kept)


def completion_helpers(completion_src, fn_src):
    """The completion's own top-level helpers that the entry method needs.

    A solution may define a sibling class or function beside `class Solution` (a
    `BinaryIndexedTree`, a `SegmentTree`). Extracting only the entry method drops those and the
    file no longer runs at all, so keep the ones it reaches.
    """
    try:
        tree = ast.parse(completion_src)
    except SyntaxError:
        return ""
    kept = _reachable_statements(tree.body, _free_names(fn_src))
    return "\n\n".join(ast.unparse(s) for s in kept)


def self_contained_source(prompt_src, completion_src, fn_src):
    """The dataset's preamble + the completion's reachable helpers + the extracted function, each
    pruned to what the solution actually uses."""
    helpers = completion_helpers(completion_src, fn_src)
    body = (helpers + "\n\n" + fn_src) if helpers else fn_src
    pre = prompt_preamble(prompt_src, body)
    return (pre + "\n\n" + body) if pre else body


def param_names(fn_src):
    """Positional parameter names of the first top-level `def`, in order."""
    tree = ast.parse(fn_src)
    fn = next(n for n in tree.body if isinstance(n, ast.FunctionDef))
    return [a.arg for a in fn.args.args]


#: A generous preamble for LiveCodeBench `execution` snippets, whose ground-truth `code` uses
#: `List`/`Optional`/`Counter`/`inf` etc. freely without importing them (the benchmark runs them in a
#: namespace that already has these bound). Mirrors the LeetCode prompt preamble.
LCB_PREAMBLE = (
    "from typing import *\n"
    "from collections import *\n"
    "from math import *\n"
    "from functools import *\n"
    "from itertools import *\n"
    "import heapq\n"
    "from heapq import *\n"
    "import bisect\n"
    "from bisect import *\n"
    "inf = float('inf')\n"
)


def _gen_random_like(v, rng, depth=0):
    """A fresh random value with the SAME shape as `v` (its type, and for containers the element
    shape of its first element). Used to synthesize extra test inputs for a problem that ships only
    one, so we can differential-test the Lean twin against the reference Python on many inputs."""
    import string
    if depth > 4:
        return v
    if isinstance(v, bool):
        return rng.choice([True, False])
    if isinstance(v, int):
        hi = max(10, abs(v) * 2 + 5)
        return rng.randint(-hi, hi)
    if isinstance(v, float):
        return round(rng.uniform(-abs(v) * 2 - 10, abs(v) * 2 + 10), 4)
    if isinstance(v, str):
        chars = sorted(set(v)) or list(string.ascii_lowercase)
        return "".join(rng.choice(chars) for _ in range(rng.randint(0, max(1, len(v) + 2))))
    if isinstance(v, list):
        elem = v[0] if v else 0
        n = rng.randint(0, max(1, len(v) + 3))
        return [_gen_random_like(elem, rng, depth + 1) for _ in range(n)]
    if isinstance(v, tuple):
        return tuple(_gen_random_like(x, rng, depth + 1) for x in v)
    if isinstance(v, dict):
        items = list(v.items())
        if not items:
            return {}
        k0, val0 = items[0]
        n = rng.randint(1, max(1, len(items) + 2))
        return {_gen_random_like(k0, rng, depth + 1): _gen_random_like(val0, rng, depth + 1)
                for _ in range(n)}
    return v


#: Worker that generates differential tests IN A CHILD PROCESS with a hard memory cap, so a reference
#: that blows up on an out-of-domain random input (e.g. `2**bignum`) is killed with MemoryError instead
#: of OOM-killing the whole fetch. Prints JSON `[[input_str, output_repr], ...]` on stdout.
_LCB_WORKER = r'''
import sys, json, random, copy, signal, ast, resource
data = json.load(open(sys.argv[1]))
mem = data["mem_mb"] * 1024 * 1024
try:
    resource.setrlimit(resource.RLIMIT_AS, (mem, mem))
except Exception:
    pass

def gen(v, rng, depth=0):
    import string
    if depth > 4: return v
    if isinstance(v, bool): return rng.choice([True, False])
    if isinstance(v, int):
        hi = min(200, max(10, abs(v) * 2 + 5))
        return rng.randint(-hi, hi)
    if isinstance(v, float): return round(rng.uniform(-abs(v) * 2 - 10, abs(v) * 2 + 10), 4)
    if isinstance(v, str):
        chars = sorted(set(v)) or list(string.ascii_lowercase)
        return "".join(rng.choice(chars) for _ in range(rng.randint(0, min(60, max(1, len(v) + 2)))))
    if isinstance(v, list):
        elem = v[0] if v else 0
        n = rng.randint(0, min(60, max(1, len(v) + 3)))
        return [gen(elem, rng, depth + 1) for _ in range(n)]
    if isinstance(v, tuple): return tuple(gen(x, rng, depth + 1) for x in v)
    if isinstance(v, dict):
        items = list(v.items())
        if not items: return {}
        k0, val0 = items[0]
        n = rng.randint(1, min(30, max(1, len(items) + 2)))
        return {gen(k0, rng, depth + 1): gen(val0, rng, depth + 1) for _ in range(n)}
    return v

class _TO(Exception): pass
signal.signal(signal.SIGALRM, lambda *_: (_ for _ in ()).throw(_TO()))
out, seen = [], set()
try:
    ns = {}
    exec(data["code"], ns)
    fn = ns[data["method"]]
    params = data["params"]; rng = random.Random(0)
    for _ in range(data["k"] * 3):
        if len(out) >= data["k"]: break
        args = [gen(a, rng) for a in data["base_args"]]
        key = repr(args)
        if len(key) > 3000 or key in seen: continue
        seen.add(key)
        signal.setitimer(signal.ITIMER_REAL, 1.0)
        try:
            res = fn(*copy.deepcopy(args))
        except BaseException:
            continue
        finally:
            signal.setitimer(signal.ITIMER_REAL, 0)
        try:
            r = repr(res)
            if len(r) > 3000: continue
            ast.literal_eval(r); ast.literal_eval(key)
            inp = ", ".join("%s = %r" % (params[i], args[i]) for i in range(len(params)))
        except Exception:
            continue
        out.append([inp, r])
except BaseException:
    pass
print(json.dumps(out))
'''


def expand_lcb_tests(code_src, method, params, base_args, k=24, mem_mb=768, timeout=25):
    """Return `[(input_str, output_repr), ...]` — extra differential tests generated by running the
    ground-truth `code` on random inputs shaped like `base_args`, in a memory-capped subprocess so a
    runaway reference can't take down the fetch. On any failure returns []."""
    import subprocess, tempfile, json as _json
    try:
        with tempfile.NamedTemporaryFile("w", suffix=".json", delete=False) as fh:
            _json.dump({"code": code_src, "method": method, "params": params,
                        "base_args": base_args, "k": k, "mem_mb": mem_mb}, fh)
            path = fh.name
        proc = subprocess.run([sys.executable, "-c", _LCB_WORKER, path],
                              capture_output=True, text=True, timeout=timeout)
        os.unlink(path)
        rows = _json.loads(proc.stdout or "[]")
        return [(r[0], r[1]) for r in rows if isinstance(r, list) and len(r) == 2]
    except Exception:
        return []


def lcb_args_only(input_str):
    """LiveCodeBench `input` is a full call `fn(a = [1,2], b = 3)`; `parse_test_input` wants the
    ARGUMENTS ONLY (`a = [1,2], b = 3`). Strip the outer `fn( … )` via the AST so nested parens and
    commas inside literals are preserved."""
    call = ast.parse(input_str.strip(), mode="eval").body
    if not isinstance(call, ast.Call):
        raise ValueError("LiveCodeBench input is not a function call")
    parts = [ast.unparse(a) for a in call.args] + \
            [f"{k.arg} = {ast.unparse(k.value)}" for k in call.keywords]
    return ", ".join(parts)


def parse_test_input(input_str, order):
    """`'nums = [3,3], target = 6'` + `['nums','target']` → `[[3,3], 6]`."""
    call = ast.parse(f"__f__({input_str})", mode="eval").body
    if not isinstance(call, ast.Call):
        raise ValueError("input is not a call-args string")
    kw = {k.arg: ast.literal_eval(k.value) for k in call.keywords}
    pos = [ast.literal_eval(a) for a in call.args]
    args = []
    for i, name in enumerate(order):
        if name in kw:
            args.append(kw[name])
        elif i < len(pos):
            args.append(pos[i])
        else:
            raise ValueError(f"missing argument {name!r}")
    return args


def py_lit_to_lean(v):
    """Render a Python literal as a Lean literal, or None if unrenderable (dict, None, object)."""
    if isinstance(v, bool):
        return "true" if v else "false"
    if isinstance(v, int):
        return f"({v} : Int)"
    if isinstance(v, float):
        return f"({v} : Float)"
    if isinstance(v, str):
        return '"' + v.replace("\\", "\\\\").replace('"', '\\"') + '"'
    if v is None:
        return None
    if isinstance(v, (list, tuple)):
        parts = [py_lit_to_lean(x) for x in v]
        return None if any(p is None for p in parts) else "[" + ", ".join(parts) + "]"
    return None


def _lean_type_of(values):
    """Infer ONE Lean type covering all concrete Python `values` at a given argument position, or
    None if they are unrenderable/mixed (dict, object, list-mixed-with-scalar). Empty lists default
    their element type to `Int`. Used to give the runtime JSON decoder a target type per field."""
    seen, elems = set(), []
    for v in values:
        if isinstance(v, bool):
            seen.add("bool")
        elif isinstance(v, int):
            seen.add("int")
        elif isinstance(v, float):
            seen.add("float")
        elif isinstance(v, str):
            seen.add("str")
        elif isinstance(v, (list, tuple)):
            seen.add("list"); elems.extend(v)
        else:
            return None
    if "list" in seen:
        if seen != {"list"}:
            return None
        inner = _lean_type_of(elems)
        return None if inner is None else f"(List {inner})"
    if "str" in seen:
        return None if seen != {"str"} else "String"
    if "float" in seen:
        # A column mixing int AND float (e.g. `any_int`, which type-checks its args) must decode as
        # `PyAny` so ints stay `.int` and floats stay `.float` — collapsing to `Float` would make
        # `type(x) == int` wrongly false for the integer rows. A pure-float column stays `Float`.
        return "PastaLean.PyAny" if "int" in seen else "Float"
    if seen == {"bool"}:
        return "Bool"
    return "Int"  # int (or int+bool, which coerces), or no information at all


def _balanced_paren(s, i):
    """`s[i]` must be '('. Return (inner-text-without-the-outer-parens, index-just-past-the-close),
    or (None, len(s)) if unbalanced."""
    depth = 0
    for j in range(i, len(s)):
        if s[j] == "(":
            depth += 1
        elif s[j] == ")":
            depth -= 1
            if depth == 0:
                return s[i + 1:j], j + 1
    return None, len(s)


def _split_top_level(s, sep):
    """Split `s` on the single char `sep`, but only at parenthesis-depth 0."""
    parts, depth, cur = [], 0, ""
    for ch in s:
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
        if ch == sep and depth == 0:
            parts.append(cur)
            cur = ""
        else:
            cur += ch
    parts.append(cur)
    return parts


# Numeric-tower names the exact (`ℚ`/`ℝ`) twin can emit, mapped to the runnable JSON-decodable atom.
_DECODABLE_ATOM = {
    "Int": "Int", "Nat": "Nat", "Bool": "Bool", "String": "String", "Float": "Float",
    "ℤ": "Int", "ℕ": "Nat", "ℚ": "Float", "ℝ": "Float", "Rat": "Float",
}


def _normalize_lean_type(t):
    """Map a Lean type from the twin's signature to a JSON-decodable harness field type, or None if
    the runtime `fromJson?` decoder can't handle it (`PyAny`, functions, class/struct types, …).
    Handles atoms, `List X`, and tuples `A × B × …`, recursively."""
    t = t.strip()
    # Peel one fully-enclosing paren pair: `(List Int)` → `List Int`.
    while t.startswith("(") and t.endswith(")"):
        inner, end = _balanced_paren(t, 0)
        if inner is None or end != len(t):
            break
        t = inner.strip()
    if t in _DECODABLE_ATOM:
        return _DECODABLE_ATOM[t]
    prod = _split_top_level(t, "×")
    if len(prod) > 1:
        parts = [_normalize_lean_type(p) for p in prod]
        if any(p is None for p in parts):
            return None
        return "(" + " × ".join(parts) + ")"
    if t.startswith("List "):
        inner = _normalize_lean_type(t[len("List "):])
        return None if inner is None else f"(List {inner})"
    return None


def _signature_arg_types(converted_lean, fn_name, arity):
    """Parse the `'rn` twin's explicit parameter types from its signature, so harness field types
    come from the transpiler's inferred signature rather than the (possibly out-of-spec) test data —
    one stray Float in an Int column otherwise flips the whole field to `List Float` and the wrapper
    fails to elaborate against the `List Int` twin. Returns a list of `arity` decodable type strings
    (`None` per position it cannot supply), or `None` to fall back entirely to data inference.

    The twin is `def NAME'rn := fun (a : T) ↦ fun (b : U) ↦ …`; we walk the leading `fun (…) ↦`
    binder chain, normalizing each binder's ascribed type."""
    m = re.search(r"\bdef\s+" + re.escape(fn_name) + r"'rn\s*:=", converted_lean)
    if m is None:
        return None
    s, i, n = converted_lean, m.end(), len(converted_lean)
    # A non-contract `mode="run"` twin is an ALIAS `def NAME'rn := NAME`; follow it to the real
    # `def NAME := fun (a : T) ↦ …` whose binder chain actually carries the parameter types (the alias
    # itself has none, so we'd otherwise fall back to `List PyAny`-style data inference and mismatch).
    eol = s.find("\n", i)
    alias = re.fullmatch(r"\s*([A-Za-z_][A-Za-z0-9_'.]*)\s*", s[i:eol if eol != -1 else n])
    if alias is not None:
        m2 = re.search(r"\bdef\s+" + re.escape(alias.group(1)) + r"\s*:=", s)
        if m2 is not None:
            i = m2.end()
    types, guard = [], 0
    while len(types) < arity and guard < 100000:
        guard += 1
        while i < n and s[i].isspace():
            i += 1
        if i >= n:
            break
        if s.startswith("fun", i):
            i += 3
        elif s.startswith("↦", i):
            i += len("↦")
        elif s.startswith("=>", i):
            i += 2
        elif s[i] == "(":
            content, end = _balanced_paren(s, i)
            i = end
            if content is None or ":" not in content:
                return None  # unparseable binder → don't trust any of it
            names_part, _, ty = content.partition(":")
            nty = _normalize_lean_type(ty)
            for _ in names_part.split():  # `(a b : Int)` shares one type across names
                types.append(nty)
        else:
            break  # implicit binder `{…}` or the function body — stop
    if not types:
        return None
    return (types + [None] * arity)[:arity]


def build_test_harness(converted_lean, fn_name, cases, data_path):
    """Append a `main` that runs the computable `fn'rn` twin over the cases, printing `PASSED p/t`
    and a `FAIL <idx>: got <value>` line per failing case. Cases with an unrenderable argument or
    expected value are skipped. Returns (source, runnable_indices, data_json).

    The cases are NOT compiled into the binary — that made a big-dataset problem embed a multi-MB
    Lean literal, whose elaboration/C-codegen took 30 GB / hours and wedged the single native build.
    Instead the data is written (by the caller) to `data_path` as JSON and READ AT RUNTIME: the
    binary carries only the solution, a small per-field `Lean.fromJson?` decoder, and the check
    loop. The decoder's target types are inferred from the concrete case values."""
    rn = f"{fn_name}'rn"
    # Renderable cases (same skip rule as before: any None/dict/object value drops the case).
    renderable = []
    for idx, (args, expected) in enumerate(cases):
        if py_lit_to_lean(expected) is None or any(py_lit_to_lean(a) is None for a in args):
            continue
        renderable.append((idx, list(args), expected))
    arity = len(renderable[0][1]) if renderable else 0
    kept = [r for r in renderable if len(r[1]) == arity]
    arg_types = [_lean_type_of([r[1][i] for r in kept]) for i in range(arity)]

    # Prefer the twin's inferred parameter types over types guessed from the (possibly out-of-spec)
    # test data: one stray Float in an Int column otherwise flips the whole field to `List Float`,
    # and the wrapper fails to elaborate against the `List Int` twin. Cases whose data doesn't
    # conform to the signature type are then dropped by the runtime `fromJson?` decoder, rather than
    # breaking the whole harness compile. Falls back to data inference where the signature is
    # unparseable or not a decodable type.
    sig_types = _signature_arg_types(converted_lean, fn_name, arity)
    if sig_types is not None:
        arg_types = [sig if sig is not None else data
                     for sig, data in zip(sig_types, arg_types)]

    if not kept or any(t is None for t in arg_types):
        body = "\n".join([converted_lean.rstrip(), "",
                          'def main : IO Unit := IO.println "PASSED 0/0"', ""])
        return body, [], "[]"

    runnable = [idx for (idx, _a, _e) in kept]
    data_json = json.dumps([[idx] + args + [expected] for (idx, args, expected) in kept])

    # The expected value is NOT given a data-inferred type — a stray Float in the *result* column
    # would otherwise mistype `e` (`List Float`) against the twin's `List Int` return and fail the
    # whole compile. Instead it's carried as a raw `Json` and decoded per-case AT THE CALL'S ACTUAL
    # RESULT TYPE via `_decodeLike _got`, so tuple/int/float returns all resolve correctly and only
    # genuinely out-of-spec expected values are dropped (not compiled away).
    in_names = ["idx"] + [f"a{i}" for i in range(arity)]
    in_types = ["Nat"] + arg_types
    disc = ", ".join(f"Lean.fromJson? (α := {t}) (f.getD {k} .null)"
                     for k, t in enumerate(in_types))
    ok_pat = ", ".join(f".ok {n}" for n in in_names)
    wild = ", ".join("_" for _ in in_types)
    tuple_ty = " × ".join(in_types + ["Lean.Json"])
    pat = "(" + ", ".join(in_names + ["ejson"]) + ")"
    call = rn + ((" " + " ".join(f"a{i}" for i in range(arity))) if arity else "")
    path_lit = str(data_path).replace("\\", "\\\\").replace('"', '\\"')
    body = "\n".join([
        "import Lean.Data.Json",
        converted_lean.rstrip(), "",
        # The converted code defines the twin inside `namespace PastaLean.User.Root`; open it so the
        # harness `main` can call `<fn>'rn` unqualified (else `unknown identifier <fn>'rn`).
        "open PastaLean.User.Root", "",
        # Float results are compared with a tolerance, not exact `==`: Lean's Float parse/division can
        # differ from CPython's by ~1 ULP, so bit-equality is the wrong test for a floating-point
        # answer. Non-float types fall back to `BEq` (exact). Lists/tuples lift the comparison.
        "private class _PyTestEq (α : Type) where teq : α → α → Bool",
        "private instance : _PyTestEq Float := "
        "⟨fun a b => (a - b).abs ≤ (1e-9 : Float) + (1e-9 : Float) * b.abs⟩",
        "private instance (priority := 100) {α} [BEq α] : _PyTestEq α := ⟨(· == ·)⟩",
        "private instance {α} [_PyTestEq α] : _PyTestEq (List α) := "
        "⟨fun a b => a.length == b.length && (a.zip b).all (fun p => _PyTestEq.teq p.1 p.2)⟩",
        "private instance {α β} [_PyTestEq α] [_PyTestEq β] : _PyTestEq (α × β) := "
        "⟨fun a b => _PyTestEq.teq a.1 b.1 && _PyTestEq.teq a.2 b.2⟩",
        "private def _pyTestEq {α} [_PyTestEq α] (a b : α) : Bool := _PyTestEq.teq a b", "",
        # A twin carrying a stray `print` (→ `IO α`) or a spurious `try/except` (→ `PyExcept α`,
        # i.e. `ExceptT PyException IO α`) is EFFECTFUL, not a bare value; run it and compare the
        # result it returns. `_RunTwin` reduces pure / IO / PyExcept twins to `IO (Option α)` (a raised
        # exception → `none`). The pure fallback is lowest priority so the effectful instances win.
        "private class _RunTwin (τ : Type) (α : outParam Type) where run : τ → IO (Option α)",
        "private instance {α} : _RunTwin (IO α) α := ⟨fun m => do let r ← m; pure (some r)⟩",
        "private instance {α} : _RunTwin (ExceptT PastaLean.PyException IO α) α := "
        "⟨fun m => do match ← ExceptT.run m with | .ok a => pure (some a) | .error _ => pure none⟩",
        "private instance (priority := 50) {α} : _RunTwin α α := ⟨fun a => pure (some a)⟩", "",
        # Decode the expected JSON at the SAME type as the value the twin computed: `_pat`'s type
        # (`α`) is unified with `_got` at the call site, so no return-type annotation is needed.
        "private def _decodeLike {α : Type} [Lean.FromJson α] (_pat : α) "
        "(j : Lean.Json) : Option α := (Lean.fromJson? j).toOption", "",
        f"private def _decodeCase' (j : Lean.Json) : Option ({tuple_ty}) :=",
        "  match j.getArr? with",
        "  | .error _ => none",
        "  | .ok f =>",
        f"    match {disc} with",
        f"    | {ok_pat} => some ({', '.join(in_names)}, f.getD {arity + 1} .null)",
        f"    | {wild} => none", "",
        "def main : IO Unit := do",
        "  let _out ← IO.getStdout",
        f'  let _raw ← IO.FS.readFile "{path_lit}"',
        "  let _cases := match Lean.Json.parse _raw with",
        "    | .ok j => ((j.getArr?).toOption.getD #[]).toList.filterMap _decodeCase'",
        "    | .error _ => []",
        "  let mut _p := 0",
        "  let mut _t := 0",
        f"  for {pat} in _cases do",
        f"    let _got? ← _RunTwin.run ({call})",
        "    match _got? with",
        # Twin raised (effectful path): count as attempted-and-failed, not silently dropped.
        '    | none => _t := _t + 1; IO.println s!"FAIL {idx}: twin raised"',
        "    | some _got =>",
        "      match _decodeLike _got ejson with",
        # Expected value undecodable at the result type → out-of-spec case, drop (don't count).
        "      | none => pure ()",
        "      | some e =>",
        "        _t := _t + 1",
        # `repr` prints what Lean computed so a failure is debuggable without a rerun.
        "        if _pyTestEq _got e then _p := _p + 1",
        '        else IO.println s!"FAIL {idx}: got {repr _got}"',
        # Flush a running count each case so a native run that times out still reports partials
        # (how many passed / attempted before it hung) instead of a bare 0/N.
        '        _out.putStr s!"PROG {_t} {_p}\\n"; _out.flush',
        '  IO.println s!"PASSED {_p}/{_t}"', ""])
    return body, runnable, data_json


def load_callable(fn_src, method):
    """Exec `fn_src` (with the star-import prelude) and return the `method` callable, or None."""
    ns = {}
    try:
        # Dataset sources are third-party text; their SyntaxWarnings (`'\/'` in a regex, …) say
        # nothing about the transpiler and would otherwise pepper the run log.
        with warnings.catch_warnings():
            warnings.simplefilter("ignore")
            exec(_PRELUDE + fn_src, ns)  # noqa: S102
    except Exception:  # noqa: BLE001
        return None
    fn = ns.get(method)
    if callable(fn):
        return fn
    try:
        name = next(n.name for n in ast.parse(fn_src).body if isinstance(n, ast.FunctionDef))
    except (SyntaxError, StopIteration):
        return None
    return ns.get(name)


# A reference solution runs in *this* process to produce ground-truth outputs. A pathological input
# — exponentially many source→target paths, O(n^4) 4Sum quadruplets — makes it allocate without
# bound, and the OS OOM-killer sends the whole run SIGKILL (a bare "Killed"). A Python `except` can't
# catch that. So run the reference in a forked child capped by an address-space rlimit and a
# wall-clock timeout: the cap turns a runaway into a `MemoryError` *inside the child* (before the
# giant result can cross the pipe back), the timeout catches an infinite loop, and the case is just
# dropped. One bad input costs one dead child, not the run.
_REF_MEM_LIMIT = 4 * 1024**3   # 4 GiB of address space per reference call
_REF_CASE_TIMEOUT = 10         # wall-clock seconds allowed for a single case


def _ref_stream_worker(conn, fn, arg_list, start, mem_bytes):
    """Child side: compute `fn(*args)` for each case under a memory cap, streaming a
    `(global_index, ok, payload)` tuple back as each one finishes — so results already computed
    survive even when a *later* case OOMs or hangs and takes this process down."""
    try:
        import resource
        resource.setrlimit(resource.RLIMIT_AS, (mem_bytes, mem_bytes))
    except (ValueError, OSError, ImportError):
        pass  # platform without RLIMIT_AS — the parent's per-case timeout is still a backstop
    # The child talks only over the pipe, so its stdio is pure noise in the run log. Solutions that
    # print, or that spawn their own threads (a "web crawler" solution whose threads raise past our
    # try/except and hit `threading.excepthook`), would otherwise spew into the parent's stderr.
    try:
        devnull = open(os.devnull, "w")
        os.dup2(devnull.fileno(), 1)
        os.dup2(devnull.fileno(), 2)
        threading.excepthook = lambda _args: None
    except Exception:  # noqa: BLE001
        pass
    for offset, args in enumerate(arg_list):
        idx = start + offset
        try:
            conn.send((idx, True, fn(*args)))
        except MemoryError:
            # The heap is wedged at the cap; a further send would fail too. Bail — the parent
            # infers this case failed from the stream stopping here.
            break
        except BaseException as exc:  # noqa: BLE001  (report, don't crash the child)
            try:
                conn.send((idx, False, f"{type(exc).__name__}: {exc}"))
            except Exception:  # noqa: BLE001
                break
    conn.close()
    # Hard-exit: a solution may have left non-daemon threads running, which would otherwise keep
    # this child alive until the parent's timeout terminates it.
    os._exit(0)


def guarded_ref_batch(fn, arg_list, *, mem_bytes=_REF_MEM_LIMIT, timeout=_REF_CASE_TIMEOUT):
    """Run `fn` over `arg_list` in memory-/time-bounded child processes; return a `(ok, value)` list
    aligned to `arg_list`. A single pathological input — one that would OOM-kill the whole run — is
    confined to a child and dropped as `(False, reason)`; because the child streams, the good cases
    *before* it survive, and the child is restarted to finish the cases *after* it. Normal input
    costs one fork; each bomb costs one extra fork."""
    n = len(arg_list)
    results = [None] * n
    ctx = mp.get_context("fork")
    i = 0
    while i < n:
        recv, send = ctx.Pipe(duplex=False)
        proc = ctx.Process(target=_ref_stream_worker,
                           args=(send, fn, arg_list[i:], i, mem_bytes), daemon=True)
        proc.start()
        send.close()  # parent holds only the read end, so `recv` sees EOF the moment the child dies
        while i < n:
            if not recv.poll(timeout):   # no result within the per-case budget → stalled on case i
                break
            try:
                idx, ok, payload = recv.recv()
            except EOFError:             # child finished, or died on case i (OOM)
                break
            results[idx] = (ok, payload)
            i = idx + 1
        if proc.is_alive():
            proc.terminate()
        proc.join(5)
        recv.close()
        # If we stopped short of the end, `arg_list[i]` is the case that stalled/killed the child.
        # Drop it and step past so the next child can finish the remainder.
        if i < n:
            if results[i] is None:
                results[i] = (False, "timeout-or-oom")
            i += 1
    return [(False, "not-run") if r is None else r for r in results]


def run_python_check(fn_src, method, cases):
    """Run the groundtruth against `cases` (whose expected values it produced). Returns (p, t)."""
    fn = load_callable(fn_src, method)
    if fn is None:
        return 0, 0
    results = guarded_ref_batch(fn, [args for args, _ in cases])
    passed = sum(1 for (ok, value), (_, expected) in zip(results, cases)
                 if ok and value == expected)
    return passed, len(cases)


def _backend_mem_limit_preexec():
    """Cap the `palc eval` backend's address space (opt-in via `PASTALEAN_EVAL_MEM_GB`) so a runaway
    harness — an exponential `fn'rn` twin — OOMs *itself*, a clean crash the driver reboots from,
    instead of pushing the machine into the OS OOM-killer, which can take down this parent too. Off
    by default: too low a cap starves the Mathlib environment and fails every problem."""
    gb = os.environ.get("PASTALEAN_EVAL_MEM_GB")
    if not gb:
        return
    try:
        import resource
        limit = int(float(gb) * 1024**3)
        resource.setrlimit(resource.RLIMIT_AS, (limit, limit))
    except (ValueError, OSError, ImportError):
        pass


class WarmLeanEval:
    """A persistent `lake exe palc eval` process: boots Mathlib ONCE, then evaluates harness files
    in-process, so the ~5 s import cost is paid once instead of per problem. `eval(path)` returns
    `(captured_stdout, None)`, or `(None, error)`. On a per-harness timeout (a non-terminating
    conversion would hang the shared process) it kills and re-boots on the next call, so one bad
    problem costs one re-boot, not the whole run."""

    READY, BEGIN, END = "===PACEVAL-READY===", "===PACEVAL-BEGIN===", "===PACEVAL-END==="
    # Boots are serialized across all workers (concurrent Mathlib imports crash) — class-wide lock.
    _boot_lock = threading.Lock()

    # Proactively reboot after this many evals: a long-lived backend accumulates heartbeat budget
    # and memory, and past ~1950 translations it hits an all-fail cliff (heartbeat poisoning). A
    # scheduled reboot (~10 s Mathlib load) keeps it fresh and is far cheaper than a run of spurious
    # timeouts. 0 disables.
    REBOOT_EVERY = 400

    def __init__(self, timeout=15, boot_timeout=300, verbose=True):
        self.timeout = timeout
        self.boot_timeout = boot_timeout
        self.verbose = verbose
        self.proc = None
        self._q = None       # lines from the backend's stdout, fed by a reader thread
        self._boots = 0
        self._evals = 0      # evals since the current boot; triggers a proactive reboot

    def _log(self, msg):
        if self.verbose:
            print(f"    [warm] {msg}", flush=True)

    def _read_lines(self, proc, q):
        """Reader thread: forward the backend's stdout line-by-line into `q`, then a `None` on EOF.
        A dedicated thread (rather than select) is what makes timeouts reliable — `select` on a
        buffered pipe misses lines already sitting in Python's read buffer."""
        try:
            for line in proc.stdout:
                q.put(line)
        except Exception:  # noqa: BLE001
            pass
        q.put(None)

    def _start(self):
        # Serialize boots across workers: concurrent `lake exe` launches contend on the Lake lock and
        # the Mathlib-import I/O/memory spike, which crashes some ("died during boot"). One at a time.
        with WarmLeanEval._boot_lock:
            self._boots += 1
            self._log(f"booting palc eval backend (boot #{self._boots}; Mathlib load ~10s)…")
            # stderr → DEVNULL so a crash (broken pipe / OOM 'resource vanished') can't pollute stdout.
            self.proc = subprocess.Popen(
                ["lake", "exe", "palc", "eval"], cwd=REPO_ROOT,
                stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL, text=True,
                preexec_fn=_backend_mem_limit_preexec)
            self._q = queue.Queue()
            threading.Thread(target=self._read_lines, args=(self.proc, self._q), daemon=True).start()
            deadline = time.time() + self.boot_timeout
            while True:
                try:
                    line = self._q.get(timeout=max(0.0, deadline - time.time()))
                except queue.Empty:
                    self._kill(); raise TimeoutError("palc eval boot timed out")
                if line is None:
                    self._kill(); raise RuntimeError("palc eval died during boot")
                if line.strip() == self.READY:
                    self._log("ready")
                    return

    def _kill(self):
        if self.proc:
            try:
                self.proc.kill()
                self.proc.wait(timeout=5)
            except Exception:  # noqa: BLE001
                pass
        self.proc, self._q = None, None

    def eval(self, path):
        # Proactive reboot before the poisoning cliff — cheaper than a run of spurious timeouts.
        if self.REBOOT_EVERY and self._evals and self._evals % self.REBOOT_EVERY == 0:
            self._log(f"proactive reboot after {self._evals} evals (avoid heartbeat poisoning)")
            self._kill()
        self._evals += 1
        # (Re)boot if the backend is down; a boot failure returns an error rather than crashing the run.
        if self.proc is None or self.proc.poll() is not None:
            try:
                self._start()
            except Exception as e:  # noqa: BLE001
                self._kill()
                return None, f"backend boot failed: {e}"
        try:
            self.proc.stdin.write(str(Path(path).resolve()) + "\n")
            self.proc.stdin.flush()
        except (BrokenPipeError, OSError):
            self._kill()
            return None, "eval process died"
        deadline, lines, capturing = time.time() + self.timeout, [], False
        while True:
            try:
                line = self._q.get(timeout=max(0.0, deadline - time.time()))
            except queue.Empty:
                self._log(f"timeout after {self.timeout}s on {Path(path).name} — restarting backend")
                self._kill(); return None, "timeout"
            if line is None:
                self._kill(); return None, "eval process died"
            s = line.rstrip("\n")
            if s == self.BEGIN:
                capturing, lines = True, []
            elif s == self.END:
                return "\n".join(lines), None
            elif capturing:
                lines.append(s)

    def close(self):
        if self.proc:
            try:
                self.proc.stdin.close()
            except Exception:  # noqa: BLE001
                pass
            self._kill()


# --------------------------------------------------------------------------------------
# The harness
# --------------------------------------------------------------------------------------

class CPastaEval:
    """Fetch, convert, evaluate, and plot one CP dataset directory."""

    def __init__(self, dataset, *, source=None, timeout=15, max_tests=0, skip_python=False,
                 random_n=None, seed=0, problems=None, max_solutions=3, split="test",
                 workers=None, interpret=False, jobs=None, native_chunk=500,
                 exclude_file="cp_harness/excluded_problems.txt"):
        self.dataset = Path(dataset)
        self.source = source
        self.timeout = timeout
        # Default eval path COMPILES every harness in one build (Mathlib loaded once) then runs the
        # native binaries — instant execution, no timeouts, no per-timeout Mathlib reboot.
        # `--interpret` falls back to the warm interpreter pool.
        self.interpret = interpret
        # Parallel workers: interpret-mode warm backends (~1.5 GB each), or native run concurrency.
        self.workers = workers or max(1, min(16, (os.cpu_count() or 4) // 4))
        # `lake build` parallelism. Lake defaults to *every* core, which starves the rest of the
        # machine; leave headroom (~3/4 of cores, hard-capped) unless `--jobs` says otherwise.
        self.jobs = jobs or max(1, min(48, ((os.cpu_count() or 4) * 3) // 4))
        # Native dispatcher chunk size: harnesses per linked `cpharness_run` binary. One giant binary
        # over the whole corpus (~2100 harnesses) can fail to link/compile, and that used to zero out
        # the entire evaluation; chunking bounds the link scale and the blast radius of any failure.
        self.native_chunk = native_chunk
        self.max_tests = max_tests
        self.skip_python = skip_python
        self.random_n = random_n
        self.seed = seed
        self.problem_names = list(problems) if problems else None
        self.max_solutions = max_solutions
        self.split = split
        self.exclude_file = Path(exclude_file)
        self._session = None
        self._warm = None
        # Problems that require reference (`--heap`) semantics: an explicit, curatable list under the
        # dataset (`heap_problems.txt`, one problem name per line). Value semantics silently drops cursor
        # writes for these trie / linked-list problems, so the harness translates them with `heap=True`.
        hf = self.dataset / "heap_problems.txt"
        self._heap_problems = set(
            ln.strip() for ln in hf.read_text().splitlines() if ln.strip() and not ln.startswith("#")
        ) if hf.exists() else set()

    # -- lifecycle ---------------------------------------------------------------------

    @property
    def session(self):
        """The warm Lean backend, booted on first use. Strict: no `pyUnsupported` degradation."""
        if self._session is None:
            self._session = Session(target="command", mode="both", best_effort=False).start()
        return self._session

    @property
    def warm(self):
        """The warm `palc eval` backend, booted on first use (Mathlib loaded once for all harnesses)."""
        if self._warm is None:
            self._warm = WarmLeanEval(timeout=self.timeout)
        return self._warm

    def close(self):
        if self._session is not None:
            self._session.close()
            self._session = None
        if self._warm is not None:
            self._warm.close()
            self._warm = None

    def __enter__(self):
        return self

    def __exit__(self, exc_type, exc, tb):
        self.close()

    @property
    def tmp_dir(self):
        d = self.dataset / ".tmp"
        d.mkdir(parents=True, exist_ok=True)
        return d

    def _prepare_tmp(self):
        """Clear leftover `.tmp` scratch and warn on low disk — the overnight run died of a full disk
        (harness files never cleaned), which also causes spurious I/O timeouts."""
        import shutil
        d = self.dataset / ".tmp"
        if d.is_dir():
            n = sum(1 for _ in d.iterdir())
            if n:
                shutil.rmtree(d, ignore_errors=True)
                print(f"[*] Cleared {n} stale files from {d}", flush=True)
        d.mkdir(parents=True, exist_ok=True)
        free_gb = shutil.disk_usage(self.dataset).free / 2**30
        if free_gb < 10:
            print(f"[!] WARNING: only {free_gb:.1f} GB free on the eval disk — a full corpus run may "
                  f"exhaust it (that crashed the last overnight run). Free space before proceeding.",
                  flush=True)

    # -- selection ---------------------------------------------------------------------

    def all_problems(self):
        """Every problem directory, sorted by name."""
        if not self.dataset.is_dir():
            return []
        return sorted(p for p in self.dataset.iterdir()
                      if p.is_dir() and not p.name.startswith("."))

    def problems(self):
        """The problem directories this run operates on: `problems` filter, then `random_n`.

        Seeded, so convert / evaluate / plot all see the *same* subset for a given seed.
        """
        probs = self.all_problems()
        if self.problem_names:
            wanted = set(self.problem_names)
            probs = [p for p in probs if p.name in wanted]
        if self.random_n is not None and self.random_n < len(probs):
            probs = sorted(random.Random(self.seed).sample(probs, self.random_n))
        return probs

    def kind_of(self, prob_dir):
        """The test model a problem was fetched under: `"function"` or `"stdio"`."""
        kind_file = prob_dir / KIND_FILE
        return kind_file.read_text().strip() if kind_file.exists() else KIND_STDIO

    def load_excluded(self):
        """Problem names never to (re-)download; `#` comments and blanks ignored."""
        if not self.exclude_file.exists():
            return set()
        names = set()
        for line in self.exclude_file.read_text().splitlines():
            line = line.split("#", 1)[0].strip()
            if line:
                names.add(line)
        return names

    # -- fetch -------------------------------------------------------------------------

    def fetch(self, num=10):
        """Download `num` problems (None / 'max' = the whole dataset) from `self.source`."""
        if self.source not in self.SOURCES:
            raise ValueError(f"--source must be one of {sorted(self.SOURCES)}, got {self.source!r}")
        if isinstance(num, str):
            num = parse_count(num)
        self.dataset.mkdir(parents=True, exist_ok=True)
        return self.SOURCES[self.source](self, num)

    def _stream(self, repo, split):
        try:
            from datasets import load_dataset
        except ImportError as e:  # pragma: no cover
            raise SystemExit("ERROR: `datasets` not installed. Run: pip install datasets") from e
        return load_dataset(repo, split=split, streaming=True)

    def _fetch_loop(self, stream, save, num, excluded, log_every):
        kept = scanned = 0
        for item in stream:
            scanned += 1
            if save(item, excluded):
                kept += 1
            if not self.problem_names and num is not None and kept >= num:
                break
            if scanned % log_every == 0:
                print(f"    ...scanned {scanned}, kept {kept}")
        print(f"\n[*] Done. Kept {kept} problem(s) into {self.dataset}")
        return 0

    def fetch_codecontests(self, num):
        """DeepMind CodeContests, Python3 solutions importing only `math`. Model: stdio."""
        excluded = self.load_excluded()
        print(f"[*] Streaming CodeContests ({self.split} split)...")
        stream = self._stream("deepmind/code_contests", self.split)
        return self._fetch_loop(stream, self._save_codecontests_problem, num, excluded, 50)

    def fetch_leetcode(self, num):
        """`newfacade/LeetCodeDataset`: the entry method as a free function. Model: function."""
        excluded = self.load_excluded()
        print("[*] Streaming newfacade/LeetCodeDataset (train split)...")
        stream = self._stream("newfacade/LeetCodeDataset", "train")
        return self._fetch_loop(stream, self._save_leetcode_problem, num, excluded, 100)

    def fetch_livecodebench(self, num):
        """`livecodebench/execution-v2` (the latest LiveCodeBench execution/groundtruth set — its
        cumulative problem window is the v6 release): ground-truth `code` + a `fn(args)` call +
        expected `output`. Model: function. Rows sharing the same `code` (one function, many inputs)
        are grouped into one problem with many tests, so each function is transpiled once. Converted
        files are NOT persisted beyond the dataset dir (same as any other source)."""
        excluded = self.load_excluded()
        print("[*] Streaming livecodebench/execution-v2 (test split)...")
        stream = self._stream("livecodebench/execution-v2", "test")
        groups = {}   # code -> {"function_name", "id", "difficulty", "contest_date", "tests": [...]}
        for item in stream:
            code = (item.get("code") or "").strip()
            fn = item.get("function_name") or ""
            if not code or not fn:
                continue
            g = groups.setdefault(code, {"function_name": fn, "id": item.get("id") or "",
                                         "difficulty": item.get("difficulty"),
                                         "contest_date": str(item.get("contest_date") or ""),
                                         "tests": []})
            g["tests"].append((item.get("input") or "", str(item.get("output")) if item.get("output") is not None else ""))
        kept = 0
        for code, g in groups.items():
            if num and num > 0 and kept >= num:
                break
            if self._save_livecodebench_problem(code, g, excluded):
                kept += 1
        print(f"[*] LiveCodeBench: {kept} problem(s) from {len(groups)} unique function(s).")
        return kept

    def _save_livecodebench_problem(self, code, g, excluded):
        method = g["function_name"]
        # Disambiguate same-named functions with different bodies by a short content hash.
        import hashlib
        task_id = f"{method}_{hashlib.sha1(code.encode()).hexdigest()[:6]}"
        if self.problem_names and task_id not in self.problem_names and method not in self.problem_names:
            return False
        prob_name = sanitize_problem_name(task_id)
        if prob_name in excluded:
            return False
        try:
            params = param_names(code)
        except (SyntaxError, StopIteration):
            return False
        cases = []
        for (inp, out) in g["tests"]:
            try:
                cases.append({"input": lcb_args_only(inp), "output": out})
            except (SyntaxError, ValueError):
                continue
        if not cases:
            return False

        # A LiveCodeBench execution row ships only ONE input/output, which is weak evidence of
        # correctness. Since we have the ground-truth `code`, synthesize many more inputs of the same
        # shape and take the reference's own outputs as expected — a differential test.
        if not self.problem_names:  # skip the costly expansion when targeting specific problems
            try:
                base_args = parse_test_input(cases[0]["input"], params)
            except (SyntaxError, ValueError):
                base_args = None
            if base_args is not None:
                for (inp, out_repr) in expand_lcb_tests(LCB_PREAMBLE + "\n" + code, method, params, base_args):
                    cases.append({"input": inp, "output": out_repr})

        prob_dir = self.dataset / prob_name
        prob_dir.mkdir(parents=True, exist_ok=True)
        (prob_dir / KIND_FILE).write_text(KIND_FUNCTION)
        (prob_dir / "problem.txt").write_text(f"LiveCodeBench execution: {method}")
        (prob_dir / "meta.json").write_text(json.dumps(
            {"task_id": task_id, "method": method, "params": params,
             "difficulty": g.get("difficulty"), "contest_date": g.get("contest_date"),
             "source": "livecodebench", "lcb_id": g["id"]}, indent=2))
        sols_dir = prob_dir / "solutions"
        sols_dir.mkdir(exist_ok=True)
        (sols_dir / "sol_0.py").write_text(LCB_PREAMBLE + "\n\n" + code + "\n")
        tests_dir = prob_dir / "tests"
        tests_dir.mkdir(exist_ok=True)
        (tests_dir / "tests.json").write_text(json.dumps(cases, indent=2))
        print(f"[+] {task_id}: fn `{method}({', '.join(params)})`, {len(cases)} test(s)")
        return True

    #: Source adapters. Each writes the normalized layout and tags every problem with its `kind`.
    SOURCES = {
        "codecontests": fetch_codecontests,     # stdio model
        "leetcode": fetch_leetcode,             # function model
        "livecodebench": fetch_livecodebench,   # function model (execution scenario, ground-truth code)
    }

    def _save_codecontests_problem(self, item, excluded):
        name = item["name"]
        if self.problem_names and name not in self.problem_names:
            return False
        prob_name = sanitize_problem_name(name)
        if prob_name in excluded:
            return False

        languages, sources = item["solutions"]["language"], item["solutions"]["solution"]
        math_only = [
            sources[i] for i, lang in enumerate(languages)
            if lang == PYTHON3_LANG_ID
            and (mods := imported_modules(sources[i])) is not None
            and mods.issubset(ALLOWED_IMPORTS)
        ]
        inputs = (item["public_tests"]["input"] + item["private_tests"]["input"]
                  + item["generated_tests"]["input"])
        outputs = (item["public_tests"]["output"] + item["private_tests"]["output"]
                   + item["generated_tests"]["output"])
        if not math_only or not inputs:
            return False

        prob_dir = self.dataset / prob_name
        prob_dir.mkdir(parents=True, exist_ok=True)
        (prob_dir / KIND_FILE).write_text(KIND_STDIO)
        (prob_dir / "problem.txt").write_text(item.get("description", ""))
        sols_dir = prob_dir / "solutions"
        sols_dir.mkdir(exist_ok=True)
        for i, src in enumerate(math_only[: self.max_solutions]):
            (sols_dir / f"sol_{i}.py").write_text(src)
        tests_dir = prob_dir / "tests"
        tests_dir.mkdir(exist_ok=True)
        for i, (inp, outp) in enumerate(zip(inputs, outputs)):
            (tests_dir / f"test_{i}.in").write_text(inp)
            (tests_dir / f"test_{i}.out").write_text(outp)
        print(f"[+] {prob_name}: {len(math_only[: self.max_solutions])} math-only solution(s), "
              f"{len(inputs)} test(s)")
        return True

    def _save_leetcode_problem(self, item, excluded):
        task_id = item.get("task_id") or f"q{item.get('question_id')}"
        if self.problem_names and task_id not in self.problem_names:
            return False
        prob_name = sanitize_problem_name(task_id)
        if prob_name in excluded:
            return False

        method = entry_method_name(item.get("entry_point", ""))
        fn_src = extract_function(item.get("completion", ""), method)
        if not fn_src:
            return False  # not a self-contained function
        try:
            params = param_names(fn_src)
        except SyntaxError:
            return False
        cases = item.get("input_output") or []
        if not cases:
            return False

        prob_dir = self.dataset / prob_name
        prob_dir.mkdir(parents=True, exist_ok=True)
        (prob_dir / KIND_FILE).write_text(KIND_FUNCTION)
        (prob_dir / "problem.txt").write_text(item.get("problem_description", ""))
        (prob_dir / "meta.json").write_text(json.dumps(
            {"task_id": task_id, "method": method, "params": params,
             "difficulty": item.get("difficulty")}, indent=2))

        sols_dir = prob_dir / "solutions"
        sols_dir.mkdir(exist_ok=True)
        # The dataset's `prompt` preamble binds `inf`, `Counter`, `List`, … which the completion
        # reads freely; without it the extracted function is not even valid Python.
        prompt = item.get("prompt", "")
        completion = item.get("completion", "")
        (sols_dir / "sol_0.py").write_text(
            self_contained_source(prompt, completion, fn_src) + "\n")
        (sols_dir / "_prompt.py").write_text(prompt + "\n")  # untouched, for provenance

        tests_dir = prob_dir / "tests"
        tests_dir.mkdir(exist_ok=True)
        (tests_dir / "tests.json").write_text(json.dumps(list(cases), indent=2))
        (tests_dir / "asserts.py").write_text(item.get("test", "") + "\n")
        print(f"[+] {task_id}: fn `{method}({', '.join(params)})`, {len(cases)} test(s)")
        return True

    # -- convert -----------------------------------------------------------------------

    def compile_check(self, lean_path, timeout=180):
        """Elaborate a generated Lean file; return (ok, error_text).

        A generated program can hang the elaborator/kernel (e.g. a closed program over reducible
        library fns, which emits `set_option maxHeartbeats 0` so there is no heartbeat backstop). A
        bare `subprocess.run` with no timeout then blocks the ENTIRE sweep forever. We cap it and, on
        timeout, kill the whole process group (`lake` spawns `lean`, which would otherwise orphan and
        keep burning a core) so one bad file becomes a single `compile_fail`, not a dead run.
        """
        # Resolve to absolute: the command runs with cwd=REPO_ROOT but `lean_path` is relative to the
        # dataset, so a relative `--dataset` yields a spurious "no such file" compile_fail otherwise.
        proc = subprocess.Popen(["lake", "env", "lean", str(Path(lean_path).resolve())],
                                cwd=REPO_ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                text=True, start_new_session=True)
        try:
            out, err = proc.communicate(timeout=timeout)
        except subprocess.TimeoutExpired:
            import signal
            try:
                os.killpg(os.getpgid(proc.pid), signal.SIGKILL)
            except ProcessLookupError:
                pass
            proc.communicate()
            return (False, f"compile timed out after {timeout}s (elaboration/kernel hang)")
        return (True, "") if proc.returncode == 0 else (False, err or out)

    def convert_solution(self, sol_path, lean_dir, wrap):
        """Translate one solution and compile-check it. Returns (status, concise_error_or_None)."""
        name = sol_path.stem
        source = sol_path.read_text()
        # stdio solutions are bare top-level code; function solutions must NOT be wrapped, or the
        # `def` ends up nested inside the guard and disappears.
        if wrap:
            src_path = self.tmp_dir / f"{name}_wrapped.py"
            src_path.write_text(wrap_for_main(source))
        else:
            src_path = sol_path

        status_path = lean_dir / f"{name}.status"
        log_path = lean_dir / f"{name}.log"

        use_heap = sol_path.parent.parent.name in self._heap_problems
        try:
            result = self.session.translate_file(src_path, heap=use_heap)
        except Exception as e:  # noqa: BLE001  (a backend crash must not kill the sweep)
            result = None
            error_text = f"{type(e).__name__}: {e}"
        else:
            error_text = result.error or "empty output"

        if result is None or not result.ok or not (result.lean_code or "").strip():
            # An out-of-scope library (concurrency, regex, datetime, interactive judge) is reported as
            # `skipped`, not `convert_fail` — it is not a codegen shortcoming we could fix.
            reason = out_of_scope_reason(source)
            if reason is not None:
                status_path.write_text("skipped")
                log_path.write_text(error_text)
                return "skipped", reason
            status_path.write_text("convert_fail")
            log_path.write_text(error_text)
            return "convert_fail", summarize_error("convert_fail", error_text)

        lean_path = lean_dir / f"{name}.lean"
        lean_path.write_text(result.lean_code)

        ok, err = self.compile_check(lean_path)
        if not ok:
            status_path.write_text("compile_fail")
            log_path.write_text(err)
            return "compile_fail", summarize_error("compile_fail", err)

        status_path.write_text("ok")
        log_path.unlink(missing_ok=True)
        return "ok", None

    def convert(self):
        """Translate + compile-check every selected problem. Writes `convert_summary.json`.

        Two independent parallelisms, both automatic: the TRANSLATE is batched through
        `Session.translate_files`, which shards across worker backends INSIDE PastaLean; the
        compile-check (a separate concern) fans out over a thread pool. `sol_0` unchanged serially."""
        self._prepare_tmp()
        problems, totals, histogram = {}, {"ok": 0, "convert_fail": 0, "compile_fail": 0, "skipped": 0}, {}

        # Phase 1 — gather work-units and materialise the (uniquely-named, so a batch can coexist)
        # `__main__`-wrapped sources. `unit = (prob, sol_name, name, lean_dir, source, src_path)`.
        units = []
        for prob_dir in self.problems():
            sols_dir = prob_dir / "solutions"
            if not sols_dir.is_dir():
                continue
            lean_dir = prob_dir / "lean"
            lean_dir.mkdir(exist_ok=True)
            wrap = self.kind_of(prob_dir) != KIND_FUNCTION
            for sol_path in sorted(sols_dir.glob("sol_*.py")):
                source = sol_path.read_text()
                if wrap:
                    src_path = self.tmp_dir / f"{prob_dir.name}__{sol_path.stem}_wrapped.py"
                    src_path.write_text(wrap_for_main(source))
                else:
                    src_path = sol_path
                units.append((prob_dir.name, sol_path.name, sol_path.stem, lean_dir, source, src_path))

        # Phase 2 — batch-translate (PastaLean parallelises internally over its own backend pool).
        # Problems on the dataset's heap list get reference semantics (`heap=True`); the rest use the
        # default value semantics. Two batches keep each worker shard's heap mode uniform.
        by_src = {str(Path(u[5]).resolve()): u for u in units}
        translated = {}
        for batch, use_heap in ((([u for u in units if u[0] not in self._heap_problems]), False),
                                (([u for u in units if u[0] in self._heap_problems]), True)):
            if not batch:
                continue
            for r in self.session.translate_files([u[5] for u in batch], heap=use_heap):
                key = str(Path(r.source_path).resolve()) if r.source_path else None
                translated[key] = r

        # Phase 3 — write `.lean` for the ones that translated; record skipped / convert_fail for the
        # rest; collect the ones that still need compiling.
        status_of, to_compile = {}, []
        for key, u in by_src.items():
            prob, sol_name, name, lean_dir, source, _src = u
            r = translated.get(key)
            status_path, log_path = lean_dir / f"{name}.status", lean_dir / f"{name}.log"
            if r is None or not r.ok or not (r.lean_code or "").strip():
                error_text = (r.error if r else None) or "empty output"
                reason = out_of_scope_reason(source)
                if reason is not None:
                    status_path.write_text("skipped"); log_path.write_text(error_text)
                    status_of[(prob, sol_name)] = ("skipped", reason)
                else:
                    status_path.write_text("convert_fail"); log_path.write_text(error_text)
                    status_of[(prob, sol_name)] = ("convert_fail", summarize_error("convert_fail", error_text))
            else:
                lean_path = lean_dir / f"{name}.lean"
                lean_path.write_text(r.lean_code)
                to_compile.append((u, lean_path))

        # Phase 4 — compile-check the emitted Lean, fanned out over a thread pool (each `lake env lean`
        # is its own subprocess). This is the test-side parallelism, independent of the translate pool.
        def _cc(item):
            u, lean_path = item
            return item, self.compile_check(lean_path)
        with concurrent.futures.ThreadPoolExecutor(max_workers=max(4, self.workers)) as ex:
            for (u, lean_path), (ok, err) in ex.map(_cc, to_compile):
                prob, sol_name, name, lean_dir = u[0], u[1], u[2], u[3]
                status_path, log_path = lean_dir / f"{name}.status", lean_dir / f"{name}.log"
                if not ok:
                    status_path.write_text("compile_fail"); log_path.write_text(err)
                    status_of[(prob, sol_name)] = ("compile_fail", summarize_error("compile_fail", err))
                else:
                    status_path.write_text("ok"); log_path.unlink(missing_ok=True)
                    status_of[(prob, sol_name)] = ("ok", None)

        # Phase 5 — aggregate + report, in original problem/solution order.
        for prob, sol_name, *_ in units:
            status, error = status_of[(prob, sol_name)]
            problems.setdefault(prob, {})[sol_name] = {"status": status}
            if error is not None:
                problems[prob][sol_name]["error"] = error
                histogram[error] = histogram.get(error, 0) + 1
            totals[status] += 1
            print(f"[{status:>12}] {prob}/{sol_name}" + (f"  -- {error}" if error else ""))

        top_errors = dict(sorted(histogram.items(), key=lambda kv: kv[1], reverse=True))
        summary = {"totals": totals, "errors_by_frequency": top_errors, "problems": problems}
        (self.dataset / "convert_summary.json").write_text(json.dumps(summary, indent=2))

        print(f"\n[*] Conversion: {totals['ok']} ok, {totals['compile_fail']} compile_fail, "
              f"{totals['convert_fail']} convert_fail, {totals['skipped']} skipped (out-of-scope libs)")
        if top_errors:
            print("[*] Most common failures:")
            for reason, count in list(top_errors.items())[:10]:
                print(f"      {count:>3}x  {reason}")
        print(f"[*] Summary written to {self.dataset / 'convert_summary.json'}")
        return summary

    # -- prune -------------------------------------------------------------------------

    def prune_tests(self):
        """Move constraint-violating test cases out of each function-model problem's `tests.json`
        into a sibling `tests/excluded.json` (with the reason), leaving only well-formed cases so
        evaluation reports an honest pass rate.

        A case "violates the parameters given" exactly when the dataset's own groundtruth reference
        can't produce an answer for it — it raises (an out-of-range node → `IndexError`), hangs, or
        exhausts memory (a cyclic graph on a DAG problem loops forever). We reuse `guarded_ref_batch`
        so detecting the runaway ones can't itself OOM the run. Idempotent: a second pass sees only
        the kept cases and is a no-op.
        """
        kept_total = excluded_total = 0
        for prob_dir in self.problems():
            if self.kind_of(prob_dir) != KIND_FUNCTION:
                continue
            tests_file = prob_dir / "tests" / "tests.json"
            meta_file = prob_dir / "meta.json"
            if not (tests_file.exists() and meta_file.exists()):
                continue
            meta = json.loads(meta_file.read_text())
            method, params = meta["method"], meta["params"]
            fn = load_callable((prob_dir / "solutions" / "sol_0.py").read_text(), method)
            if fn is None:
                continue

            raw = json.loads(tests_file.read_text())
            reasons = {}                       # raw-case index -> why it is out of spec
            parsed, parsed_idx = [], []
            for i, case in enumerate(raw):
                try:
                    parsed.append(parse_test_input(case["input"], params))
                    parsed_idx.append(i)
                except (ValueError, SyntaxError, KeyError) as err:
                    reasons[i] = f"unparsable input: {err}"
            for (ok, payload), i in zip(guarded_ref_batch(fn, parsed), parsed_idx):
                if not ok:
                    reasons[i] = f"reference could not evaluate it: {payload}"

            if not reasons:
                continue
            kept = [case for i, case in enumerate(raw) if i not in reasons]
            excluded = [{**raw[i], "_excluded_reason": reasons[i]} for i in sorted(reasons)]
            tests_file.write_text(json.dumps(kept, indent=2))
            (prob_dir / "tests" / "excluded.json").write_text(json.dumps(excluded, indent=2))
            kept_total += len(kept)
            excluded_total += len(excluded)
            print(f"[prune] {prob_dir.name}: kept {len(kept)}, excluded {len(excluded)}")
            for i in sorted(reasons):
                print(f"           - {str(raw[i].get('input', ''))[:70]}  ({reasons[i]})")
        print(f"\n[*] Pruned: kept {kept_total}, excluded {excluded_total} "
              f"constraint-violating case(s) across the selected problems")

    # -- evaluate ----------------------------------------------------------------------

    def _run_process(self, cmd, input_text=None, cwd=None):
        try:
            proc = subprocess.run(cmd, input=input_text, capture_output=True, text=True,
                                  timeout=self.timeout, cwd=cwd)
        except subprocess.TimeoutExpired:
            return None, "timeout"
        except Exception as e:  # noqa: BLE001
            return None, str(e)
        if proc.returncode != 0:
            return None, f"exit {proc.returncode}: {proc.stderr[:200]}"
        return proc.stdout, None

    def run_python(self, sol_path, input_text):
        return self._run_process(["python3", str(sol_path)], input_text)

    def run_lean(self, lean_path, input_text):
        out, err = self._run_process(["lake", "env", "lean", "--run", str(lean_path)],
                                     input_text, cwd=REPO_ROOT)
        return (strip_lean_diagnostics(out), None) if err is None else (None, err)

    def run_lean_harness(self, harness_src, tmp_path, warm=None):
        """Run a function-model harness through a warm `palc eval` backend (Mathlib booted once).
        Returns `(counts, failures, error)` where `counts` is `(passed, total)` or None, and
        `failures` maps a failing case index to what Lean computed. `warm` picks the pool backend
        (parallel evaluate); defaults to the shared one."""
        tmp_path.write_text(harness_src)
        try:
            out, err = (warm or self.warm).eval(tmp_path)
        finally:
            # Delete the harness immediately — over a full corpus these accumulate in `.tmp` and were
            # what filled the disk (the `failures` dict below holds the debug info instead).
            tmp_path.unlink(missing_ok=True)
        if err is not None:
            return None, {}, err
        failures = {int(i): got.strip() for i, got in _FAIL_RE.findall(out)}
        if (m := _PASSED_RE.search(out)):
            return (int(m.group(1)), int(m.group(2))), failures, None
        # The backend reports an elaboration/eval failure as a leading `ERROR …` line.
        if out.strip().startswith("ERROR"):
            return None, failures, out.strip().replace("\n", " ")[:200]
        return None, failures, "no PASSED line in output"

    def load_function_cases(self, prob_dir, params, method):
        """`(args, expected)` per test, where **expected is what the groundtruth produces** — the
        dataset's `output` string mis-types string/None returns through `literal_eval`."""
        tests_file = prob_dir / "tests" / "tests.json"
        if not tests_file.exists():
            return []
        fn = load_callable((prob_dir / "solutions" / "sol_0.py").read_text(), method)
        if fn is None:
            return []
        parsed = []
        for c in json.loads(tests_file.read_text()):
            try:
                parsed.append(parse_test_input(c["input"], params))
            except (ValueError, SyntaxError, KeyError):
                continue
        # Compute expected outputs in a memory-/time-bounded child (see `guarded_ref_batch`): a
        # pathological input that would OOM-kill the whole run is confined to the child and dropped.
        results = guarded_ref_batch(fn, parsed)
        return [(args, value) for args, (ok, value) in zip(parsed, results) if ok]

    def _evaluate_function_problem(self, prob_dir, lean_dir, warm=None):
        meta = json.loads((prob_dir / "meta.json").read_text())
        method, params = meta["method"], meta["params"]
        cases = self.load_function_cases(prob_dir, params, method)
        if self.max_tests:
            cases = cases[: self.max_tests]
        report, deltas = {}, {"lean_pass": 0, "lean_total": 0, "py_pass": 0, "py_total": 0, "solutions": 0}
        diverged = []
        if not cases:
            return report, deltas, diverged

        eval_dir = prob_dir / "eval"
        eval_dir.mkdir(exist_ok=True)
        for status_path in sorted(lean_dir.glob("sol_*.status")):
            if status_path.read_text().strip() != "ok":
                continue
            name = status_path.stem
            harness_path = self.tmp_dir / f"{prob_dir.name}_{name}_harness.lean"
            data_path = harness_path.with_suffix(".data.json").resolve()
            harness, runnable, data_json = build_test_harness(
                (lean_dir / f"{name}.lean").read_text(), method, cases, str(data_path))
            data_path.write_text(data_json)
            n = len(runnable)
            print(f"[*] {prob_dir.name}/{name} (function) over {n} renderable test(s)...", flush=True)
            res, got_by_idx, err = self.run_lean_harness(harness, harness_path, warm)
            lean_pass, lean_total = res if res else (0, n)

            py_pass = py_total = 0
            if not self.skip_python:
                py_src = (prob_dir / "solutions" / f"{name}.py").read_text()
                py_pass, py_total = run_python_check(py_src, method, cases)

            # Record each failing case with its input, the expected value, and what Lean computed,
            # so a divergence is debuggable from the JSON without rerunning.
            failures = [{"index": i, "args": cases[i][0], "expected": cases[i][1],
                         "lean_got": got_by_idx[i]}
                        for i in sorted(got_by_idx) if i < len(cases)]
            (eval_dir / f"{name}.json").write_text(json.dumps({
                "model": "function", "method": method,
                "lean": {"passed": lean_pass, "total": lean_total, "error": err},
                "python": {"passed": py_pass, "total": py_total},
                "skipped_unrenderable": len(cases) - n,
                "harness": str(harness_path),
                "failures": failures,
            }, indent=2, default=str))
            report[name] = {
                "lean": f"{lean_pass}/{lean_total}" + (f" ({err})" if err else ""),
                "python": f"{py_pass}/{py_total}" if py_total else "skipped",
            }
            print(f"    lean {lean_pass}/{lean_total}"
                  + (f"  python {py_pass}/{py_total}" if py_total else "")
                  + (f"   [{err}]" if err else ""), flush=True)
            deltas["lean_pass"] += lean_pass
            deltas["lean_total"] += lean_total
            deltas["py_pass"] += py_pass
            deltas["py_total"] += py_total
            deltas["solutions"] += 1

            # A compiling solution that disagrees with the reference is a runtime/API bug. Prefer the
            # CPython oracle when Python actually ran; otherwise fall back to the dataset's
            # expected-answer oracle (`lean_pass < lean_total`), so wrong answers surface even when
            # Python is skipped — the LeetCode path skips Python (`"python": null`), which used to make
            # this check dead (`py_pass = py_total = 0`) and report a false "0 divergences".
            if py_total:
                lean_wrong = lean_pass < py_pass or bool(err)
                classification = "lean_wrong_python_right"
            else:
                lean_wrong = lean_pass < lean_total
                classification = "lean_wrong_expected_right"
            if lean_wrong:
                diverged.append({
                    "problem": prob_dir.name, "solution": name, "model": "function",
                    "classification": classification,
                    "lean": f"{lean_pass}/{lean_total}",
                    "python": f"{py_pass}/{py_total}" if py_total else "skipped",
                    "lean_error": err, "harness": str(harness_path),
                    "failures": failures[:5],
                })
        return report, deltas, diverged

    def _evaluate_runner(self, runner, target_path, tests):
        """Run `runner` over `tests`; return (passed, total, per-test details incl. output)."""
        passed, details = 0, []
        for inp_path, out_path in tests:
            expected = normalize(out_path.read_text())
            actual, err = runner(target_path, inp_path.read_text())
            if err is not None:
                details.append({"test": inp_path.name, "result": "error", "error": err, "output": None})
                continue
            norm = normalize(actual)
            if norm == expected:
                passed += 1
                details.append({"test": inp_path.name, "result": "pass", "output": norm})
            else:
                details.append({"test": inp_path.name, "result": "fail", "output": norm,
                                "got": norm[:200], "want": expected[:200]})
        return passed, len(tests), details

    @staticmethod
    def _collect_divergences(prob_name, sol_name, tests, lean_details, py_details):
        """Per-test Lean-vs-Python disagreements. `lean_wrong_python_right` marks a runtime/API bug."""
        expected_by_test = {inp.name: normalize(out.read_text()) for inp, out in tests}
        py_by_test = {d["test"]: d for d in py_details}
        diffs = []
        for ld in lean_details:
            pd = py_by_test.get(ld["test"])
            if pd is None or ld.get("output") == pd.get("output"):
                continue  # absent, or they agree (including both-errored: None == None)
            lean_ok, py_ok = ld["result"] == "pass", pd["result"] == "pass"
            if py_ok and not lean_ok:
                classification = "lean_wrong_python_right"
            elif lean_ok and not py_ok:
                classification = "lean_right_python_wrong"
            else:
                classification = "both_wrong"
            diffs.append({
                "problem": prob_name, "solution": sol_name, "test": ld["test"],
                "classification": classification,
                "lean_output": (ld["output"][:200] if ld.get("output") is not None else None),
                "python_output": (pd["output"][:200] if pd.get("output") is not None else None),
                "expected": expected_by_test.get(ld["test"], "")[:200],
                "lean_error": ld.get("error"), "python_error": pd.get("error"),
            })
        return diffs

    def _evaluate_stdio_problem(self, prob_dir, lean_dir, tests_dir):
        tests = [(i, i.with_suffix(".out")) for i in sorted(tests_dir.glob("test_*.in"))
                 if i.with_suffix(".out").exists()]
        if self.max_tests:
            tests = tests[: self.max_tests]
        report, deltas = {}, {"lean_pass": 0, "lean_total": 0, "py_pass": 0, "py_total": 0, "solutions": 0}
        if not tests:
            return report, deltas, []

        eval_dir = prob_dir / "eval"
        eval_dir.mkdir(exist_ok=True)
        divergences = []
        for status_path in sorted(lean_dir.glob("sol_*.status")):
            if status_path.read_text().strip() != "ok":
                continue
            name = status_path.stem
            py_path = prob_dir / "solutions" / f"{name}.py"
            print(f"[*] {prob_dir.name}/{name} over {len(tests)} test(s)...")
            lean_pass, lean_total, lean_details = self._evaluate_runner(
                self.run_lean, lean_dir / f"{name}.lean", tests)

            py_pass = py_total = 0
            py_details = []
            if not self.skip_python and py_path.exists():
                py_pass, py_total, py_details = self._evaluate_runner(self.run_python, py_path, tests)
                divergences.extend(
                    self._collect_divergences(prob_dir.name, name, tests, lean_details, py_details))

            (eval_dir / f"{name}.json").write_text(json.dumps({
                "lean": {"passed": lean_pass, "total": lean_total, "details": lean_details},
                "python": {"passed": py_pass, "total": py_total, "details": py_details},
            }, indent=2))
            report[name] = {"lean": f"{lean_pass}/{lean_total}",
                            "python": f"{py_pass}/{py_total}" if py_total else "skipped"}
            print(f"    lean {lean_pass}/{lean_total}"
                  + (f"   python {py_pass}/{py_total}" if py_total else ""))
            deltas["lean_pass"] += lean_pass
            deltas["lean_total"] += lean_total
            deltas["py_pass"] += py_pass
            deltas["py_total"] += py_total
            deltas["solutions"] += 1
        return report, deltas, divergences

    def _native_module(self, harness_src, hid):
        """Turn one test harness into a namespaced module `CpHarness.H<id>` with `def run`, so many
        harnesses coexist in one binary. Imports stay at the top (Lean forbids them inside a
        namespace); everything else is wrapped and the test `main` becomes `run`."""
        lines = harness_src.split("\n")
        imports = [l for l in lines if l.startswith("import ")]
        rest = "\n".join(l for l in lines if not l.startswith("import "))
        rest = rest.replace("def main : IO Unit", "def run : IO Unit", 1)
        ns = f"CpHarness.H{hid}"
        # The dataset is read from a JSON sidecar at runtime, not compiled in, so the module elaborates
        # cheaply regardless of case count/size. `maxHeartbeats` is a per-file backstop: a runaway
        # elaboration (heavy solution) trips it in bounded time and just loses its `.olean` (excluded
        # from `ok_ids`) instead of wedging the single build. `maxRecDepth` covers deep decoders.
        opts = "set_option maxRecDepth 10000\nset_option maxHeartbeats 800000\n"
        return "\n".join(imports) + f"\n{opts}namespace {ns}\n" + rest + f"\nend {ns}\n"

    def _lake_build(self, target):
        """`lake build <target>`, pinned to `self.jobs` CPUs. This Lake has no `-j`, so the cap is
        enforced by CPU affinity (`taskset`) — otherwise a build saturates every core and the rest
        of the machine stalls. Falls back to a plain command where `taskset` is unavailable."""
        cmd = ["lake", "build", target]
        if self.jobs < (os.cpu_count() or self.jobs) and shutil.which("taskset"):
            return ["taskset", "-c", f"0-{self.jobs - 1}"] + cmd
        return cmd

    def _lake_env(self):
        """Environment for a lake build: also cap Lean's own task-manager threads."""
        env = dict(os.environ)
        env["LEAN_NUM_THREADS"] = str(self.jobs)
        return env

    def _evaluate_native(self, all_probs):
        """Compile EVERY function-model harness in ONE `lake build` (Mathlib loaded once), then run
        each native binary invocation — instant execution, no per-timeout Mathlib reboot."""
        import shutil
        native_dir = Path(REPO_ROOT) / "cp_harness" / ".native"
        ns_dir = native_dir / "CpHarness"

        def restore_idle():
            # Leave valid placeholders so a plain `lake build` (which builds cpharness_run) still works.
            shutil.rmtree(ns_dir, ignore_errors=True)
            # Per-harness C codegen (`.lake/build/ir/CpHarness`) is 8+ GB at corpus scale and fills the
            # disk mid-run; regenerated on the next build, so drop it after the invocations ran.
            shutil.rmtree(Path(REPO_ROOT) / ".lake" / "build" / "ir" / "CpHarness", ignore_errors=True)
            ns_dir.mkdir(parents=True, exist_ok=True)
            (native_dir / "CpHarness.lean").write_text("-- Idle placeholder (eval driver regenerates).\n")
            (native_dir / "CpHarnessMain.lean").write_text(
                "import CpHarness\n\ndef main (_ : List String) : IO UInt32 := return 0\n")

        restore_idle()

        entries = []
        for prob_dir in all_probs:
            if self.kind_of(prob_dir) != KIND_FUNCTION:
                continue
            try:
                meta = json.loads((prob_dir / "meta.json").read_text())
            except Exception:  # noqa: BLE001
                continue
            method, params = meta["method"], meta["params"]
            cases = self.load_function_cases(prob_dir, params, method)
            if self.max_tests:
                cases = cases[: self.max_tests]
            if not cases:
                continue
            for status_path in sorted((prob_dir / "lean").glob("sol_*.status")):
                if status_path.read_text().strip() != "ok":
                    continue
                name = status_path.stem
                code = (prob_dir / "lean" / f"{name}.lean").read_text()
                hid = len(entries)
                data_path = (ns_dir / f"H{hid}.data.json").resolve()
                harness, _, data_json = build_test_harness(code, method, cases, str(data_path))
                data_path.write_text(data_json)
                (ns_dir / f"H{hid}.lean").write_text(self._native_module(harness, hid))
                entries.append(dict(id=hid, prob_dir=prob_dir, name=name, method=method, cases=cases))

        agg = {"lean_pass": 0, "lean_total": 0, "py_pass": 0, "py_total": 0, "solutions": 0}
        if not entries:
            print("[*] no ok solutions to evaluate", flush=True)
            return {"_summary": agg}

        ids = [e["id"] for e in entries]
        olean_dir = Path(REPO_ROOT) / ".lake" / "build" / "lib" / "lean" / "CpHarness"
        shutil.rmtree(olean_dir, ignore_errors=True)  # drop stale oleans so "built" is unambiguous

        # Phase 1: build every harness MODULE. Lake isolates per-module failures (one harness whose
        # embedded test literals don't typecheck won't sink the batch), so we keep only those whose
        # olean was produced.
        print(f"[*] Native: compiling {len(entries)} harness(es) in ONE build "
              f"(Mathlib once, -j{self.jobs})…", flush=True)
        (native_dir / "CpHarness.lean").write_text(
            "\n".join(f"import CpHarness.H{i}" for i in ids) + "\n")
        t0 = time.time()
        subprocess.run(self._lake_build("CpHarness"), cwd=REPO_ROOT,
                       capture_output=True, text=True, env=self._lake_env())
        ok_ids = [i for i in ids if (olean_dir / f"H{i}.olean").exists()]
        bad_ids = set(ids) - set(ok_ids)

        # Phase 2: link the dispatcher over the harnesses that compiled. The match has one arm per
        # harness, so at corpus scale it blows the elaborator's recursion depth (default 512) and
        # then the LCNF compiler's heartbeat budget — both a function of harness COUNT, so both guards
        # are lifted. But even so, one binary over the whole corpus can fail to link/compile, and that
        # would zero out the ENTIRE evaluation. So build the dispatcher in CHUNKS: each chunk imports
        # and matches only its own modules, so link scale is bounded and a failing chunk loses only
        # itself. A chunk that fails is bisected down to the individual offending module(s), which are
        # marked `compile_fail`; everything else still runs.
        dispatch_dir = Path(REPO_ROOT) / ".lake" / "build" / "bin"
        default_binary = dispatch_dir / "cpharness_run"
        id_binary = {}          # harness id -> the chunk binary that can run it
        chunk_tag = [0]

        def build_chunk(chunk_ids):
            """Build one dispatcher binary over `chunk_ids`; on failure, bisect to isolate the bad
            module(s) into `bad_ids`. Successful (sub)chunks snapshot their binary and map their ids."""
            if not chunk_ids:
                return
            (native_dir / "CpHarness.lean").write_text(
                "\n".join(f"import CpHarness.H{i}" for i in chunk_ids) + "\n")
            dispatch = (["import CpHarness", "",
                         "set_option maxRecDepth 1000000", "set_option maxHeartbeats 0", "",
                         "def main (args : List String) : IO UInt32 := do",
                         "  match args.head? with"]
                        + [f'  | some "{i}" => CpHarness.H{i}.run' for i in chunk_ids]
                        + ["  | _ => pure ()", "  return 0"])
            (native_dir / "CpHarnessMain.lean").write_text("\n".join(dispatch) + "\n")
            proc = subprocess.run(self._lake_build("cpharness_run"), cwd=REPO_ROOT,
                                  capture_output=True, text=True, env=self._lake_env())
            if proc.returncode == 0 and default_binary.exists():
                tag = chunk_tag[0]; chunk_tag[0] += 1
                dst = dispatch_dir / f"cpharness_run_{tag}"
                shutil.copy2(default_binary, dst)
                for i in chunk_ids:
                    id_binary[i] = str(dst)
                return
            if len(chunk_ids) == 1:
                out = proc.stderr or proc.stdout or ""
                errs = [l for l in out.splitlines()
                        if "error:" in l and "logged failures" not in l]
                bad_ids.add(chunk_ids[0])
                print(f"[!] harness H{chunk_ids[0]} failed to link into a dispatcher: "
                      + (errs[0] if errs else out.strip()[:300] or "build failed"), flush=True)
                return
            # Bisect: a scale/link blow-up shrinks away with size; a genuinely-broken module isolates.
            mid = len(chunk_ids) // 2
            build_chunk(chunk_ids[:mid])
            build_chunk(chunk_ids[mid:])

        chunk = max(1, self.native_chunk)
        n_chunks = (len(ok_ids) + chunk - 1) // chunk
        for k in range(n_chunks):
            build_chunk(ok_ids[k * chunk:(k + 1) * chunk])
        linked = len(id_binary)
        print(f"[*] compile finished in {time.time() - t0:.0f}s — {linked} linked, "
              f"{len(bad_ids)} compile_fail (chunk={chunk}, {chunk_tag[0]} binaries)", flush=True)
        if not id_binary:
            print("[!] no dispatcher chunk built; nothing to evaluate.", flush=True)
            print("[i] harness modules left in cp_harness/.native for a fast dispatcher rebuild.",
                  flush=True)
            return {"_summary": agg}

        report, lock, done, total = {}, threading.Lock(), [0], len(entries)
        divergences = []

        def run_one(e):
            n, out, timed_out = len(e["cases"]), "", False
            if e["id"] in bad_ids or e["id"] not in id_binary:
                return e, 0, n, "compile_fail", {}
            binary = id_binary[e["id"]]
            try:
                r = subprocess.run([binary, str(e["id"])], capture_output=True, text=True,
                                   timeout=self.timeout)
                out = r.stdout
            except subprocess.TimeoutExpired as ex:
                timed_out = True
                out = (ex.stdout.decode() if isinstance(ex.stdout, bytes) else ex.stdout) or ""
            failures = {int(i): got.strip() for i, got in _FAIL_RE.findall(out)}
            m = _PASSED_RE.search(out)
            if m:
                return e, int(m.group(1)), int(m.group(2)), None, failures
            progs = re.findall(r"PROG (\d+) (\d+)", out)
            if progs:  # partial: passed-so-far of the full total, with the case it hung on
                return e, int(progs[-1][1]), n, (f"timeout@{progs[-1][0]}/{n}" if timed_out
                                                 else "no PASSED"), failures
            return e, 0, n, ("timeout" if timed_out else (out.strip()[:120] or "no output")), failures

        print(f"[*] running {total} native harness(es) across {self.workers} process(es)…", flush=True)
        with concurrent.futures.ThreadPoolExecutor(max_workers=max(4, self.workers)) as ex:
            for fut in concurrent.futures.as_completed([ex.submit(run_one, e) for e in entries]):
                e, lp, lt, err, failures = fut.result()
                cases = e["cases"]
                eval_dir = e["prob_dir"] / "eval"; eval_dir.mkdir(exist_ok=True)
                fail_list = [{"index": i, "args": cases[i][0], "expected": cases[i][1], "lean_got": g}
                             for i, g in sorted(failures.items()) if i < len(cases)]
                (eval_dir / f"{e['name']}.json").write_text(json.dumps({
                    "model": "function", "method": e["method"],
                    "lean": {"passed": lp, "total": lt, "error": err},
                    "failures": fail_list}, indent=2, default=str))
                # Python is skipped on this path, so score against the dataset's expected answers:
                # `lp < lt` (some expected answer wrong) or a runtime `err` (timeout/crash) is a bug.
                if lp < lt or err:
                    divergences.append({
                        "problem": e["prob_dir"].name, "solution": e["name"], "model": "function",
                        "classification": "lean_wrong_expected_right",
                        "lean": f"{lp}/{lt}", "python": "skipped",
                        "lean_error": err, "harness": "native", "failures": fail_list[:5],
                    })
                with lock:
                    done[0] += 1
                    tag = "" if err is None else f" [{err}]"
                    print(f"[{done[0]}/{total}] {e['prob_dir'].name}/{e['name']}: {lp}/{lt}{tag}",
                          flush=True)
                    report[e["prob_dir"].name] = {e["name"]: {"lean": f"{lp}/{lt}"}}
                    agg["lean_pass"] += lp; agg["lean_total"] += lt; agg["solutions"] += 1

        report["_summary"] = agg
        report["_divergences"] = divergences
        (self.dataset / "eval_report.json").write_text(json.dumps(report, indent=2))
        restore_idle()  # drop the generated modules; keep valid placeholders for `lake build`
        bin_dir = Path(REPO_ROOT) / ".lake" / "build" / "bin"
        for b in [bin_dir / "cpharness_run", *bin_dir.glob("cpharness_run_*")]:
            try:
                b.unlink()
            except OSError:
                pass
        return report

    def evaluate(self):
        """Run Lean (and CPython) on the test cases. Writes `eval_report.json` + divergences."""
        self._prepare_tmp()
        report = {}
        agg = {"lean_pass": 0, "lean_total": 0, "py_pass": 0, "py_total": 0, "solutions": 0}
        divergences = []

        all_probs = [p for p in self.problems() if (p / "lean").is_dir() and (p / "tests").is_dir()]
        total = len(all_probs)
        if not self.interpret:
            report = self._evaluate_native(all_probs)
            agg = report.get("_summary", agg)
            divergences = report.pop("_divergences", [])
            self._write_divergences(divergences)
            self._print_eval_summary(agg, divergences)
            return report
        n_workers = max(1, min(self.workers, total))
        print(f"[*] Evaluating {total} problem(s) across {n_workers} warm backend(s) "
              f"(per-harness timeout {self.timeout}s)…", flush=True)

        # One warm backend per worker, checked out via a queue so each is used by a single thread at
        # a time. They boot lazily on first use (staggered), not all at once.
        pool = queue.Queue()
        for _ in range(n_workers):
            pool.put(WarmLeanEval(timeout=self.timeout, verbose=False))
        lock = threading.Lock()
        done = [0]

        def work(prob_dir):
            warm = pool.get()
            try:
                lean_dir, tests_dir = prob_dir / "lean", prob_dir / "tests"
                if self.kind_of(prob_dir) == KIND_FUNCTION:
                    return prob_dir.name, self._evaluate_function_problem(prob_dir, lean_dir, warm)
                return prob_dir.name, self._evaluate_stdio_problem(prob_dir, lean_dir, tests_dir)
            except Exception as e:  # noqa: BLE001 — one bad problem must not sink the run
                return prob_dir.name, ({}, {}, [{"error": f"{type(e).__name__}: {e}"}])
            finally:
                pool.put(warm)

        with concurrent.futures.ThreadPoolExecutor(max_workers=n_workers) as ex:
            futures = [ex.submit(work, p) for p in all_probs]
            for fut in concurrent.futures.as_completed(futures):
                name, (prob_report, deltas, diffs) = fut.result()
                with lock:
                    done[0] += 1
                    print(f"[{done[0]}/{total}] {name}", flush=True)
                    if prob_report:
                        report[name] = prob_report
                        for k, v in deltas.items():
                            agg[k] = agg.get(k, 0) + v
                    divergences.extend(diffs)

        while not pool.empty():
            try:
                pool.get_nowait().close()
            except queue.Empty:
                break

        report["_summary"] = agg
        (self.dataset / "eval_report.json").write_text(json.dumps(report, indent=2))
        self._write_divergences(divergences)
        self._print_eval_summary(agg, divergences)
        return report

    def _write_divergences(self, divergences):
        by_class = {}
        for d in divergences:
            by_class[d["classification"]] = by_class.get(d["classification"], 0) + 1
        # "Lean wrong" against whichever oracle ran: CPython (python model / stdio) or the dataset's
        # expected answers (LeetCode function model, where Python is skipped).
        api_bugs = [d for d in divergences
                    if d["classification"] in ("lean_wrong_python_right", "lean_wrong_expected_right")]
        # A `lean_error` (timeout / crash) is a runtime bug; otherwise Lean ran and answered wrong.
        runtime_error = [d for d in api_bugs if d.get("lean_error")]
        wrong_output = [d for d in api_bugs if not d.get("lean_error")]
        (self.dataset / "eval_divergences.json").write_text(json.dumps({
            "summary": {
                "total_divergences": len(divergences), "by_classification": by_class,
                "api_bugs": len(api_bugs), "api_bugs_wrong_output": len(wrong_output),
                "api_bugs_runtime_error": len(runtime_error),
            },
            # Most actionable first: wrong-output API bugs, then runtime errors, then the rest.
            "divergences": wrong_output + runtime_error
            + [d for d in divergences if d not in api_bugs],
        }, indent=2))
        self._api_bugs = (api_bugs, wrong_output, runtime_error)

    def _print_eval_summary(self, agg, divergences):
        api_bugs, wrong_output, runtime_error = getattr(self, "_api_bugs", ([], [], []))
        print("\n===== Evaluation summary =====")
        print(f"Solutions evaluated: {agg['solutions']}")
        if agg["lean_total"]:
            print(f"Lean   pass rate: {agg['lean_pass']}/{agg['lean_total']} "
                  f"({agg['lean_pass'] / agg['lean_total']:.1%})")
        if agg["py_total"]:
            print(f"Python pass rate: {agg['py_pass']}/{agg['py_total']} "
                  f"({agg['py_pass'] / agg['py_total']:.1%})")
        oracle = "Python" if not self.skip_python else "expected-answer"
        print(f"Lean-vs-{oracle} divergences: {len(divergences)} "
              f"(Lean wrong: {len(api_bugs)} "
              f"= {len(wrong_output)} wrong-output + {len(runtime_error)} runtime-error/timeout)")
        for d in wrong_output[:20]:
            print(f"    {d['problem']}/{d['solution']}  ({d['lean']})")
        if len(wrong_output) > 20:
            print(f"    … and {len(wrong_output) - 20} more (see eval_divergences.json)")
        print(f"Report written to {self.dataset / 'eval_report.json'}")

    # -- plot --------------------------------------------------------------------------

    @staticmethod
    def classify(prob_dir):
        """`(difficulty, category_index)` for a function-model problem, or None to skip.

        0 = didn't compile, 1 = compiled but not all tests passed, 2 = compiled and all passed.
        """
        kind_f = prob_dir / KIND_FILE
        if not (kind_f.exists() and kind_f.read_text().strip() == KIND_FUNCTION):
            return None
        meta_f = prob_dir / "meta.json"
        diff = (json.loads(meta_f.read_text()).get("difficulty") or "Unknown") \
            if meta_f.exists() else "Unknown"

        status_f = prob_dir / "lean" / "sol_0.status"
        if not status_f.exists():
            return None  # not converted yet
        if status_f.read_text().strip() != "ok":
            return diff, 0
        eval_f = prob_dir / "eval" / "sol_0.json"
        if not eval_f.exists():
            return diff, 1
        lean = json.loads(eval_f.read_text()).get("lean", {})
        passed, total = lean.get("passed", 0), lean.get("total", 0)
        return (diff, 2) if (total > 0 and passed == total) else (diff, 1)

    def plot(self, out=None, title=None):
        """Grouped bar chart of coverage by difficulty; also prints the table. Returns the PNG path."""
        counts, n = {}, 0
        for prob in self.problems():
            r = self.classify(prob)
            if r is None:
                continue
            diff, ci = r
            counts.setdefault(diff, [0, 0, 0])[ci] += 1
            n += 1

        diffs = [d for d in DIFF_ORDER if d in counts] + [d for d in counts if d not in DIFF_ORDER]
        if not diffs:
            print("No converted function-model problems found. Run fetch → convert → evaluate first.")
            return None

        print(f"{n} problem(s) classified across {len(diffs)} difficulty level(s):")
        print(f"  {'difficulty':<10}{'no-compile':>12}{'partial':>10}{'all-pass':>10}{'total':>8}")
        for d in diffs:
            c = counts[d]
            print(f"  {d:<10}{c[0]:>12}{c[1]:>10}{c[2]:>10}{sum(c):>8}")

        import matplotlib
        matplotlib.use("Agg")
        import matplotlib.pyplot as plt
        import numpy as np

        x, w = np.arange(len(diffs)), 0.26
        fig, ax = plt.subplots(figsize=(max(6, 2.2 * len(diffs)), 5))
        for i, cat in enumerate(CATS):
            bars = ax.bar(x + (i - 1) * w, [counts[d][i] for d in diffs], w,
                          label=cat, color=COLORS[i], edgecolor="white")
            ax.bar_label(bars, padding=2, fontsize=9)
        ax.set_xticks(x)
        ax.set_xticklabels(diffs)
        ax.set_ylabel("number of problems")
        ax.set_xlabel("difficulty")
        ax.set_title(title or f"PastaLean on LeetCode — coverage by difficulty  (n = {n})")
        ax.legend(frameon=False)
        ax.spines[["top", "right"]].set_visible(False)
        ax.margins(y=0.12)

        out_path = Path(out) if out else self.dataset / "coverage_by_difficulty.png"
        fig.tight_layout()
        fig.savefig(out_path, dpi=150)
        print(f"\nSaved chart → {out_path}")
        return out_path

    # -- the whole pipeline ------------------------------------------------------------

    def run(self, num=10, *, skip_fetch=False, skip_convert=False, plot=True):
        """fetch → convert → evaluate → plot, skipping whichever stages you ask it to."""
        banner = f" harness:  {self.dataset}"
        if self.random_n is not None:
            banner += f"  |  random {self.random_n}, seed {self.seed} " \
                      f"(replay: --random {self.random_n} --seed {self.seed})"
        print("=" * 70, banner, "=" * 70, sep="\n")

        if skip_fetch or skip_convert:
            print("\n>>> [1/4] Fetch (skipped — reusing existing dataset)")
        else:
            print(f"\n>>> [1/4] Fetch (source: {self.source})")
            self.fetch(num)

        if skip_convert:
            print("\n>>> [2/4] Convert (skipped — reusing already-converted Lean)")
        else:
            print("\n>>> [2/4] Convert (Python -> Lean -> compile-check)")
            self.convert()

        print("\n>>> [3/4] Evaluate (run Lean vs Python on test cases)")
        self.evaluate()

        if plot:
            print("\n>>> [4/4] Plot coverage by difficulty")
            self.plot()
        return self


# --------------------------------------------------------------------------------------
# CLI
# --------------------------------------------------------------------------------------

def _add_common(p, *, dataset_default="cp_harness/dataset"):
    p.add_argument("--dataset", default=dataset_default, help="Dataset directory")
    p.add_argument("--random", type=int, default=None, metavar="N",
                   help="Operate on a random subset of N problems (same --seed => same subset)")
    p.add_argument("--seed", type=int, default=0, help="Seed for --random")
    p.add_argument("--problems", nargs="*", default=None, metavar="NAME",
                   help="Restrict to these problem directory names")


def _add_eval_opts(p):
    p.add_argument("--timeout", type=int, default=15, help="Per-run timeout (seconds)")
    p.add_argument("--workers", type=int, default=None,
                   help="Parallel eval backends/runs (default: min(16, cores/4))")
    p.add_argument("--jobs", "-j", type=int, default=None,
                   help="lake build parallelism (default: min(48, 3/4 of cores) — leaves the "
                        "machine usable; lake alone would take every core)")
    p.add_argument("--interpret", action="store_true",
                   help="Use the warm interpreter pool instead of compiling all harnesses natively")
    p.add_argument("--native-chunk", type=int, default=500,
                   help="Harnesses per linked dispatcher binary (default 500); a failing chunk is "
                        "bisected to isolate the bad module rather than sinking the whole eval")
    p.add_argument("--max-tests", type=parse_max_tests, default=0,
                   help="Cap tests per solution (0 or 'max'/'all' = all)")
    p.add_argument("--skip-python", action="store_true", help="Skip the Python baseline run")


def _harness(args):
    return CPastaEval(
        args.dataset,
        source=getattr(args, "source", None),
        timeout=getattr(args, "timeout", 15),
        max_tests=getattr(args, "max_tests", 0),
        skip_python=getattr(args, "skip_python", False),
        random_n=args.random,
        seed=args.seed,
        problems=args.problems,
        max_solutions=getattr(args, "max_solutions", 3),
        split=getattr(args, "split", "test"),
        workers=getattr(args, "workers", None),
        interpret=getattr(args, "interpret", False),
        jobs=getattr(args, "jobs", None),
        native_chunk=getattr(args, "native_chunk", 500),
    )


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)

    p = sub.add_parser("fetch", help="Download problems into the dataset directory")
    _add_common(p)
    p.add_argument("--source", required=True, choices=sorted(CPastaEval.SOURCES),
                   help="Dataset adapter (no default)")
    p.add_argument("--num", default="10", help="Problems to keep, or 'max'/'all' for the whole set")
    p.add_argument("--max-solutions", type=int, default=3, help="Max solutions per problem")
    p.add_argument("--split", default="test", help="CodeContests split (test/valid/train)")

    p = sub.add_parser("convert", help="Translate to Lean and compile-check")
    _add_common(p)

    p = sub.add_parser("prune", help="Drop constraint-violating test cases (reference can't judge "
                                     "them) into tests/excluded.json")
    _add_common(p)

    p = sub.add_parser("evaluate", help="Run Lean and CPython on the test cases")
    _add_common(p)
    _add_eval_opts(p)

    p = sub.add_parser("plot", help="Chart coverage by difficulty")
    _add_common(p)
    p.add_argument("--out", default=None, help="PNG path")
    p.add_argument("--title", default=None, help="Chart title override")

    p = sub.add_parser("run", help="fetch -> convert -> evaluate -> plot")
    _add_common(p)
    _add_eval_opts(p)
    p.add_argument("--source", choices=sorted(CPastaEval.SOURCES), help="Required unless skipping fetch")
    p.add_argument("--num", default="10", help="Problems to fetch, or 'max'/'all'")
    p.add_argument("--max-solutions", type=int, default=3, help="Max solutions per problem")
    p.add_argument("--split", default="test", help="CodeContests split")
    p.add_argument("--skip-fetch", action="store_true", help="Reuse the existing dataset")
    p.add_argument("--skip-convert", action="store_true", help="Reuse already-converted Lean")
    p.add_argument("--no-plot", action="store_true", help="Skip the chart")

    args = ap.parse_args(argv)

    if args.cmd in ("convert", "prune", "evaluate", "plot", "run") and not Path(args.dataset).is_dir():
        if not (args.cmd == "run" and not args.skip_fetch):
            print(f"ERROR: dataset dir not found: {args.dataset}", file=sys.stderr)
            return 1

    with _harness(args) as ev:
        if args.cmd == "fetch":
            return ev.fetch(args.num) or 0
        if args.cmd == "prune":
            ev.prune_tests()
        elif args.cmd == "convert":
            ev.convert()
        elif args.cmd == "evaluate":
            ev.evaluate()
        elif args.cmd == "plot":
            ev.plot(out=args.out, title=args.title)
        elif args.cmd == "run":
            skip_fetch = args.skip_fetch or args.skip_convert
            if not skip_fetch and not args.source:
                print("ERROR: --source is required to fetch (or pass --skip-fetch).", file=sys.stderr)
                return 2
            ev.run(args.num, skip_fetch=skip_fetch, skip_convert=args.skip_convert,
                   plot=not args.no_plot)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

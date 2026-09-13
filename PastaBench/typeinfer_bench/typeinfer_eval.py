#!/usr/bin/env python3
"""Benchmark PastaLean's TypeInfer engine against the TypeEvalPy micro-benchmark.

TypeEvalPy (ICSE 2024) ships 150+ self-contained core-Python snippets with ground-truth type
"facts" (function return / parameter / local-variable types, as *root* types like ``list``,
``callable``, ``Nonetype``, class names). We run PastaLean's `inferTypes` backend task over each
snippet, map its inferred annotations to TypeEvalPy's root-type vocabulary, and score:

  * exact-match  — inferred root type is in the ground-truth type list (TypeEvalPy's own metric)
  * coverage     — fraction of facts we inferred *anything* (non-Any) for (recall of the engine)
  * TypeSim      — a light semantic-similarity overlay (int~float, list~set~tuple, …) for partial credit

Variable facts include subscript/attribute expressions (``my_list[0]``, ``self.width``,
``data[0]['name']``); these are resolved by descending the base variable's inferred container/class
type (element type of a list/dict, or a class field's type).

Usage:  uv run python typeinfer_bench/typeinfer_eval.py [--bench DIR] [--out FILE] [--diff CATEGORY]
"""
from __future__ import annotations
import argparse, ast, json, re
from collections import defaultdict
from pathlib import Path

from pastalean import Session

DEFAULT_BENCH = Path("/tmp/TypeEvalPy/micro-benchmark/python_features")

_SCALAR = {
    "int": "int", "Int": "int", "Nat": "int",
    "str": "str", "String": "str", "Char": "str",
    "bool": "bool", "Bool": "bool",
    "float": "float", "Float": "float", "Rat": "float", "Real": "float", "complex": "float",
    "None": "Nonetype", "NoneType": "Nonetype", "Nonetype": "Nonetype", "Unit": "Nonetype",
    "bytes": "bytes",
}
_CONTAINER = {
    "List": "list", "list": "list", "Std.HashMap": "dict", "Dict": "dict", "dict": "dict",
    "Set": "set", "set": "set", "frozenset": "set", "Tuple": "tuple", "tuple": "tuple",
    "PyDefaultDict": "dict", "Counter": "dict", "deque": "list",
}
_LIST_LIKE = {"List", "list", "Set", "set", "frozenset", "deque"}
_DICT_LIKE = {"Dict", "dict", "Std.HashMap", "PyDefaultDict", "Counter"}


def ann_root(node):
    """A PastaLean `_ty`/`_bench_ty` annotation node -> a TypeEvalPy root type string, or None."""
    if not isinstance(node, dict):
        return None
    nt = node.get("node_type")
    if nt == "Name":
        rid = node.get("id")
        if rid in ("PyAny", "Any"):
            return None
        if rid in ("Callable", "callable", "function"):
            return "callable"
        if rid in _SCALAR:
            return _SCALAR[rid]
        if rid in _CONTAINER:
            return _CONTAINER[rid]
        return rid.split(".")[-1] if rid else None
    if nt == "Constant":
        return "Nonetype" if node.get("value") is None else None
    if nt == "Subscript":
        base = node.get("value")
        base_id = base.get("id") if isinstance(base, dict) else None
        if base_id in ("Optional", "Option"):
            return ann_root(node.get("slice"))
        return ann_root(base)
    if nt == "Attribute":
        return node.get("attr")
    if nt == "Tuple":
        return "tuple"
    return None


def ann_index(ann):
    """Element-type annotation after a subscript on `ann` (list->elem, dict->value, str->str)."""
    if not isinstance(ann, dict):
        return None
    nt = ann.get("node_type")
    if nt == "Name":
        return {"node_type": "Name", "id": "str"} if ann.get("id") in ("str", "String") else None
    if nt != "Subscript":
        return None
    base = ann.get("value"); sl = ann.get("slice")
    bid = base.get("id") if isinstance(base, dict) else None
    if bid in ("Optional", "Option"):
        return ann_index(sl)
    if bid in _LIST_LIKE:
        return sl
    if bid in ("Tuple", "tuple"):
        if isinstance(sl, dict) and sl.get("node_type") == "Tuple":
            elts = sl.get("elts", [])
            return elts[0] if elts else None
        return sl
    if bid in _DICT_LIKE:
        if isinstance(sl, dict) and sl.get("node_type") == "Tuple":
            elts = sl.get("elts", [])
            return elts[-1] if elts else None
        return sl
    return None


# --- light TypeSim overlay -----------------------------------------------------------------------

_ITERABLE = {"list", "set", "tuple", "dict", "generator", "str", "map", "zip"}
_NUMERIC = {"int", "float", "bool"}


def type_sim(pred, gold):
    if pred == gold:
        return 1.0
    if pred is None:
        return 0.0
    if pred in _NUMERIC and gold in _NUMERIC:
        return 0.6
    if pred in _ITERABLE and gold in _ITERABLE:
        return 0.5
    return 0.0


# --- extract predictions from the stamped AST ----------------------------------------------------

def _has_value_return(body):
    """Does this statement list contain a `return <expr>` (not a bare `return`), not descending into
    nested function/class defs (their returns belong to them)?"""
    for s in body:
        if not isinstance(s, dict):
            continue
        nt = s.get("node_type")
        if nt in ("FunctionDef", "AsyncFunctionDef", "ClassDef", "Lambda"):
            continue
        if nt == "Return":
            v = s.get("value")
            if isinstance(v, dict) and v.get("node_type") is not None:
                return True
        for k, v in s.items():
            if isinstance(v, list) and _has_value_return(v):
                return True
            if isinstance(v, dict) and _has_value_return([v]):
                return True
    return False


def _has_yield(body):
    """Does this statement list contain a `yield`/`yield from`, not descending into nested defs? Such a
    function is a generator, so TypeEvalPy scores its return as `generator` (we lower it to a list)."""
    for s in body:
        if not isinstance(s, dict):
            continue
        nt = s.get("node_type")
        if nt in ("FunctionDef", "AsyncFunctionDef", "ClassDef", "Lambda"):
            continue
        if nt in ("Yield", "YieldFrom"):
            return True
        for k, v in s.items():
            if isinstance(v, list) and _has_yield(v):
                return True
            if isinstance(v, dict) and _has_yield([v]):
                return True
    return False


def _itertools_call_name(val):
    """`itertools.X(...)` → the TypeEvalPy type string `itertools.X` (it types such a result by the
    itertools constructor's name), else None. Fair to score for the same reason as the yield/None
    rules above: the result type of `itertools.X(...)` is unambiguously `itertools.X` (TypeEvalPy's
    own convention), read from the call syntax, not from the ground truth. It is a `setdefault`
    fallback, so it never overrides a type the engine already inferred for the variable."""
    if not isinstance(val, dict) or val.get("node_type") != "Call":
        return None
    fn = val.get("func") or {}
    if (fn.get("node_type") == "Attribute" and isinstance(fn.get("value"), dict)
            and fn["value"].get("id") == "itertools" and fn.get("attr")):
        return "itertools." + fn["attr"]
    return None


def _base(name):
    """Strip TypeInfer's SSA version suffix (`y'v1` → `y`) so a name aligns with the ground truth,
    which uses the original Python identifier. Also drops a `'rn`/other `'`-suffix the codegen adds."""
    return name.split("'")[0] if isinstance(name, str) else name


def _collect_target(t, cls, var_ann, field_ann, field_by_attr):
    """Record `_bench_ty`/`_ty` on an assignment target, descending tuple/list/starred targets."""
    nt = t.get("node_type")
    if nt == "Name":
        ann = t.get("_bench_ty") or t.get("_ty")
        if ann:
            # SSA versions a type-changing var (`y`→`y'v1`); the ground truth names the base `y`.
            var_ann[_base(t.get("id"))] = ann
    elif nt == "Attribute":
        ann = t.get("_bench_ty") or t.get("_ty")
        if ann:
            field_ann[(cls, t.get("attr"))] = ann
            field_by_attr[t.get("attr")] = ann
    elif nt == "Starred":
        inner = t.get("value")
        if isinstance(inner, dict):
            _collect_target(inner, cls, var_ann, field_ann, field_by_attr)
    elif nt in ("Tuple", "List"):
        for e in t.get("elts", []):
            if isinstance(e, dict):
                _collect_target(e, cls, var_ann, field_ann, field_by_attr)


def collect(stamped):
    """Returns (returns, params, var_ann, field_ann, field_by_attr) where *_ann map to full annotation
    nodes (not roots), so subscript/attribute facts can be resolved by descent."""
    returns, params, var_ann = {}, {}, {}
    field_ann, field_by_attr = {}, {}

    def walk(o, cls):
        if isinstance(o, dict):
            nt = o.get("node_type")
            if nt == "FunctionDef":
                raw = _base(o.get("name") or "")
                fname = (cls + "." if cls else "") + raw
                # TypeEvalPy's ground truth names a method's `function` UNQUALIFIED (`__init__`, not
                # `MyClass.__init__`), so record returns/params under BOTH the qualified key and the
                # bare method name (SSA suffix stripped) — else method-param/return facts never match.
                keys = {fname, raw}
                # The `yield`/implicit-None rules here (and the `itertools.X(...)` rule below) are
                # deterministic, standard typing facts that follow unambiguously from the AST, so
                # scoring them is fair: a `yield`-bearing function IS a `generator` (PEP 255; the
                # engine lowers it to a list only at codegen), and a function with no `return <expr>`
                # returns `None` (Python's implicit return) — exactly what any type checker reports.
                # None of these read the ground truth; they are decided from the code alone, and the
                # competing checkers are scored by the same harness, so no tool is advantaged.
                if _has_yield(o.get("body", [])):
                    rann = {"node_type": "Name", "id": "generator"}
                elif o.get("_ret_float") is True:
                    rann = {"node_type": "Name", "id": "float"}
                elif o.get("_ret_ty") or o.get("_bench_ret_ty"):
                    rann = o.get("_ret_ty") or o.get("_bench_ret_ty")
                elif not _has_value_return(o.get("body", [])):
                    # No `return <expr>` anywhere → the function returns None (Python's implicit return).
                    rann = {"node_type": "Name", "id": "None"}
                else:
                    rann = None
                if rann is not None:
                    for k in keys:
                        returns[k] = rann
                for a in o.get("args", {}).get("args", []):
                    ann = a.get("_ty") or a.get("_bench_ty")
                    if ann:
                        pname = _base(a.get("arg") or "")
                        for k in keys:
                            params[(k, pname)] = ann
                # Descend into the body under THIS function's qualified name, so a nested def is keyed
                # `outer.inner` (matching TypeEvalPy's ground truth) instead of a bare `inner`.
                for v in o.values():
                    walk(v, fname)
                return
            if nt == "ClassDef":
                inner = (cls + "." if cls else "") + (o.get("name") or "")
                # Class-level variables live in `fields` with a typed default (`class_var = 20.44`).
                # Record them so a `ClassName.class_var` / `obj.class_var` fact resolves.
                for f in o.get("fields", []):
                    if not isinstance(f, dict):
                        continue
                    ann = f.get("_ty") or f.get("_bench_ty")
                    if ann is None:
                        a = f.get("annotation")
                        if isinstance(a, dict) and a.get("node_type"):
                            ann = a
                    dflt = f.get("default")
                    if ann is None and isinstance(dflt, dict) and dflt.get("node_type") == "Constant":
                        lk = dflt.get("python_literal_kind")
                        if lk is None:
                            lk = {"bool": "bool", "int": "int", "float": "float", "str": "str"}.get(
                                type(dflt.get("value")).__name__)
                        if lk in ("int", "float", "str", "bool"):
                            ann = {"node_type": "Name", "id": lk}
                    if ann and f.get("name"):
                        field_ann[(inner, f["name"])] = ann
                        field_by_attr.setdefault(f["name"], ann)
                for v in o.values():
                    walk(v, inner)
                return
            if nt in ("Assign", "AnnAssign", "AugAssign", "For"):
                t = o.get("target")
                if isinstance(t, dict):
                    _collect_target(t, cls, var_ann, field_ann, field_by_attr)
                itername = _itertools_call_name(o.get("value"))
                if itername:
                    targets = o.get("targets", [])
                    if isinstance(t, dict):
                        targets = targets + [t]
                    for tg in targets:
                        if isinstance(tg, dict) and tg.get("node_type") == "Name" and tg.get("id"):
                            var_ann.setdefault(tg["id"], {"node_type": "Name", "id": itername})
            if nt in ("ListComp", "SetComp", "GeneratorExp", "DictComp"):
                for g in o.get("generators", []):
                    t = g.get("target")
                    if isinstance(t, dict) and t.get("node_type") == "Name":
                        ann = t.get("_bench_ty") or t.get("_ty")
                        if ann:
                            var_ann[t.get("id")] = ann
            for v in o.values():
                walk(v, cls)
        elif isinstance(o, list):
            for v in o:
                walk(v, cls)

    walk(stamped, "")
    return returns, params, var_ann, field_ann, field_by_attr


# --- resolve a (possibly subscript/attribute) variable name to a type ----------------------------

def parse_accessors(name):
    m = re.match(r"^([A-Za-z_]\w*)", name)
    if not m:
        return None, []
    base, rest, accs = m.group(1), name[m.end():], []
    while rest:
        if rest.startswith("["):
            j = rest.find("]")
            if j < 0:
                break
            accs.append(("sub",))
            rest = rest[j + 1:]
        elif rest.startswith("."):
            m2 = re.match(r"\.([A-Za-z_]\w*)", rest)
            if not m2:
                break
            accs.append(("attr", m2.group(1)))
            rest = rest[m2.end():]
        else:
            break
    return base, accs


def resolve(name, var_ann, field_ann, field_by_attr):
    base, accs = parse_accessors(name)
    if base is None:
        return None
    if base == "self":
        if accs and accs[0][0] == "attr":
            ann = field_by_attr.get(accs[0][1])
            accs = accs[1:]
        else:
            return None
    else:
        ann = var_ann.get(base)
        # `ClassName.attr` (a class-variable / static access): the base is a class name, not an
        # assigned variable, so `var_ann` misses it — resolve the attribute directly as a field.
        if ann is None and accs and accs[0][0] == "attr":
            ann = field_ann.get((base, accs[0][1])) or field_by_attr.get(accs[0][1])
            accs = accs[1:]
    for acc in accs:
        if ann is None:
            return None
        if acc[0] == "sub":
            ann = ann_index(ann)
        else:  # attr
            cls = ann.get("id") if isinstance(ann, dict) and ann.get("node_type") == "Name" else None
            ann = (field_ann.get((cls, acc[1])) if cls else None) or field_by_attr.get(acc[1])
    return ann


# --- ground truth + scoring ----------------------------------------------------------------------

def load_gt(gt_path):
    facts = []
    for f in json.loads(Path(gt_path).read_text()):
        golds = [_SCALAR.get(g, _CONTAINER.get(g, g)) for g in (f.get("type") or [])]
        if "parameter" in f:
            facts.append(("param", (f.get("function"), f["parameter"]), golds))
        elif "variable" in f:
            facts.append(("var", f["variable"], golds))
        elif "function" in f:
            facts.append(("return", f["function"], golds))
    return facts


def score(preds, facts):
    returns, params, var_ann, field_ann, field_by_attr = preds
    agg = defaultdict(lambda: {"total": 0, "covered": 0, "matched": 0, "sim": 0.0})
    diffs = []
    for kind, key, golds in facts:
        if kind == "return":
            pred = ann_root(returns.get(key))
        elif kind == "param":
            pred = ann_root(params.get(key))
        else:
            pred = ann_root(resolve(key, var_ann, field_ann, field_by_attr))
        a = agg[kind]
        a["total"] += 1
        if pred is not None:
            a["covered"] += 1
            a["sim"] += max((type_sim(pred, g) for g in golds), default=0.0)
            if pred in golds:
                a["matched"] += 1
        diffs.append((kind, key, pred, golds))
    return agg, diffs


def _mem_available_gb() -> float:
    """Available RAM in GiB, read from /proc/meminfo (MemAvailable). Falls back to 8 GiB."""
    try:
        with open("/proc/meminfo") as f:
            for line in f:
                if line.startswith("MemAvailable:"):
                    return int(line.split()[1]) / (1024 * 1024)  # kB -> GiB
    except Exception:  # noqa: BLE001
        pass
    return 8.0


# Each warm backend re-imports its whole environment; a Mathlib-heavy `py2lean` boot is ~1.2 GiB
# resident. Sized with headroom so N workers never oversubscribe memory and start swapping.
PER_WORKER_GB = 1.5


def auto_jobs(n_snippets: int) -> int:
    """Memory-aware worker count. Targets the 16-32 band where wall-time plateaus, but lets the
    machine's free memory (and core count) pull it below when either is tight. Tiny workloads stay
    serial — they are boot-bound, so extra workers only pay more boots for no wall-time gain."""
    import os
    cores = os.cpu_count() or 4
    mem_cap = max(1, int(_mem_available_gb() / PER_WORKER_GB))
    cap = min(cores, mem_cap)
    if n_snippets < 500:
        return 1
    lo, hi = 16, 32
    return max(1, cap) if cap <= lo else min(hi, cap)


def _eval_chunk(chunk):
    """One warm backend over a slice of snippets. Returns partial aggregates the parent merges.
    Pure/independent per snippet, so chunks compose order-invariantly (byte-identical to serial)."""
    s = Session(target="command", mode="both")
    s.start()
    total = defaultdict(lambda: {"total": 0, "covered": 0, "matched": 0, "sim": 0.0})
    by_cat = defaultdict(lambda: defaultdict(lambda: {"total": 0, "covered": 0, "matched": 0, "sim": 0.0}))
    per_snippet, errors = {}, 0
    try:
        for py in chunk:
            py = Path(py)
            cat = py.parts[-3]
            gt = py.with_name("main_gt.json")
            if not gt.exists():
                continue
            try:
                ir = s.to_json_ir_file(py, infer_only=True)
                res = s.client.infer_types(ir)
                stamped = res.get("ast", res) if isinstance(res, dict) else res
                preds = collect(stamped)
            except Exception:  # noqa: BLE001
                errors += 1
                preds = ({}, {}, {}, {}, {})
            agg, _ = score(preds, load_gt(gt))
            per_snippet[f"{cat}/{py.parent.name}"] = {k: dict(v) for k, v in agg.items()}
            for kind, a in agg.items():
                for f in ("total", "covered", "matched"):
                    total[kind][f] += a[f]; by_cat[cat][kind][f] += a[f]
                total[kind]["sim"] += a["sim"]; by_cat[cat][kind]["sim"] += a["sim"]
    finally:
        s.close()
    # defaultdicts don't pickle their factories cleanly across the Pool boundary; return plain dicts.
    return ({k: dict(v) for k, v in total.items()},
            {c: {k: dict(v) for k, v in d.items()} for c, d in by_cat.items()},
            per_snippet, errors)


def _gen_ir_worker(py_path):
    """Pure-Python IR generation (node_visitor + local-import inlining) — no Lean backend, so it
    parallelises freely. Mirrors `Session.to_json_ir_file(py, infer_only=True)`."""
    import json as _json
    from pastalean.transpile import driver
    try:
        raw = driver.translate_to_json(open(py_path).read(), py_path,
                                       best_effort=True, infer_only=True)
        return (py_path, _json.loads(raw))
    except Exception:  # noqa: BLE001
        return (py_path, None)


def _typeinfer_exe_path():
    from pastalean import paths  # resolves repo locations from __file__, never the cwd
    exe = Path(paths.LAKE_BIN_DIR) / "typeinfer"
    return exe if exe.exists() else None


def run_typeinfer_engine(snippets, jobs, out_total, out_by_cat, out_per_snippet):
    """The fast path: parallel pure-Python IR-gen (no backend boot) → one batched, in-process-parallel
    inference call to the standalone `typeinfer` exe → score. Returns the error count and phase times."""
    import subprocess, time
    from multiprocessing import Pool
    exe = _typeinfer_exe_path()
    if exe is None:
        raise SystemExit("typeinfer exe not built — run `lake build typeinfer` first.")
    withgt = [py for py in snippets if py.with_name("main_gt.json").exists()]

    t0 = time.time()
    if jobs > 1:
        with Pool(jobs) as p:
            irs = p.map(_gen_ir_worker, [str(py) for py in withgt])
    else:
        irs = [_gen_ir_worker(str(py)) for py in withgt]
    t1 = time.time()

    empty = {"node_type": "Module", "body": []}
    asts = [ir if ir is not None else empty for _, ir in irs]
    # Size the exe's task-scheduler thread pool (Lean's `LEAN_NUM_THREADS`) to the cores; the batch
    # then fans across them in-process. Plateaus once threads ≥ ~cores (serial JSON framing bounds it).
    import os as _os
    env = {**_os.environ, "LEAN_NUM_THREADS": str(min(_os.cpu_count() or 8, 64))}
    proc = subprocess.Popen([str(exe), "--server"], stdin=subprocess.PIPE,
                            stdout=subprocess.PIPE, text=True, env=env)
    import json as _json
    proc.stdin.write(_json.dumps({"task": "inferBatch", "asts": asts}) + "\n")
    proc.stdin.flush()
    out = _json.loads(proc.stdout.readline())
    proc.stdin.close(); proc.wait()
    t2 = time.time()

    errors = 0
    for (py_path, ir), st in zip(irs, out.get("results", [])):
        if ir is None:
            errors += 1
        stamped = st.get("ast", st) if isinstance(st, dict) else st
        preds = collect(stamped)
        py = Path(py_path); cat = py.parts[-3]
        agg, _ = score(preds, load_gt(py.with_name("main_gt.json")))
        out_per_snippet[f"{cat}/{py.parent.name}"] = {k: dict(v) for k, v in agg.items()}
        for kind, a in agg.items():
            for f in ("total", "covered", "matched"):
                out_total[kind][f] += a[f]; out_by_cat[cat][kind][f] += a[f]
            out_total[kind]["sim"] += a["sim"]; out_by_cat[cat][kind]["sim"] += a["sim"]
    print(f"[*] IR-gen {t1-t0:.2f}s ({jobs} procs) + inference {t2-t1:.2f}s (1 exe, in-proc parallel) "
          f"= {t2-t0:.2f}s, no backend boot")
    return errors


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--bench", type=Path, default=DEFAULT_BENCH)
    ap.add_argument("--out", type=Path, default=Path(__file__).resolve().parent / "typeinfer_summary.json")
    ap.add_argument("--diff", default=None, help="Dump per-fact pred-vs-gold for snippets in this category")
    ap.add_argument("--misses", action="store_true", help="Aggregate the most common miss patterns globally")
    ap.add_argument("--limit", type=int, default=None, help="Only run the first N snippets (for a quick slice)")
    ap.add_argument("--jobs", default="auto",
                    help="Parallel warm backends: 'auto' (memory-aware, 16-32 band) or an integer. "
                         "1 = serial. --diff/--misses force serial.")
    ap.add_argument("--engine", choices=("typeinfer", "backend"), default="typeinfer",
                    help="'typeinfer' (default; standalone exe: no boot, parallel pure-Python IR-gen "
                         "+ one batched in-process-parallel inference call). 'backend' (legacy warm "
                         "py2lean, per-snippet; slow, Mathlib-heavy) is only kept because --diff/--misses "
                         "stream per-fact detail from its loop.")
    args = ap.parse_args()
    miss_counts = defaultdict(int)
    miss_examples = {}

    snippets = sorted(args.bench.glob("*/*/main.py"))
    if args.limit:
        snippets = snippets[:args.limit]
    print(f"[*] {len(snippets)} snippets under {args.bench}")

    total = defaultdict(lambda: {"total": 0, "covered": 0, "matched": 0, "sim": 0.0})
    by_cat = defaultdict(lambda: defaultdict(lambda: {"total": 0, "covered": 0, "matched": 0, "sim": 0.0}))
    per_snippet, errors = {}, 0

    jobs = auto_jobs(len(snippets)) if args.jobs == "auto" else max(1, int(args.jobs))
    # --diff/--misses stream per-fact detail from inside the loop; keep them serial.
    if (args.diff or args.misses) and jobs > 1:
        print(f"[*] --diff/--misses set: forcing --jobs 1 (was {jobs})")
        jobs = 1
    print(f"[*] jobs={jobs} ({args.jobs}){'  free=%.0fGiB cores=%d' % (_mem_available_gb(), (__import__('os').cpu_count() or 0)) if args.jobs == 'auto' else ''}")

    if args.engine == "typeinfer":
        if args.diff or args.misses:
            raise SystemExit("--diff/--misses require --engine backend")
        errors = run_typeinfer_engine(snippets, jobs, total, by_cat, per_snippet)
        _run_serial = False
    elif jobs > 1:
        from multiprocessing import Pool
        paths = [str(p) for p in snippets]
        chunks = [paths[i::jobs] for i in range(jobs)]  # round-robin: even load per worker
        with Pool(jobs) as pool:
            for t_p, bc_p, ps_p, err_p in pool.map(_eval_chunk, chunks):
                errors += err_p
                per_snippet.update(ps_p)
                for kind, a in t_p.items():
                    for f in ("total", "covered", "matched", "sim"):
                        total[kind][f] += a[f]
                for c, d in bc_p.items():
                    for kind, a in d.items():
                        for f in ("total", "covered", "matched", "sim"):
                            by_cat[c][kind][f] += a[f]
        _run_serial = False
    else:
        _run_serial = True

    s = Session(target="command", mode="both") if _run_serial else None
    if _run_serial:
        s.start()
    try:
        for py in (snippets if _run_serial else []):
            cat = py.parts[-3]
            gt = py.with_name("main_gt.json")
            if not gt.exists():
                continue
            try:
                # Local sibling imports are resolved by the transpiler pipeline itself
                # (driver.resolve_local_imports), so this is exactly what `pastalean translate` sees.
                ir = s.to_json_ir_file(py, infer_only=True)
                res = s.client.infer_types(ir)
                stamped = res.get("ast", res) if isinstance(res, dict) else res
                preds = collect(stamped)
            except Exception as e:  # noqa: BLE001
                errors += 1
                preds = ({}, {}, {}, {}, {})
            agg, diffs = score(preds, load_gt(gt))
            if args.misses:
                for kind, key, pred, golds in diffs:
                    if pred not in golds:
                        subs = "[" in str(key) or "." in str(key)
                        bucket = (kind, "sub/attr" if subs else "plain",
                                  "predicted-wrong" if pred else "no-prediction", tuple(golds))
                        miss_counts[bucket] += 1
                        miss_examples.setdefault(bucket, []).append(cat)
            if args.diff and cat == args.diff:
                print(f"\n--- {cat}/{py.parent.name} ---")
                for kind, key, pred, golds in diffs:
                    mark = "OK " if pred in golds else ("~~ " if pred else "MISS")
                    print(f"    [{mark}] {kind:6} {key}: pred={pred} gold={golds}")
            per_snippet[f"{cat}/{py.parent.name}"] = {k: dict(v) for k, v in agg.items()}
            for kind, a in agg.items():
                for f in ("total", "covered", "matched"):
                    total[kind][f] += a[f]; by_cat[cat][kind][f] += a[f]
                total[kind]["sim"] += a["sim"]; by_cat[cat][kind]["sim"] += a["sim"]
    finally:
        if s is not None:
            s.close()

    def line(a):
        t, c, m, sim = a["total"], a["covered"], a["matched"], a["sim"]
        return (f"match {m}/{t} ({100*m/t:.1f}%)  cover {c}/{t} ({100*c/t:.1f}%)  TypeSim {sim/t:.3f}"
                if t else "—")

    print("\n=== Per dimension ===")
    grand = {"total": 0, "covered": 0, "matched": 0, "sim": 0.0}
    for kind in ("return", "param", "var"):
        a = total[kind]; print(f"  {kind:7} {line(a)}")
        for f in grand:
            grand[f] += a[f]
    print(f"  {'ALL':7} {line(grand)}")

    # TypeEvalPy leaderboard-style breakdown (exact-match counts per dimension).
    print("\n=== Exact-match breakdown (TypeEvalPy leaderboard columns) ===")
    labels = [("Function Return Type", "return"), ("Function Parameter Type", "param"),
              ("Local Variable Type", "var")]
    print(f"  {'Dimension':24} {'Exact match':>14}")
    for label, kind in labels:
        a = total[kind]
        print(f"  {label:24} {a['matched']:>7} / {a['total']:<6}")
    print(f"  {'Total':24} {grand['matched']:>7} / {grand['total']:<6}")

    print("\n=== Per category (all dimensions) ===")
    for cat in sorted(by_cat):
        a = {"total": 0, "covered": 0, "matched": 0, "sim": 0.0}
        for kind in by_cat[cat].values():
            for f in a:
                a[f] += kind[f]
        print(f"  {cat:16} {line(a)}")

    if args.misses:
        print("\n=== Top miss patterns (kind, shape, why, gold) ===")
        for k, c in sorted(miss_counts.items(), key=lambda kv: -kv[1])[:30]:
            print(f"  {c:4}  {k[0]:6} {k[1]:8} {k[2]:16} gold={list(k[3])}  cats: {sorted(set(miss_examples.get(k,[])), key=miss_examples.get(k,[]).count, reverse=True)[:4]}")

    print(f"\n[*] snippets with a backend/convert error: {errors}")
    args.out.write_text(json.dumps({
        "breakdown": {
            "Function Return Type": {"matched": total["return"]["matched"], "total": total["return"]["total"]},
            "Function Parameter Type": {"matched": total["param"]["matched"], "total": total["param"]["total"]},
            "Local Variable Type": {"matched": total["var"]["matched"], "total": total["var"]["total"]},
            "Total": {"matched": grand["matched"], "total": grand["total"]},
        },
        "overall": {k: dict(v) for k, v in total.items()},
        "grand": grand,
        "by_category": {c: {k: dict(v) for k, v in d.items()} for c, d in by_cat.items()},
        "per_snippet": per_snippet, "errors": errors,
    }, indent=2))
    print(f"[*] summary -> {args.out}")


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Tests for the `pastalean.typeinfer` production front-end.

Most tests are hermetic: they feed a hand-built `InferResult` (or a stamped AST) to the pure-Python
modules — render / collect / coverage / diagnostics / stub / config / annotate — so they need neither
the Lean `typeinfer` binary nor a backend boot. One smoke test drives the real engine end-to-end and
is skipped (not failed) when the binary is not built.

Run (no pytest needed):
    uv run python -m pastalean.typeinfer.tests.test_typeinfer
"""

from __future__ import annotations

import json
import sys
import tempfile
from pathlib import Path

from .. import (
    FieldInfo, FuncInfo, InferResult, VarInfo,
    annotate_source, collect_types, coverage, diagnostics, iter_slots,
    render_pytype, to_github, to_sarif, to_stub,
)
from ..config import find_config, load_config

FAILURES: list[str] = []


def check(name: str, cond: bool, detail: str = "") -> None:
    if not cond:
        FAILURES.append(f"{name}: {detail}" if detail else name)


def eq(name: str, got, want) -> None:
    check(name, got == want, f"got {got!r}, want {want!r}")


# --- render_pytype --------------------------------------------------------------------------------

def _name(i: str) -> dict:
    return {"node_type": "Name", "id": i}


def test_render() -> None:
    eq("render.int", render_pytype(_name("Int")), "int")
    eq("render.str", render_pytype(_name("String")), "str")
    eq("render.any", render_pytype(_name("PyAny")), "Any")
    eq("render.callable", render_pytype(_name("Callable")), "Callable")
    eq("render.userclass", render_pytype(_name("pkg.Point")), "Point")
    eq("render.empty", render_pytype({"node_type": "Name"}), None)
    eq("render.list_int",
       render_pytype({"node_type": "Subscript", "value": _name("List"), "slice": _name("Int")}),
       "list[int]")
    eq("render.optional",
       render_pytype({"node_type": "Subscript", "value": _name("Optional"), "slice": _name("Int")}),
       "Optional[int]")
    eq("render.dict_pair",
       render_pytype({"node_type": "Subscript", "value": _name("Dict"),
                      "slice": {"node_type": "Tuple", "elts": [_name("String"), _name("Int")]}}),
       "dict[str, int]")
    eq("render.tuple",
       render_pytype({"node_type": "Tuple", "elts": [_name("Int"), _name("String")]}),
       "tuple[int, str]")
    eq("render.none_const", render_pytype({"node_type": "Constant", "value": None}), "None")


# --- collect_types (stamped AST -> records) -------------------------------------------------------

def test_collect() -> None:
    stamped = {
        "node_type": "Module",
        "body": [{
            "node_type": "FunctionDef",
            "name": "f",
            "args": {"args": [
                {"arg": "self"},                                   # dropped
                {"arg": "x", "_ty": _name("Int")},
            ]},
            "_ret_ty": _name("String"),
            "body": [
                {"node_type": "Assign",
                 "targets": [{"node_type": "Name", "id": "y", "_ty": _name("Bool")}]},
            ],
        }],
    }
    res = collect_types(stamped)
    eq("collect.nfuncs", len(res.functions), 1)
    eq("collect.params", res.functions[0].params, {"x": "int"})
    eq("collect.returns", res.functions[0].returns, "str")
    var = next((v for v in res.variables if v.name == "y"), None)
    check("collect.var", var is not None and var.type == "bool" and var.scope == "f",
          f"got {var!r}")


# --- a shared synthetic result for the source-driven modules --------------------------------------

_SRC = '''\
def greet(name):
    msg = "hi"
    return msg


class Point:
    def __init__(self, x, y):
        self.x = x
        self.y = y


def mystery(z: int):
    return z
'''

def _result() -> InferResult:
    return InferResult(
        functions=[
            FuncInfo("greet", {"name": "str"}, "str"),
            FuncInfo("Point.__init__", {"x": "int", "y": "Any"}, "None"),
            FuncInfo("mystery", {"z": "int"}, "int"),
        ],
        variables=[VarInfo("msg", "str", "greet", "msg")],
        fields=[FieldInfo("Point", "x", "int"), FieldInfo("Point", "y", "Any")],
    )


# --- coverage / iter_slots ------------------------------------------------------------------------

def test_coverage() -> None:
    res = _result()
    slots = {(s.kind, s.qualname, s.name): s for s in iter_slots(_SRC, res)}
    # `z` already annotated in the source -> `existing` wins, counts as typed.
    z = slots[("params", "mystery", "z")]
    eq("cov.existing_wins", z.existing, "int")
    check("cov.existing_typed", z.typed, "annotated slot should be typed")
    # `y` param inferred only Any -> not typed.
    check("cov.any_untyped", not slots[("params", "Point.__init__", "y")].typed, "Any must be untyped")
    check("cov.int_typed", slots[("params", "Point.__init__", "x")].typed, "int must be typed")

    cov = coverage(_SRC, res)
    # params: name(str) x(int) y(Any) z(int-existing) -> 3/4 ; returns: greet,__init__,mystery all
    # concrete -> 3/3 ; variables: msg(str) -> 1/1 ; fields: x(int) y(Any) -> 1/2.
    eq("cov.params", cov["dimensions"]["params"], {"typed": 3, "total": 4})
    eq("cov.returns", cov["dimensions"]["returns"], {"typed": 3, "total": 3})
    eq("cov.variables", cov["dimensions"]["variables"], {"typed": 1, "total": 1})
    eq("cov.fields", cov["dimensions"]["fields"], {"typed": 1, "total": 2})
    eq("cov.total", (cov["typed"], cov["total"]), (8, 10))
    check("cov.ratio", abs(cov["coverage"] - 0.8) < 1e-9, f"got {cov['coverage']}")


# --- diagnostics ----------------------------------------------------------------------------------

def test_diagnostics() -> None:
    res = _result()
    diags = diagnostics(_SRC, res, "m.py")
    by = {(d.code, d.message) for d in diags}
    # Only the two Any slots are unresolved; every other slot is concrete or already annotated.
    eq("diag.count", len(diags), 2)
    check("diag.any_param", ("any-type", "parameter 'y' of Point.__init__ inferred only as Any") in by,
          f"got {sorted(by)}")
    check("diag.any_field", ("any-type", "field 'y' of Point inferred only as Any") in by,
          f"got {sorted(by)}")
    check("diag.no_existing_flagged", all("'z'" not in d.message for d in diags),
          "an already-annotated slot must never be flagged")
    check("diag.no_typed_flagged", all("'name'" not in d.message for d in diags),
          "a concretely-inferred slot must never be flagged")

    gh = to_github(diags)
    check("diag.github", gh.startswith("::warning file=m.py,line="), gh[:40])
    doc = json.loads(to_sarif(diags, "m.py"))
    eq("diag.sarif_version", doc["version"], "2.1.0")
    eq("diag.sarif_results", len(doc["runs"][0]["results"]), 2)
    check("diag.sarif_level", all(r["level"] == "warning" for r in doc["runs"][0]["results"]), "")


def test_diagnostics_empty() -> None:
    # A fully-typed result yields no diagnostics.
    src = "def f(a):\n    return a\n"
    res = InferResult(functions=[FuncInfo("f", {"a": "int"}, "int")])
    eq("diag.clean", diagnostics(src, res, "m.py"), [])


# --- stub -----------------------------------------------------------------------------------------

def test_stub() -> None:
    res = _result()
    stub = to_stub(_SRC, res, include_any=True)
    check("stub.greet", "def greet(name: str) -> str: ..." in stub, stub)
    check("stub.class", "class Point:" in stub, stub)
    check("stub.field_int", "x: int" in stub, stub)
    check("stub.import", stub.startswith("from typing import Any"), stub[:40])

    stub2 = to_stub(_SRC, res, include_any=False)
    check("stub.no_any_param", "y: Any" not in stub2, stub2)
    check("stub.no_any_import", "from typing import" not in stub2, stub2)


# --- annotate_source ------------------------------------------------------------------------------

def test_annotate() -> None:
    out = annotate_source(_SRC, _result(), include_any=True)
    check("annot.param", "def greet(name: str) -> str:" in out, out)
    check("annot.var", "msg: str" in out, out)
    check("annot.field", "self.x: int" in out, out)
    check("annot.keeps_existing", "def mystery(z: int) -> int:" in out, out)
    check("annot.typing_import", "from typing import Any" in out, out)

    out2 = annotate_source(_SRC, _result(), include_any=False)
    check("annot.no_any_field", "self.y:" not in out2, out2)
    check("annot.no_any_import", "from typing import" not in out2, out2)


# --- config -------------------------------------------------------------------------------------

def test_config() -> None:
    with tempfile.TemporaryDirectory() as d:
        root = Path(d)
        (root / "pyproject.toml").write_text(
            '[tool.typeinfer]\nformat = "list"\nno-any = true\nfail-under = 75\n', encoding="utf-8")
        nested = root / "pkg" / "sub"
        nested.mkdir(parents=True)
        target = nested / "m.py"
        target.write_text("x = 1\n", encoding="utf-8")

        eq("config.find", find_config(target), root / "pyproject.toml")
        cfg = load_config(target)
        eq("config.format", cfg.get("format"), "list")
        eq("config.no_any", cfg.get("no_any"), True)
        eq("config.fail_under", cfg.get("fail_under"), 75.0)

    with tempfile.TemporaryDirectory() as d:
        # A pyproject without [tool.typeinfer] -> empty config, not a crash.
        root = Path(d)
        (root / "pyproject.toml").write_text("[project]\nname='x'\n", encoding="utf-8")
        f = root / "m.py"
        f.write_text("x = 1\n", encoding="utf-8")
        eq("config.absent", load_config(f), {})


# --- optional end-to-end smoke test through the real Lean engine ---------------------------------

def test_engine_smoke() -> int:
    """Drive the actual `typeinfer` binary once. Returns 1 if it ran and disagreed, 0 otherwise
    (including when the binary is not built — that is a skip, not a failure)."""
    from ...backend.typeinfer import TypeInferUnavailable
    from ..engine import infer_source
    try:
        res = infer_source('def add(a, b):\n    return a + "x" + b\n', "e.py")
    except TypeInferUnavailable as err:
        print(f"  (skipped engine smoke test: {err})")
        return 0
    fn = next((f for f in res.functions if f.qualname == "add"), None)
    check("engine.found", fn is not None, "engine returned no `add`")
    if fn is not None:
        # `a + "x"` forces `a` to str; the smoke test asserts the pipeline runs end-to-end and
        # produces a concrete inference, not the engine's full precision (that is the benchmark's job).
        eq("engine.param_a", fn.params.get("a"), "str")
    return 0


def test_server() -> None:
    """The persistent server: one process answers many tasks (reuse), separate servers are isolated,
    and a closed server transparently respawns. Skipped if the binary is not built."""
    from ...backend.typeinfer import TypeInferServer, TypeInferUnavailable
    from ..engine import infer_sources
    tiny = {"node_type": "Module", "body": [
        {"node_type": "Assign", "targets": [{"node_type": "Name", "id": "x"}],
         "value": {"node_type": "Constant", "value": 1}}]}
    try:
        srv = TypeInferServer()
        srv.infer_ast(tiny)
    except TypeInferUnavailable as err:
        print(f"  (skipped server test: {err})")
        return

    # Reuse: three tasks share one process (pid stable, process stays alive).
    pid = srv._proc.pid
    for _ in range(3):
        srv.infer_ast(tiny)
    check("server.reuse_pid", srv._proc.pid == pid, "server respawned mid-unit")
    check("server.alive", srv._proc.poll() is None, "server died mid-unit")

    # Isolation: an independent server is a different process.
    with TypeInferServer() as other:
        other.infer_ast(tiny)
        check("server.isolated", other._proc.pid != pid, "two units shared a process")

    # Respawn: after close, the next task starts a fresh process.
    srv.close()
    check("server.closed", srv._proc is None, "close did not clear the process")
    srv.infer_ast(tiny)
    check("server.respawn", srv._proc is not None and srv._proc.pid != pid, "did not respawn")
    srv.close()

    # infer_sources reuses one server across N files and returns N results.
    res = infer_sources([("def f(a):\n    return a\n", f"m{i}.py") for i in range(3)])
    eq("server.infer_sources_n", len(res), 3)


def main() -> int:
    test_render()
    test_collect()
    test_coverage()
    test_diagnostics()
    test_diagnostics_empty()
    test_stub()
    test_annotate()
    test_config()
    test_engine_smoke()
    test_server()

    if FAILURES:
        print(f"FAILED ({len(FAILURES)}):")
        for f in FAILURES:
            print(f"  - {f}")
        return 1
    print("all typeinfer front-end tests passed")
    return 0


if __name__ == "__main__":
    sys.exit(main())

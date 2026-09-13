"""`pastalean typeinfer` — surface the TypeInfer engine's inferences for one Python file or repo.

The engine itself is the compiled Lean `typeinfer` binary (see `backend/typeinfer.py`); this package
is the production front-end around it:

    Python source --(node_visitor)--> JSON IR --(typeinfer exe)--> type-stamped AST
                                                    |
              +----------------+----------------+---+------------+---------------+
              v                v                v                v               v
        annotated .py    JSON / listing    .pyi stub     coverage report    diagnostics

The engine stamps each assignment target / parameter / class field with a `_ty` (or `_bench_ty`)
annotation node and each function with a return-type stamp. `collect_types` (collect.py) walks that
stamped AST into scope-keyed records (records.py); `render_pytype` (render.py) turns one annotation
node into a Python type string; the formatters (report.py, annotate.py, stub.py) render those
records; coverage.py / diagnostics.py add the production CI surface; cli.py wires the command.
"""

from __future__ import annotations

from .annotate import annotate_repo, annotate_source
from .collect import collect_types
from .coverage import Slot, coverage, format_coverage_report, iter_slots
from .diagnostics import Diagnostic, diagnostics, to_github, to_sarif
from .engine import infer_file, infer_repo_dir, infer_source, infer_sources
from .records import FieldInfo, FuncInfo, InferResult, VarInfo, MODULE_SCOPE
from .render import render_pytype
from .report import count_annotations, format_stats_report, to_json_obj, to_report
from .stub import to_stub

__all__ = [
    "MODULE_SCOPE",
    "FuncInfo", "VarInfo", "FieldInfo", "InferResult",
    "render_pytype", "collect_types",
    "infer_source", "infer_file", "infer_sources", "infer_repo_dir",
    "annotate_source", "annotate_repo",
    "count_annotations", "format_stats_report", "to_json_obj", "to_report",
    "coverage", "format_coverage_report", "iter_slots", "Slot",
    "diagnostics", "Diagnostic", "to_github", "to_sarif",
    "to_stub",
]

"""Diagnostics for unresolved slots, with CI-friendly output formats.

A slot the engine could not resolve (no existing annotation, and either no inference or a bare `Any`)
becomes one diagnostic. `to_github` emits GitHub Actions workflow-command annotations; `to_sarif`
emits SARIF 2.1.0 so the results can be uploaded to a code-scanning dashboard."""

from __future__ import annotations

import json
from dataclasses import dataclass

from .coverage import Slot, iter_slots
from .records import InferResult

TOOL_NAME = "typeinfer"

def _subject(kind: str, name: str, owner: str) -> str:
    owner = owner or "<module>"
    if kind == "returns":
        return f"return type of {owner}"
    if kind == "params":
        return f"parameter '{name}' of {owner}"
    if kind == "fields":
        return f"field '{name}' of {owner}"
    return f"variable '{name}' in {owner}"


@dataclass
class Diagnostic:
    file: str
    line: int
    col: int
    code: str      # "no-type" (no inference at all) or "any-type" (inferred only Any)
    message: str


def diagnostics(source: str, result: InferResult, path: str) -> list[Diagnostic]:
    """One diagnostic per unresolved slot in `source`. Slots that already carry a source annotation
    are never flagged; a slot inferred as bare `Any` is flagged as `any-type`, one with no inference
    at all as `no-type`."""
    diags: list[Diagnostic] = []
    for s in iter_slots(source, result):
        if s.existing is not None or s.typed:
            continue
        subject = _subject(s.kind, s.name, s.qualname)
        if s.inferred == "Any":
            code = "any-type"
            msg = f"{subject} inferred only as Any"
        else:
            code = "no-type"
            msg = f"{subject} has no inferred type"
        diags.append(Diagnostic(path, s.line, s.col + 1, code, msg))
    return diags


def to_text(diags: list[Diagnostic]) -> str:
    return "\n".join(f"{d.file}:{d.line}:{d.col}: {d.code}: {d.message}" for d in diags)


def to_github(diags: list[Diagnostic]) -> str:
    """GitHub Actions workflow commands (`::warning file=...,line=...,col=...::message`), which the
    CI log renders as inline annotations on the changed lines."""
    return "\n".join(
        f"::warning file={d.file},line={d.line},col={d.col},title=typeinfer {d.code}::{d.message}"
        for d in diags
    )


def to_sarif(diags: list[Diagnostic], path: str) -> str:
    """SARIF 2.1.0 JSON — the interchange format code-scanning dashboards ingest."""
    rules = {}
    for d in diags:
        rules.setdefault(d.code, {"id": d.code, "shortDescription": {"text": d.code}})
    results = [
        {
            "ruleId": d.code,
            "level": "warning",
            "message": {"text": d.message},
            "locations": [{
                "physicalLocation": {
                    "artifactLocation": {"uri": d.file},
                    "region": {"startLine": d.line, "startColumn": d.col},
                }
            }],
        }
        for d in diags
    ]
    doc = {
        "version": "2.1.0",
        "$schema": "https://json.schemastore.org/sarif-2.1.0.json",
        "runs": [{
            "tool": {"driver": {"name": TOOL_NAME, "rules": list(rules.values())}},
            "results": results,
        }],
    }
    return json.dumps(doc, indent=2)

"""`pastalean mcp` — an MCP server that lets an LLM verify Python logic through PastaLean.

The intended loop, which the server's `instructions` spell out to the client:

    write contracts in the Python  ->  translate_python  ->  prove the emitted spec theorems
    ->  verify_theorems (axiom audit + fidelity check)  ->  run_differential for the runnable twin

Every artifact lands in `.pastalean-mcp/` under the repo, so a client with file access can edit the
generated Lean in place and hand back `lean_path`. `verify_theorems` is the only tool whose answer
means "proved": it compiles the file, audits each theorem's axioms, and checks the definitions and
theorem statements are still the ones `translate_python` emitted.
"""

from __future__ import annotations

import re
import threading
from pathlib import Path
from typing import Any

from .api import Session
from .backend import lean as lean_tools
from .paths import REPO_ROOT

WORKSPACE = REPO_ROOT / ".pastalean-mcp"
GUIDES = {
    "contracts": REPO_ROOT / "docs" / "contract-prompt-system.md",
    "proving": REPO_ROOT / "docs" / "proving-with-pastalean.md",
    "verifiable_design": REPO_ROOT / "docs" / "verifiable-python-design.md",
    "contract_qa": REPO_ROOT / "docs" / "contract-qa.md",
}
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
LEMMA_ROOTS = ("PastaLean", "Libraries")
# What the source-browsing tools may read: the runtime, libraries, docs, examples, the front end.
BROWSE_ROOTS = ("PastaLean", "Libraries", "TypeInfer", "docs", "PastaBench", "example_scripts", "src")
BROWSE_SUFFIXES = {".lean", ".md", ".py"}
EXAMPLE_ROOTS = (REPO_ROOT / "PastaBench" / "humaneval",)
PLAYGROUND = REPO_ROOT / "example_scripts" / "mvcgen_playground"

INSTRUCTIONS = """\
PastaLean translates Python deterministically into Lean 4 so its logic can be PROVED, not just tested.

Workflow for verifying a Python function:
1. Read get_guide("contracts"). Annotate the Python with `from contracts import *` and
   Requires / Ensures (with Result()) / Invariant (first statement in each loop) / Decreases.
   State the function's PURPOSE (e.g. Result() == n!), not bookkeeping. Quantify with all()/any().
2. translate_python. It returns lean_path plus the open proof obligations (theorems ending in
   `taste?`). If `degraded` is true, the relevant logic was replaced by pyUnsupported and cannot be
   verified -- restructure the Python (get_guide("verifiable_design")) and translate again.
   Then find_counterexample: it searches every property function and contract (CPython engines incl.
   precondition-directed search, Hypothesis and CrossHair, plus both Lean twins). REFUTED means the
   claim is FALSE -- report it with the witness and do not try to prove it; FLOAT_ONLY /
   ROUNDING_SENSITIVE / TWIN_DIVERGENCE_* mean a proof over exact ℚ would not cover the float program
   -- say so (ROUNDING_SENSITIVE: the proved IEEE error enclosure shows the flip is a rounding effect);
   FIDELITY_BUG is a PastaLean translation bug -- report it; PARTIALITY_GAP means Python raises on the
   witness while the exact model returns a default -- the proof would hold but the program crashes.
3. Prove each obligation by editing ONLY the proof after `:= by` (helper lemmas may be added).
   Never change a `def` or a theorem statement. get_guide("proving"), list_proved_examples /
   get_example and search_lemmas show the patterns (mvcgen + loop invariants over cur.prefix.length).
   When a goal mentions a runtime function (pyLen, pyAppend, pySetItem, ...), look it up:
   find_definition shows what it computes, search_lemmas/grep_source the facts already proved about
   it, read_source the surrounding file. `#check @PastaLean.pyLen` / `#print PastaLean.pyAppend` inside
   check_lean also works. Use check_lean to iterate on errors.
4. verify_theorems is the ONLY verdict. Report a function as proved only if every theorem shows
   status "proved". An obligation that resists every proof may be a FALSE postcondition -- look for a
   counterexample (run_differential / evaluate the runnable twin) before trying harder.
5. run_differential compares CPython with the runnable twin on a program with a __main__ block.
"""

_THEOREM_RE = re.compile(r"^(?:@\[[^\]]*\]\s*)*(?:private\s+|protected\s+)?(?:theorem|lemma)\s+(\S+)")
_DECL_START_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*(?:noncomputable\s+|private\s+|protected\s+|partial\s+|unsafe\s+)*"
    r"(def|theorem|lemma|instance|structure|inductive|abbrev|axiom|opaque)\b"
)
_AXIOMS_RE = re.compile(r"'(?P<name>[^']+)' depends on axioms: \[(?P<axioms>[^\]]*)\]")
_NO_AXIOMS_RE = re.compile(r"'(?P<name>[^']+)' does not depend on any axioms")
_SAFE_NAME_RE = re.compile(r"[^A-Za-z0-9_.-]+")
# The `:=` that ends a signature: followed by `by` or a line break, so `let x := e` inside a
# statement does not end it.
_PROOF_SEP_RE = re.compile(r":=\s*(?=by\b|\n|$)")
# Added content may only prove things. A new def/instance/notation could change what an unchanged
# statement *means*; these constructs bypass the kernel or name resolution outright.
_FORBIDDEN_DECL_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*(?:private\s+|protected\s+|noncomputable\s+|local\s+|scoped\s+|partial\s+)*"
    r"(def|abbrev|instance|opaque|axiom|structure|inductive|class|notation|infix|infixl|infixr|prefix|"
    r"postfix|macro|macro_rules|syntax|elab|elab_rules|declare_syntax_cat|initialize|builtin_initialize)\b"
)
_FORBIDDEN_ANYWHERE_RE = re.compile(
    r"skipKernelTC|implemented_by|\bextern\b|\bunsafe\b|default_instance|\brun_cmd\b|\brun_tac\b|"
    r"\battribute\s*\[[^\]]*\binstance\b"
)


class _State:
    """One warm translation backend for the life of the server (Mathlib boots once)."""

    def __init__(self) -> None:
        self._session: Session | None = None
        self._lock = threading.Lock()

    def session(self) -> Session:
        with self._lock:
            if self._session is None:
                self._session = Session(target="command", mode="both").start()
            return self._session


_STATE = _State()


# ── helpers ──────────────────────────────────────────────────────────────────────────────────────


def _workspace_file(name: str, suffix: str) -> Path:
    WORKSPACE.mkdir(exist_ok=True)
    stem = _SAFE_NAME_RE.sub("_", name).strip("._") or "program"
    return WORKSPACE / f"{stem}{suffix}"


def _resolve_source(source: str | None, path: str | None, name: str) -> tuple[str, Path]:
    """The Python text plus a file holding it (the translator re-reads sources by path)."""
    if (source is None) == (path is None):
        raise ValueError("pass exactly one of `source` or `path`")
    if path is not None:
        p = Path(path).expanduser()
        if not p.is_absolute():
            p = REPO_ROOT / p
        return p.read_text(encoding="utf-8"), p
    p = _workspace_file(name, ".py")
    p.write_text(source, encoding="utf-8")
    return source, p


def _resolve_lean(lean_code: str | None, lean_path: str | None) -> tuple[str, Path | None]:
    if (lean_code is None) == (lean_path is None):
        raise ValueError("pass exactly one of `lean_code` or `lean_path`")
    if lean_path is not None:
        p = Path(lean_path).expanduser()
        if not p.is_absolute():
            p = REPO_ROOT / p
        return p.read_text(encoding="utf-8"), p
    return lean_code, None


def _declarations(code: str) -> list[tuple[str, str, str]]:
    """Top-level declarations as `(kind, qualified_name, text)`, tracking `namespace`/`end`.
    `text` runs from the declaration line to the line before the next top-level item."""
    lines = code.splitlines()
    starts: list[tuple[int, str, str]] = []
    namespaces: list[str] = []
    boundaries: list[int] = []
    attr_start: int | None = None  # first line of a run of attribute-only lines (`@[spec]`)
    for i, line in enumerate(lines):
        stripped = line.rstrip()
        if re.fullmatch(r"@\[[^\]]*\]", stripped):
            attr_start = i if attr_start is None else attr_start
            continue
        pending, attr_start = attr_start, None
        if stripped.startswith("namespace "):
            namespaces.append(stripped.split()[1])
            boundaries.append(i)
            continue
        if stripped.startswith("end ") and namespaces and stripped.split()[1] == namespaces[-1]:
            namespaces.pop()
            boundaries.append(i)
            continue
        if line[:1].isspace() or not stripped:
            continue
        m = _DECL_START_RE.match(stripped)
        if m:
            name_m = re.match(r"\s*(\S+)", stripped[m.end():])
            short = name_m.group(1) if name_m else ""
            qual = ".".join(namespaces + [short]) if namespaces else short
            first = pending if pending is not None else i
            starts.append((first, m.group(1), qual))
            boundaries.append(first)
        elif stripped.startswith(("#", "open ", "set_option ", "section", "variable ", "/-", "--",
                                  "attribute ")):
            boundaries.append(i)
    decls = []
    for i, kind, qual in starts:
        nxt = min((b for b in boundaries if b > i), default=len(lines))
        decls.append((kind, qual, "\n".join(lines[i:nxt]).rstrip()))
    return decls


def _split_proof(text: str) -> tuple[str, str]:
    """`(statement, proof)` of a theorem's text."""
    m = _PROOF_SEP_RE.search(text) or re.search(r":=", text)
    return (text[:m.start()], text[m.end():]) if m else (text, "")


def _statement(text: str) -> str:
    return " ".join(_split_proof(text)[0].split())


def _norm(text: str) -> str:
    return " ".join(text.split())


def _is_open(text: str) -> bool:
    return bool(re.search(r"\btaste\?|\bsorry\b|\badmit\b", _split_proof(text)[1]))


def _diagnostics(check: lean_tools.CheckResult, limit: int = 25) -> dict[str, Any]:
    errors = [str(d) for d in check.errors][:limit]
    warnings = [str(d) for d in check.diagnostics if d.severity == "warning"][:limit]
    out: dict[str, Any] = {"ok": check.ok and not check.errors, "errors": errors, "warnings": warnings}
    if not check.diagnostics and not check.ok:
        out["raw"] = (check.stderr or check.stdout)[-4000:]
    return out


# ── server ───────────────────────────────────────────────────────────────────────────────────────


def build_server():
    from mcp.server.mcpserver import MCPServer

    server = MCPServer(name="pastalean", instructions=INSTRUCTIONS)

    @server.tool()
    def translate_python(
        source: str | None = None,
        path: str | None = None,
        name: str = "program",
        mode: str = "both",
        heap: bool = False,
        strict: bool = False,
        check: bool = True,
    ) -> dict[str, Any]:
        """Translate Python (text via `source`, or a file via `path`) to Lean 4 with PastaLean.

        mode: "both" (default) emits the provable twin plus a runnable twin suffixed 'rn;
        "prove" exact Q/R only; "run" Float only. heap: opt-in reference semantics.
        strict: fail instead of degrading unsupported statements to pyUnsupported.
        check: compile the result (proof obligations replaced by `sorry` for speed).

        Returns lean_path (editable file under .pastalean-mcp/), the Lean code, the open proof
        obligations, and whether the translation was degraded.
        """
        text, py_path = _resolve_source(source, path, name)
        result = _STATE.session().translate(text, filepath=py_path, mode=mode, heap=heap,
                                            best_effort=not strict)
        if not result.ok:
            return {"ok": False, "stage": "translate", "error": result.error}
        code = result.lean_code or ""
        lean_path = _workspace_file(name, ".lean")
        lean_path.write_text(code + "\n", encoding="utf-8")
        # The pristine translation, against which verify_theorems checks fidelity.
        _workspace_file(name, ".orig.lean").write_text(code + "\n", encoding="utf-8")
        decls = _declarations(code)
        out: dict[str, Any] = {
            "ok": True,
            "lean_path": str(lean_path),
            "python_path": str(py_path),
            "degraded": result.degraded,
            "unsupported": result.unsupported,
            "definitions": [q for k, q, _ in decls if k in ("def", "abbrev")],
            # Proofs left to the `taste?` search (or `sorry`); the search sometimes closes them on its
            # own, so verify_theorems is what says which still need a proof.
            "proof_obligations": [q for k, q, t in decls if k in ("theorem", "lemma") and _is_open(t)],
            "lean_code": code,
        }
        if check:
            fast = re.sub(r"\bby\s+taste\?", "by sorry", code)
            out["compile"] = _diagnostics(lean_tools.compile_check(fast))
        return out

    @server.tool()
    def check_lean(lean_code: str | None = None, lean_path: str | None = None,
                   timeout: float = 600.0) -> dict[str, Any]:
        """Elaborate Lean (text or a file) against PastaLean + Mathlib and return its diagnostics.
        Use this to iterate on a proof; use verify_theorems for the final verdict."""
        code, path = _resolve_lean(lean_code, lean_path)
        check = lean_tools.compile_check(lean_path=path, timeout=timeout) if path else \
            lean_tools.compile_check(code, timeout=timeout)
        return _diagnostics(check)

    @server.tool()
    def verify_theorems(lean_code: str | None = None, lean_path: str | None = None,
                        theorems: list[str] | None = None, timeout: float = 900.0) -> dict[str, Any]:
        """The verdict. Compiles the file, then audits each theorem with `#print axioms`.

        A theorem is "proved" only if the file compiles and its axioms are within
        {propext, Classical.choice, Quot.sound} -- `sorry` (sorryAx), `native_decide`
        (Lean.ofReduceBool) or any user `axiom` disqualifies it. When `lean_path` came from
        translate_python, every emitted `def` and theorem statement must also be unchanged
        (fidelity), so a proof cannot succeed by weakening the program or the spec.
        theorems: names to audit (default: every theorem in the file)."""
        code, path = _resolve_lean(lean_code, lean_path)
        decls = _declarations(code)
        all_theorems = [q for k, q, _ in decls if k in ("theorem", "lemma")]
        wanted = theorems or all_theorems

        def qualify(name: str) -> str:
            if name in all_theorems:
                return name
            matches = [q for q in all_theorems if q.endswith("." + name)]
            return matches[0] if len(matches) == 1 else name

        targets = [qualify(t) for t in wanted]
        fidelity: dict[str, Any] = {"checked": False}
        if path is not None and path.suffix == ".lean":
            orig = path.with_name(path.stem + ".orig.lean")
            if orig.exists():
                fidelity = _fidelity(orig.read_text(encoding="utf-8"), code)

        probe = code.rstrip() + "\n\n" + "\n".join(f"#print axioms {t}" for t in targets) + "\n"
        check = lean_tools.compile_check(probe, timeout=timeout)
        output = check.stdout + check.stderr
        axioms: dict[str, list[str]] = {}
        for m in _AXIOMS_RE.finditer(output):
            axioms[m["name"]] = [a.strip() for a in m["axioms"].split(",") if a.strip()]
        for m in _NO_AXIOMS_RE.finditer(output):
            axioms[m["name"]] = []

        compiled = check.ok and not check.errors
        verdicts = {}
        for t in targets:
            if t not in axioms:
                verdicts[t] = {"status": "unknown", "reason": "no axiom report (name not found or file failed)"}
                continue
            extra = sorted(set(axioms[t]) - STANDARD_AXIOMS)
            if "sorryAx" in extra:
                verdicts[t] = {"status": "unproved", "reason": "depends on sorry", "axioms": axioms[t]}
            elif extra:
                verdicts[t] = {"status": "unproved", "reason": f"non-standard axioms {extra}",
                               "axioms": axioms[t]}
            elif not compiled:
                verdicts[t] = {"status": "unproved", "reason": "file has errors", "axioms": axioms[t]}
            else:
                verdicts[t] = {"status": "proved", "axioms": axioms[t]}
        # `<t>_counterexample : ¬ type_of% @<t>` proved cleanly means `<t>` is false, not merely unproved.
        for t in list(verdicts):
            refuter = verdicts.get(f"{t}_counterexample")
            if refuter and refuter["status"] == "proved":
                verdicts[t] = {"status": "refuted", "by": f"{t}_counterexample"}
        faithful = fidelity.get("ok", True)
        all_proved = compiled and faithful and bool(verdicts) and \
            all(v["status"] == "proved" for v in verdicts.values())
        return {"verified": all_proved, "compiled": compiled, "fidelity": fidelity,
                "theorems": verdicts, "diagnostics": _diagnostics(check)}

    @server.tool()
    def find_counterexample(source: str | None = None, path: str | None = None, name: str = "program",
                            only: str | None = None, seed: int = 24301, time_ms: int = 4000,
                            against_source: str | None = None, against_path: str | None = None,
                            stdin_examples: list[str] | None = None, negative: bool = False,
                            tests: int = 1000, equiv: list[str] | None = None) -> dict[str, Any]:
        """Search for inputs breaking the program's property functions (`def p(x): assert …`, e.g.
        `assert brute(xs) == fast(xs)`) and contracts (Requires/Ensures). Every witness is judged in the
        provable twin (exact ℚ), the runnable twin (Float) and CPython, and classified: REFUTED (false
        everywhere; comes with a kernel-checked `_counterexample` theorem), FLOAT_ONLY, ROUNDING_SENSITIVE,
        TWIN_DIVERGENCE_*, FIDELITY_BUG, ENCLOSURE_VIOLATION, NONTERMINATION, or NO_COUNTEREXAMPLE. A float
        witness also carries `ieee_enclosure`: the property re-run over sound IEEE error intervals
        (`holds` / `violates` for every rounding, `rounding`, or `unsupported:<why>`).

        A stdin program (a `main` reading `input()`) with no contracts is instead run on generated
        well-formed inputs (or mutations of `stdin_examples`) in CPython and both twins; with
        `against_source` / `against_path` (e.g. a brute-force reference) it looks for inputs on which
        the two programs print differently (PROGRAM_DIFF, confirmed in both Lean worlds). `negative`
        lets generated integers be negative.

        `tests` is how many inputs satisfying the `Requires` each search runs (draws are generated from
        the preconditions, and rejected ones do not count). `equiv` (e.g. ["brute=fast"]) also checks
        `brute(x) == fast(x)` on brute's inputs, without writing a property function. A contract
        witness reports what the function returned and which Ensures it broke: either the code or that
        Ensures is wrong."""
        from .refute import EXPLAIN, refute_source
        from .refute.obligations import collect, reads_stdin

        text, _ = _resolve_source(source, path, name)
        against = against_source
        if against is None and against_path:
            against, _ = _resolve_source(None, against_path, "reference")
        if against or stdin_examples or (not collect(text) and reads_stdin(text)):
            from .refute.stdin import refute_stdin

            rep = refute_stdin(text, session=_STATE.session(), against=against, examples=stdin_examples,
                               seed=seed, negative=negative)
            return {"ok": rep.error is None, "error": rep.error, "found": rep.found, "stdin": True,
                    "tested": rep.tested, "rejected": rep.rejected, "notes": rep.notes, "seed": seed,
                    "findings": [{"verdict": f.verdict, "explanation": EXPLAIN.get(f.verdict, ""),
                                  "note": f.note, "input": f.input,
                                  "worlds": {w: o.show() for w, o in f.worlds.items()}}
                                 for f in rep.findings]}
        pairs = [tuple(p.split("=", 1)) for p in (equiv or []) if "=" in p]
        report = refute_source(text, session=_STATE.session(), seed=seed, only=only, tests=tests,
                               equiv=pairs, time_ms=time_ms if time_ms != 4000 else None)
        out = []
        for o in report.obligations:
            entry = {"function": o.name, "theorem": o.theorem, "kind": o.kind, "verdict": o.verdict}
            if o.witness is not None:
                w = o.witness
                entry.update({
                    "witness": dict(zip(o.params, w.python)), "witness_lits": w.lits,
                    "explanation": EXPLAIN.get(o.verdict, ""),
                    "worlds": {"provable": w.prov, "runnable": w.run, "cpython": w.py},
                    "exception": w.exc, "found_by": w.origin, "ieee_enclosure": w.interval,
                    "explain": w.explain})
            py = o.searches.get("cpython") or {}
            entry["searched"] = {"valid_inputs": py.get("valid"), "rejected_by_requires": py.get("rejected"),
                                 "generated_from": py.get("plan")}
            if o.kernel_proof:
                thm = o.theorem or o.name
                entry["refutation_theorem"] = (f"theorem {thm}_counterexample : ¬ type_of% @{thm} := by\n"
                                               f"  {o.kernel_proof}")
            if o.error:
                entry["error"] = o.error
            out.append(entry)
        return {"ok": report.error is None, "error": report.error, "found": report.found,
                "obligations": out, "seed": seed}

    @server.tool()
    def float_model_report(source: str | None = None, path: str | None = None, name: str = "program",
                           samples: int = 200, seed: int = 24301) -> dict[str, Any]:
        """How faithfully each `-> float` function is modelled: on sampled inputs, CPython's result, the
        runnable twin's (Float) and the provable twin's (exact ℚ) against the proved IEEE error enclosure
        of the exact result. CPython must always lie inside (else the enclosure is wrong); the runnable
        twin should equal CPython bit for bit; `median_width` (ulps) is how far an exact-ℚ proof's value
        can be from the float one. `run_silent` counts inputs where CPython raised but the runnable twin
        returned a value (a fidelity gap); `prov_silent` those where the provable twin's total model gave
        a default instead (a proof there says nothing about the crash)."""
        import dataclasses

        from .refute.floatreport import float_report

        text, _ = _resolve_source(source, path, name)
        reports = float_report(text, session=_STATE.session(), samples=samples, seed=seed)
        return {"functions": [{**dataclasses.asdict(r), "median_width": r.median_width} for r in reports]}

    @server.tool()
    def run_differential(source: str | None = None, path: str | None = None, name: str = "program",
                         stdin: str = "", timeout: float = 120.0) -> dict[str, Any]:
        """Run the program under CPython and as PastaLean's runnable twin, and compare stdout.
        The program needs a `main()` / `if __name__ == "__main__":` block that prints results;
        add one exercising the inputs you care about (edge cases, suspected counterexamples)."""
        from .pyexec import run_python

        text, py_path = _resolve_source(source, path, name)
        shim_dir = WORKSPACE / "_shim"
        shim_dir.mkdir(parents=True, exist_ok=True)
        (shim_dir / "contracts.py").write_text(
            "from pastalean.transpile.contract_passta import *  # noqa: F401,F403\n", encoding="utf-8")
        py = run_python(text, stdin=stdin, timeout=timeout, extra_paths=[shim_dir])
        result = _STATE.session().translate(text, filepath=py_path, mode="run")
        if not result.ok:
            return {"ok": False, "stage": "translate", "error": result.error,
                    "python": {"stdout": py.stdout, "stderr": py.stderr[-2000:], "ok": py.ok}}
        lean = lean_tools.run_program(result.lean_code, stdin=stdin, timeout=timeout)
        return {
            "ok": True,
            "match": py.ok and lean.ok and py.stdout.strip() == lean.stdout.strip(),
            "degraded": result.degraded,
            "python": {"ok": py.ok, "stdout": py.stdout[-4000:], "stderr": py.stderr[-2000:]},
            "lean": {"ok": lean.ok, "stdout": lean.stdout[-4000:], "stderr": lean.stderr[-2000:]},
        }

    @server.tool()
    def typecheck_python(source: str | None = None, path: str | None = None,
                         name: str = "program") -> dict[str, Any]:
        """Type-check Python with PastaLean's checker (TypeInfer). Reports annotations contradicted
        by how values are used; silent on what it cannot fully understand (no false alarms on
        known-good code). No annotations required."""
        from .typeinfer.check import check_paths, to_lines

        _, py_path = _resolve_source(source, path, name)
        diags = check_paths([str(py_path)], jobs=1)
        return {"ok": not diags, "count": len(diags), "diagnostics": to_lines(diags)}

    @server.tool()
    def get_guide(topic: str = "contracts") -> str:
        """Reference material. topic: "contracts" (how to write Requires/Ensures/Invariant that
        PastaLean can prove), "proving" (proof patterns for the emitted Lean), "verifiable_design"
        (restructuring Python to be provable), "contract_qa" (common contract mistakes)."""
        p = GUIDES.get(topic)
        if p is None:
            return f"unknown topic {topic!r}; choose from {sorted(GUIDES)}"
        return p.read_text(encoding="utf-8")

    @server.tool()
    def list_proved_examples(query: str = "") -> list[dict[str, str]]:
        """Fully proved worked examples (Python with contracts -> Lean -> sorry-free proof).
        query filters by name or by text in the proof (e.g. "mvcgen", "pyRange", "all(")."""
        out = []
        for name, py, lean in _examples():
            text = lean.read_text(encoding="utf-8")
            if query and query.lower() not in (name + text + py.read_text(encoding="utf-8")).lower():
                continue
            out.append({"name": name, "monadic": str("mvcgen" in text), "lean": str(lean.relative_to(REPO_ROOT))})
        return out

    @server.tool()
    def get_example(name: str) -> dict[str, str]:
        """One proved example: its contracted Python source and the Lean with the complete proof."""
        for ex_name, py, lean in _examples():
            if ex_name == name:
                return {"python": py.read_text(encoding="utf-8"), "lean": lean.read_text(encoding="utf-8")}
        return {"error": f"no proved example named {name!r}; see list_proved_examples"}

    @server.tool()
    def search_lemmas(pattern: str, limit: int = 40) -> list[str]:
        """Search the PastaLean runtime and Libraries for theorems/lemmas/@[spec]/@[simp] facts whose
        declaration line matches the regex `pattern` (e.g. "pyRange_forIn", "pyLen.*append").
        Returns `file:line: declaration`."""
        rx = re.compile(pattern)
        hits: list[str] = []
        for root in LEMMA_ROOTS:
            for f in sorted((REPO_ROOT / root).rglob("*.lean")):
                lines = f.read_text(encoding="utf-8", errors="replace").splitlines()
                for i, line in enumerate(lines):
                    if _THEOREM_RE.match(line.strip()) and rx.search(line):
                        hits.append(f"{f.relative_to(REPO_ROOT)}:{i + 1}: {line.strip()}")
                        if len(hits) >= limit:
                            return hits
        return hits

    @server.tool()
    def find_definition(name: str, limit: int = 5) -> list[dict[str, str]]:
        """Source of a Lean declaration in the PastaLean runtime or Libraries, by name or dotted
        suffix (e.g. "pyAppend", "PyLen.pyLen", "pyRange_forIn"): what a function in a goal
        actually computes, or what a lemma states. Returns file, line and the declaration text."""
        short = name.split(".")[-1]
        rx = re.compile(r"^(?:@\[[^\]]*\]\s*)*(?:\w+\s+)*(?:def|theorem|lemma|abbrev|instance|class|"
                        r"structure|inductive|opaque)\s+(?:[\w.']*\.)?" + re.escape(short) + r"(?![\w'])")
        found = []
        for root in LEMMA_ROOTS:
            for f in sorted((REPO_ROOT / root).rglob("*.lean")):
                lines = f.read_text(encoding="utf-8", errors="replace").splitlines()
                for i, line in enumerate(lines):
                    if line[:1].isspace() or not rx.match(line):
                        continue
                    j = i + 1
                    while j < len(lines) and j - i < 60 and (not lines[j].strip() or lines[j][:1].isspace()):
                        j += 1
                    found.append({"file": str(f.relative_to(REPO_ROOT)), "line": str(i + 1),
                                  "source": "\n".join(lines[i:j]).rstrip()})
                    if len(found) >= limit:
                        return found
        return found

    @server.tool()
    def grep_source(pattern: str, path_prefix: str = "PastaLean", limit: int = 60) -> list[str]:
        """Regex search over repository sources (.lean/.md/.py) under `path_prefix` (one of
        PastaLean, Libraries, TypeInfer, docs, PastaBench, example_scripts, src, or a subpath such
        as "PastaLean/PyAPI"). Returns `file:line: text`."""
        try:
            base = _browse_path(path_prefix)
        except ValueError as err:
            return [str(err)]
        rx = re.compile(pattern)
        files = [base] if base.is_file() else sorted(base.rglob("*"))
        hits: list[str] = []
        for f in files:
            if not f.is_file() or f.suffix not in BROWSE_SUFFIXES:
                continue
            for i, line in enumerate(f.read_text(encoding="utf-8", errors="replace").splitlines()):
                if rx.search(line):
                    hits.append(f"{f.relative_to(REPO_ROOT)}:{i + 1}: {line.strip()[:200]}")
                    if len(hits) >= limit:
                        return hits
        return hits

    @server.tool()
    def read_source(path: str, start: int = 1, end: int = 200) -> str:
        """Read lines [start, end] of a repository source file (.lean/.md/.py), e.g. a file
        returned by find_definition or grep_source. At most 400 lines per call."""
        try:
            f = _browse_path(path)
        except ValueError as err:
            return str(err)
        if not f.is_file() or f.suffix not in BROWSE_SUFFIXES:
            return f"not a readable source file: {path}"
        lines = f.read_text(encoding="utf-8", errors="replace").splitlines()
        start = max(1, start)
        end = min(len(lines), end, start + 399)
        return "\n".join(f"{n:5d}  {lines[n - 1]}" for n in range(start, end + 1))

    return server


def _browse_path(path: str) -> Path:
    """Resolve a repo-relative path, refusing anything outside the browsable roots."""
    p = (REPO_ROOT / path).resolve()
    if not p.is_relative_to(REPO_ROOT.resolve()):
        raise ValueError(f"{path!r} is outside the repository")
    rel = p.relative_to(REPO_ROOT.resolve())
    if not rel.parts or rel.parts[0] not in BROWSE_ROOTS:
        raise ValueError(f"{path!r} is outside the browsable roots {BROWSE_ROOTS}")
    return p


def _fidelity(original: str, edited: str) -> dict[str, Any]:
    """Every `def` of the translation must survive verbatim and every theorem keep its statement;
    only proofs may change and helper lemmas may be added."""
    edited_decls = {q: (k, t) for k, q, t in _declarations(edited)}
    changed = []
    original_lines = {_norm(line) for line in original.splitlines()}
    for i, line in enumerate(edited.splitlines(), 1):
        if _norm(line) in original_lines:
            continue
        if _FORBIDDEN_DECL_RE.match(line) or _FORBIDDEN_ANYWHERE_RE.search(line):
            changed.append(f"line {i}: only theorems/lemmas may be added, found `{line.strip()[:80]}`")
    for kind, qual, text in _declarations(original):
        now = edited_decls.get(qual)
        if now is None:
            changed.append(f"{qual}: removed")
        elif kind in ("theorem", "lemma"):
            if _statement(now[1]) != _statement(text):
                changed.append(f"{qual}: statement changed")
        elif _norm(now[1]) != _norm(text):
            changed.append(f"{qual}: definition changed")
    return {"checked": True, "ok": not changed, "changed": changed}


def _examples():
    """`(name, contracted_python, proved_lean)` for every sorry-free worked example."""
    for root in EXAMPLE_ROOTS:
        for d in sorted(p for p in root.iterdir() if p.is_dir()):
            py, lean = d / "solution_contracts.py", d / "Proofs.lean"
            if py.exists() and lean.exists() and not re.search(r"\bsorry\b", lean.read_text(encoding="utf-8")):
                yield d.name, py, lean
    for lean in sorted(PLAYGROUND.glob("*.lean")):
        py = lean.with_suffix(".py")
        if py.exists() and not re.search(r"\bsorry\b", lean.read_text(encoding="utf-8")):
            yield f"playground/{lean.stem}", py, lean


def serve() -> None:
    build_server().run("stdio")

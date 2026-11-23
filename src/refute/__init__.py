"""Counterexamples to a program's contracts and properties, found in Lean and confirmed in all three worlds.

`refute_source(source)`:

1. finds the obligations (`obligations.collect`) and writes a checker for each;
2. translates the program plus checkers once in `both` mode;
3. searches in both Lean worlds (the backend `refute` task, the `refute?` machinery), certifying a
   provable refutation with the kernel;
4. executes each witness Lean found once under CPython (no search on the Python side);
5. classifies each witness (`classify`) and keeps the most telling one per obligation.
"""

from __future__ import annotations

import logging
import json
import os
import subprocess
import sys
import threading
import time
from dataclasses import dataclass, field
from pathlib import Path

from . import obligations as O
from .pylit import py_repr

# witnesses travel as JSON text: an exact big integer (`fib(100000)`) must not hit the 4300-digit limit
if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)

logger = logging.getLogger(__name__)

__all__ = ["refute_source", "refute_file", "RefuteReport", "ObligationReport", "VERDICT_ORDER"]

NS = "PastaLean.User.Root."
HARNESS = Path(__file__).with_name("harness.py")

#: Most telling first: a genuine refutation beats a divergence, which beats an inconclusive witness.
VERDICT_ORDER = ["REFUTED", "PROGRAM_DIFF", "PARTIALITY_GAP", "FLOAT_ONLY", "ROUNDING_SENSITIVE", "TWIN_DIVERGENCE_PROVABLE", "FIDELITY_BUG",
                 "RUN_TWIN_BUG", "ENCLOSURE_VIOLATION",
                 "PROVABLE_TWIN_DIVERGENCE", "PRECONDITION_MISMATCH", "NONTERMINATION",
                 "INCONCLUSIVE"]

EXPLAIN = {
    "REFUTED": "fails in the provable twin, the runnable twin and CPython: the function or its spec is wrong",
    "FLOAT_ONLY": "true over exact ℚ but false in IEEE floats (runnable twin and CPython): a ℚ proof would hide a real float bug",
    "ROUNDING_SENSITIVE": "true over exact ℚ, false in IEEE floats, and the proved rounding enclosure cannot decide it: a rounding effect, so a ℚ proof says nothing about the float program",
    "ENCLOSURE_VIOLATION": "CPython's float result left the proved IEEE enclosure: a gap in the enclosure model itself (e.g. an unmodelled operation)",
    "TWIN_DIVERGENCE_PROVABLE": "fails only in the provable twin: its exact model (e.g. x/0 = 0) is stricter than Python",
    "FIDELITY_BUG": "the Lean twins disagree with CPython: PastaLean translates this program unfaithfully",
    "RUN_TWIN_BUG": "the runnable twin disagrees with the provable twin and CPython",
    "PROVABLE_TWIN_DIVERGENCE": "the provable twin disagrees with the runnable twin and CPython",
    "PRECONDITION_MISMATCH": "the worlds disagree on whether the input satisfies the precondition",
    "NONTERMINATION": "the input made some world run past its deadline",
    "INCONCLUSIVE": "some world could not evaluate the input",
    "PROGRAM_DIFF": "the program and the reference print differently on this input",
    "PROVED": "no counterexample exists: grind or taste? proved the property for every input satisfying the precondition (provable twin)",
    "PARTIALITY_GAP": "Python raises here, but the provable twin's total model returns a default value instead (e.g. x // 0 = 0), so the theorem can hold, and be proved, although the program crashes on this input",
}


def world_state(j: dict | None) -> str:
    """`violates` / `holds` / `vacuous` / `timeout` / `unknown` from one world's judgement."""
    if not j:
        return "unknown"
    if j.get("exc") == "Timeout":
        return "timeout"
    # a contract over the function's locals (`Ensures(base ** Result() >= n)`) cannot be evaluated
    # outside it: a `NameError` there says nothing about the program
    if j.get("exc") in ("MemoryError", "NameError"):
        return "unknown"
    if j.get("guard") is False:
        return "vacuous"
    if j.get("guard") is True:
        if j.get("exc") or j.get("holds") is False:
            return "violates"
        if j.get("holds") is True:
            return "holds"
    return "unknown"


def refine_with_interval(verdict: str | None, interval: str | None, prov: str, py: str) -> str | None:
    """Use the IEEE enclosure judgement on a float witness. The enclosure contains both the exact value and
    every IEEE result, so when it decides, CPython (IEEE exactly) must agree, and so must the exact-ℚ twin
    unless its model departs from real arithmetic (e.g. `x/0 = 0`). When it cannot decide, a flip between
    the exact and float worlds is ordinary rounding."""
    if interval is None or verdict is None:
        return verdict
    decided = interval in ("holds", "violates")
    if decided and py in ("holds", "violates") and interval != py:
        return "ENCLOSURE_VIOLATION"
    if decided and prov in ("holds", "violates") and interval != prov:
        return "PROVABLE_TWIN_DIVERGENCE" if prov != py else verdict
    if interval == "rounding" and verdict == "FLOAT_ONLY":
        return "ROUNDING_SENSITIVE"
    return verdict


def classify(prov: str, run: str, py: str) -> str | None:
    """The verdict on one witness, or `None` when no world sees a violation."""
    worlds = (prov, run, py)
    if "violates" not in worlds and "timeout" not in worlds:
        return None
    if "timeout" in worlds:
        return "NONTERMINATION"
    live = [w for w in worlds if w != "unavailable"]
    if len(live) < 3:
        # A world that cannot run at all (e.g. a twin that does not elaborate) is left out; the two that
        # remain (always CPython and one Lean twin) must both see the violation.
        return "REFUTED" if len(live) >= 2 and all(w == "violates" for w in live) else "INCONCLUSIVE"
    if "unknown" in worlds:
        return "INCONCLUSIVE"
    if "vacuous" in worlds:
        return "PRECONDITION_MISMATCH"
    if worlds == ("violates", "violates", "violates"):
        return "REFUTED"
    if worlds == ("holds", "violates", "violates"):
        return "FLOAT_ONLY"
    if worlds == ("violates", "holds", "holds"):
        return "TWIN_DIVERGENCE_PROVABLE"
    if prov == run != py:
        return "FIDELITY_BUG"
    if prov == py != run:
        return "RUN_TWIN_BUG"
    return "PROVABLE_TWIN_DIVERGENCE"


@dataclass
class Witness:
    origin: str
    lits: list
    prov: str
    run: str
    py: str
    verdict: str | None
    exc: str | None = None
    interval: str | None = None
    explain: dict | None = None     # contract: what the function returned, which `Ensures` it breaks

    @property
    def python(self) -> list[str]:
        return [py_repr(l) for l in self.lits]


@dataclass
class ObligationReport:
    name: str
    kind: str
    theorem: str | None
    params: list[str]
    verdict: str
    witness: Witness | None = None
    kernel_proof: str | None = None
    witnesses: list[Witness] = field(default_factory=list)
    searches: dict = field(default_factory=dict)
    error: str | None = None

    def witness_text(self) -> str:
        if self.witness is None:
            return ""
        return ", ".join(f"{n} = {v}" for n, v in zip(self.params, self.witness.python))


@dataclass
class RefuteReport:
    obligations: list[ObligationReport]
    lean_code: str | None = None
    error: str | None = None

    @property
    def found(self) -> bool:
        return any(o.verdict in VERDICT_ORDER for o in self.obligations)


def _run_harness(module: str, obs: list[O.Obligation], witnesses: dict[str, list], *, per_case_ms: int,
                 timeout: float) -> dict:
    """Execute the given witnesses under CPython (`harness.py`); it never generates inputs."""
    req = {"module": module, "perCaseMs": per_case_ms,
           "obligations": [{"name": o.name, "kind": o.kind, "params": o.params, "pre": o.pre,
                            "chk": o.chk, "pre_fn": o.pre_fn, "chk_fn": o.chk_fn, "ensures": o.ensures,
                            "raises": o.raises, "lets": o.lets, "witnesses": witnesses.get(o.name, [])}
                           for o in obs]}
    try:
        p = subprocess.run([sys.executable, str(HARNESS)], input=json.dumps(req), capture_output=True,
                           text=True, timeout=timeout, cwd=str(HARNESS.parent))
    except subprocess.TimeoutExpired:
        return {"error": "CPython harness timed out"}
    if p.returncode != 0:
        return {"error": (p.stderr or p.stdout).strip()[-2000:]}
    return json.loads(p.stdout)


#: Per-thread context the refute daemon (`daemon.py`) sets for each request it serves: the warm `session`
#: to use when a call is given none, and `env` overrides (`PASTALEAN_REFUTE_CONFIG`) of the caller.
REQUEST = threading.local()


def _request_session():
    return getattr(REQUEST, "session", None)


def _request_env(name: str, default: str) -> str:
    return getattr(REQUEST, "env", {}).get(name, os.environ.get(name, default))


def refute_source(source: str, *, session=None, seed: int = 24301, time_ms: int | None = None,
                  per_case_ms: int = 1000, only: str | None = None, tests: int = 1000,
                  equiv: list[tuple[str, str]] | None = None) -> RefuteReport:
    """Search for counterexamples to every obligation in `source`, in Lean only, and classify each one
    across the worlds. Python supplies the program and its contracts; the search runs over the
    translated twins (the `refute?` machinery), and CPython only executes the witnesses Lean found, as
    the ground truth the twins are checked against. A program PastaLean cannot translate is reported as
    such. `tests` is the Lean search's count of guard-satisfying inputs per world; `equiv` adds a
    property `f(x) == g(x)` per pair, guarded by `f`'s `Requires`."""
    from ..api import Session

    if time_ms is None:
        time_ms = 4000 + tests // 2
    started = time.monotonic()
    if equiv:
        source = source.rstrip() + "\n" + "".join(O.equiv_source(source, f, g) for f, g in equiv)
    obs = [o for o in O.collect(source) if only is None or o.name == only or o.theorem == only]
    if not obs:
        return RefuteReport([], error="no property functions or contracts found")
    program = O.asserts_raise(source, obs)
    O.refine_params(program, obs)
    cpy_module = O.cpython_module(source, obs)
    own = session is None and _request_session() is None
    sess = session or _request_session() or Session(target="command", mode="both")
    try:
        res = sess.translate(O.lean_module(program, obs), prove_asserts=False)
        if not res.ok:
            return RefuteReport([], error=f"PastaLean cannot translate this program, so refute cannot search it: "
                                          f"{(res.error or '')[:300]}")
        code = res.lean_code
        targets = []
        for o in obs:
            t = {"id": o.name, "provPre": NS + o.pre_fn, "provChk": NS + o.chk_fn,
                 "runPre": NS + o.pre_fn + "'rn", "runChk": NS + o.chk_fn + "'rn", "raises": [r.rsplit(".", 1)[-1] for r in o.raises]}
            if o.theorem and (f"theorem {o.theorem} " in code or f"theorem {o.theorem}\n" in code):
                t["theorem"] = NS + o.theorem
            targets.append(t)
        # `time_ms` is the whole run's budget per obligation; the two worlds search one after the other.
        left_ms = time_ms * len(obs) - (time.monotonic() - started) * 1000
        per_world = int(max(0, left_ms) / max(1, len(obs)) * 0.45)
        config = {"seed": seed, "timeMs": max(per_world, 300), "perCaseMs": per_case_ms, "numInst": tests,
                  # experiments: e.g. {"plausible": false, "solver": false} to measure one engine alone
                  **json.loads(_request_env("PASTALEAN_REFUTE_CONFIG", "{}"))}
        lean_out = sess.client.refute(code, targets, [], config) or {}
        if not lean_out.get("result") and not lean_out.get("error"):
            # The backend died, typically out of memory on a drawn table size (`[0] * (10**9 + 7)`):
            # once more with generated integers kept small.
            logger.warning("the Lean backend stopped during the search; retrying with small integers")
            lean_out = sess.client.refute(code, targets, [], {**config, "intCap": 1000}) or {}
        if not lean_out.get("result"):
            return RefuteReport([], lean_code=code, error=f"Lean refute task failed: {lean_out.get('error')}")
        if lean_out.get("errors"):
            logger.warning("the translated program has Lean errors in the refute run: %s",
                           "; ".join(lean_out["errors"]))
        if lean_out.get("instanceErrors"):
            logger.warning("generators for the program's classes failed to elaborate: %s",
                           "; ".join(lean_out["instanceErrors"]))
        lean_by_id = {t["id"]: t for t in lean_out.get("targets", [])}
        # A non-terminating evaluation leaves its thread spinning in the backend; restart it.
        if any((t.get(w) or {}).get("hang") for t in lean_out.get("targets", []) for w in ("prov", "run")) \
                or any(t.get("judgeHang") for t in lean_out.get("targets", [])):
            sess.client.close()

        # Each witness Lean found, executed once under CPython.
        to_judge = {o.name: [w["lits"] for w in lean_by_id.get(o.name, {}).get("witnesses", [])] for o in obs}
        judged = _run_harness(cpy_module, obs, to_judge, per_case_ms=per_case_ms,
                              timeout=60 + 5 * sum(map(len, to_judge.values())))
        py_judged = {o["id"]: o.get("judged", []) for o in judged.get("obligations", [])}

        reports = []
        for o in obs:
            lt = lean_by_id.get(o.name, {})
            ws = []
            for lw, pj in zip(lt.get("witnesses", []), py_judged.get(o.name, [])):
                prov = world_state(lw.get("prov") or lw.get("provChk"))
                run = world_state(lw.get("run"))
                # A twin whose search could not even start (it does not elaborate) is unavailable.
                if run == "unknown" and "error" in (lt.get("run") or {}):
                    run = "unavailable"
                if prov == "unknown" and "error" in (lt.get("prov") or {}):
                    prov = "unavailable"
                py = world_state(pj)
                verdict = refine_with_interval(classify(prov, run, py), pj.get("interval"), prov, py)
                provj = lw.get("prov") or lw.get("provChk") or {}
                if prov == "holds" and py == "violates" and provj.get("panic") and provj["panic"] == pj.get("exc"):
                    verdict = "PARTIALITY_GAP"
                ws.append(Witness(lw.get("origin"), lw["lits"], prov, run, py, verdict, pj.get("exc"),
                                  pj.get("interval"), pj.get("explain")))
            # A witness that only fails with a TypeError is a type confusion (a str where a list was meant):
            # real, but a violation on well-typed input says more, so it leads.
            ranked = sorted((w for w in ws if w.verdict), key=lambda w: (VERDICT_ORDER.index(w.verdict),
                                                                          w.exc == "TypeError",
                                                                          len(json.dumps(w.lits))))
            best = ranked[0] if ranked else None
            proof = None
            certs = lt.get("certifiedAll") or []
            if best is not None and best.verdict == "REFUTED" and certs:
                mine = next((c for c in certs if c.get("lits") == best.lits), None)
                if mine is not None:
                    proof = mine["proof"]
                else:
                    # Lead with a certified witness instead, unless that one is only a type confusion.
                    for c in certs:
                        other = next((w for w in ws if w.lits == c.get("lits")), None)
                        if other is not None and other.verdict == "REFUTED" and \
                                (other.exc != "TypeError" or best.exc == "TypeError"):
                            best, proof = other, c["proof"]
                            break
            solver = lt.get("solver") or {}
            verdict = best.verdict if best else ("PROVED" if solver.get("status") == "proved" else "NO_COUNTEREXAMPLE")
            reports.append(ObligationReport(
                o.name, o.kind, o.theorem if "theorem" in next((t for t in targets if t["id"] == o.name), {}) else None,
                [n for n, _ in o.params], verdict, best, proof, ws,
                {"prov": lt.get("prov") or {}, "run": lt.get("run") or {}, "solver": solver},
                lt.get("error") or judged.get("error")))
        return RefuteReport(reports, lean_code=code)
    finally:
        if own:
            sess.close()


def refute_file(path: str | Path, **kw) -> RefuteReport:
    return refute_source(Path(path).read_text(encoding="utf-8"), **kw)

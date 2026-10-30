"""Counterexamples to a program's contracts and properties, confirmed in all three worlds.

`refute_source(source)`:

1. finds the obligations (`obligations.collect`) and writes a checker for each;
2. translates the program plus checkers once in `both` mode;
3. searches on the CPython side (`harness.py`: enumeration, precondition-directed hill climbing,
   Hypothesis) and in both Lean worlds (the backend `refute` task: enumeration + random, with the
   provable refutation certified by the kernel);
4. judges every witness, whoever found it, in the provable twin, the runnable twin and CPython;
5. classifies each witness (`classify`) and keeps the most telling one per obligation.
"""

from __future__ import annotations

import json
import subprocess
import sys
from dataclasses import dataclass, field
from pathlib import Path

from . import obligations as O
from .pylit import py_repr

__all__ = ["refute_source", "refute_file", "RefuteReport", "ObligationReport", "VERDICT_ORDER"]

NS = "PastaLean.User.Root."
HARNESS = Path(__file__).with_name("harness.py")

#: Most telling first: a genuine refutation beats a divergence, which beats an inconclusive witness.
VERDICT_ORDER = ["REFUTED", "PROGRAM_DIFF", "PARTIALITY_GAP", "FLOAT_ONLY", "ROUNDING_SENSITIVE", "TWIN_DIVERGENCE_PROVABLE", "FIDELITY_BUG",
                 "RUN_TWIN_BUG", "ENCLOSURE_VIOLATION",
                 "PROVABLE_TWIN_DIVERGENCE", "PRECONDITION_MISMATCH", "NONTERMINATION", "CPYTHON_ONLY",
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
    "CPYTHON_ONLY": "false under CPython; the Lean twins could not evaluate it (see the error), so the finding is not cross-checked",
    "PARTIALITY_GAP": "Python raises here, but the provable twin's total model returns a default value instead (e.g. x // 0 = 0), so the theorem can hold, and be proved, although the program crashes on this input",
}


def world_state(j: dict | None) -> str:
    """`violates` / `holds` / `vacuous` / `timeout` / `unknown` from one world's judgement."""
    if not j:
        return "unknown"
    if j.get("exc") == "Timeout":
        return "timeout"
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


def _run_harness(module: str, obs: list[O.Obligation], witnesses: dict[str, list], *, search: bool,
                 seed: int, search_ms: int, per_case_ms: int, timeout: float, tests: int = 1000) -> dict:
    req = {"module": module, "search": search, "seed": seed, "searchMs": search_ms,
           "perCaseMs": per_case_ms, "tests": tests,
           "obligations": [{"name": o.name, "kind": o.kind, "params": o.params, "pre": o.pre,
                            "chk": o.chk, "pre_fn": o.pre_fn, "chk_fn": o.chk_fn, "ensures": o.ensures,
                            "lets": o.lets,
                            "witnesses": witnesses.get(o.name, [])} for o in obs]}
    try:
        p = subprocess.run([sys.executable, str(HARNESS)], input=json.dumps(req), capture_output=True,
                           text=True, timeout=timeout, cwd=str(HARNESS.parent))
    except subprocess.TimeoutExpired:
        return {"error": "CPython harness timed out"}
    if p.returncode != 0:
        return {"error": (p.stderr or p.stdout).strip()[-2000:]}
    return json.loads(p.stdout)


def refute_source(source: str, *, session=None, seed: int = 24301, time_ms: int | None = None,
                  per_case_ms: int = 1000, only: str | None = None, cpython_search: bool = True,
                  lean_search: bool = True, tests: int = 1000,
                  equiv: list[tuple[str, str]] | None = None) -> RefuteReport:
    """Search for counterexamples to every obligation in `source` and classify them across worlds.
    `tests` is how many precondition-satisfying inputs each search runs (rejected draws do not count);
    `equiv` adds a property `f(x) == g(x)` per pair, guarded by `f`'s `Requires`."""
    from ..api import Session

    if time_ms is None:
        time_ms = 4000 + tests // 2
    if equiv:
        source = source.rstrip() + "\n" + "".join(O.equiv_source(source, f, g) for f, g in equiv)
    obs = [o for o in O.collect(source) if only is None or o.name == only or o.theorem == only]
    if not obs:
        return RefuteReport([], error="no property functions or contracts found")
    own = session is None
    sess = session or Session(target="command", mode="both")
    try:
        res = sess.translate(O.lean_module(source, obs), prove_asserts=False)
        if not res.ok:
            return RefuteReport([], error=f"translation failed: {res.error}")
        code = res.lean_code
        cpy_module = O.cpython_module(source, obs)

        # CPython-side search first: its witnesses are then judged by both Lean worlds as well.
        found = _run_harness(cpy_module, obs, {}, search=cpython_search, seed=seed, search_ms=time_ms,
                             per_case_ms=per_case_ms, timeout=time_ms / 1000 * len(obs) * 1.5 + 60,
                             tests=tests)
        py_found = {o["id"]: (o.get("search") or {}) for o in found.get("obligations", [])}

        targets, given = [], []
        for o in obs:
            t = {"id": o.name, "provPre": NS + o.pre_fn, "provChk": NS + o.chk_fn,
                 "runPre": NS + o.pre_fn + "'rn", "runChk": NS + o.chk_fn + "'rn"}
            if o.theorem and (f"theorem {o.theorem} " in code or f"theorem {o.theorem}\n" in code):
                t["theorem"] = NS + o.theorem
            targets.append(t)
            lits = py_found.get(o.name, {}).get("lits")
            if lits:
                given.append({"target": o.name, "lits": lits})
            # Valid inputs CPython passed, re-checked in both twins: a twin failing one is a divergence.
            given += [{"target": o.name, "lits": s} for s in py_found.get(o.name, {}).get("samples") or []]
        config = {"seed": seed, "timeMs": time_ms, "perCaseMs": per_case_ms, "numInst": tests}
        if not lean_search:
            config.update({"numInst": 0, "enumDepth": 0})
        lean = sess.client.refute(code, targets, given, config) or {}
        if not lean.get("result"):
            return RefuteReport([], lean_code=code, error=f"Lean refute task failed: {lean.get('error')}")
        lean_by_id = {t["id"]: t for t in lean.get("targets", [])}
        # A non-terminating evaluation leaves its thread spinning in the backend; restart it.
        if any((t.get(w) or {}).get("hang") for t in lean.get("targets", []) for w in ("prov", "run")):
            sess.client.close()

        # Every witness through CPython.
        to_judge = {o.name: [w["lits"] for w in lean_by_id.get(o.name, {}).get("witnesses", [])] for o in obs}
        # A CPython witness the Lean side never judged (e.g. the twins do not elaborate) is still judged here.
        extra = {}
        for o in obs:
            lits = py_found.get(o.name, {}).get("lits")
            if lits and lits not in to_judge[o.name]:
                extra[o.name] = lits
                to_judge[o.name].append(lits)
        judged = _run_harness(cpy_module, obs, to_judge, search=False, seed=seed, search_ms=0,
                              per_case_ms=per_case_ms, timeout=60 + 5 * sum(map(len, to_judge.values())))
        py_judged = {o["id"]: o.get("judged", []) for o in judged.get("obligations", [])}

        reports = []
        for o in obs:
            lt = lean_by_id.get(o.name, {})
            ws = []
            for lw, pj in zip(lt.get("witnesses", []), py_judged.get(o.name, [])):
                prov = world_state(lw.get("prov") or lw.get("provChk"))
                run = world_state(lw.get("run"))
                py = world_state(pj)
                origin = lw.get("origin")
                if origin == "given":
                    origin = "cpython:" + (py_found.get(o.name, {}).get("engine") or "sample")
                verdict = refine_with_interval(classify(prov, run, py), pj.get("interval"), prov, py)
                provj = lw.get("prov") or lw.get("provChk") or {}
                if prov == "holds" and py == "violates" and provj.get("panic") and provj["panic"] == pj.get("exc"):
                    verdict = "PARTIALITY_GAP"
                ws.append(Witness(origin, lw["lits"], prov, run, py, verdict, pj.get("exc"), pj.get("interval"),
                                  pj.get("explain")))
            if o.name in extra:
                pj = py_judged.get(o.name, [])[len(ws):len(ws) + 1]
                pj = pj[0] if pj else {}
                if world_state(pj) == "violates":
                    ws.append(Witness("cpython:" + (py_found[o.name].get("engine") or "?"), extra[o.name],
                                      "unknown", "unknown", "violates", "CPYTHON_ONLY", pj.get("exc"),
                                      pj.get("interval"), pj.get("explain")))
            ranked = sorted((w for w in ws if w.verdict), key=lambda w: (VERDICT_ORDER.index(w.verdict),
                                                                          len(json.dumps(w.lits))))
            best = ranked[0] if ranked else None
            prov_search = lt.get("prov") or {}
            cert = lt.get("certified") or {}
            # A kernel-checked refutation for any witness the provable twin rejects: prefer the one the
            # report shows, else whichever was certified.
            proof = None
            if best is not None and best.verdict == "REFUTED" and cert.get("proof"):
                proof = cert["proof"]
                if cert.get("lits") != best.lits:
                    certified = next((w for w in ws if w.lits == cert.get("lits")), None)
                    if certified is not None and certified.verdict == "REFUTED":
                        best = certified
            reports.append(ObligationReport(
                o.name, o.kind, o.theorem if "theorem" in next(t for t in targets if t["id"] == o.name) else None,
                [n for n, _ in o.params], best.verdict if best else "NO_COUNTEREXAMPLE", best, proof, ws,
                {"prov": prov_search, "run": lt.get("run") or {}, "cpython": py_found.get(o.name, {})},
                lt.get("error") or found.get("error")))
        return RefuteReport(reports, lean_code=code)
    finally:
        if own:
            sess.close()


def refute_file(path: str | Path, **kw) -> RefuteReport:
    return refute_source(Path(path).read_text(encoding="utf-8"), **kw)

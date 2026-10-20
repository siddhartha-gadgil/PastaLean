"""Render a certificate as a Lean file whose compilation IS its certificate check.

`--verify-cert` re-checks a certificate by running `TypeInfer.validate` — a program checking a
program. This module writes the same claim as Lean source, so the checker is Lean's own kernel:

    theorem f_replay : replayOk fCert = true := by cert_replay fCert
    theorem f_welltyped : CertSound fCert := replay_sound fCert f_replay

`CertSound` is the semantic statement (`TypeInfer/Theorem/Certificate.lean`): wherever the
certificate says a slot's uses narrow to `t`, every runtime value of type `t` satisfies every one of
those uses. `replay_sound` is proved once, there; this file supplies the witness it applies to.

**What the emitted file checks, and what it does not.** It checks the certificate-internal half —
`replayOk`. It does *not* check that the certificate is about a particular program: the identity hash
and the declaration grounding do not reduce in the kernel (`String.hash` is an `extern`, and hash-map
lookups do not evaluate there), so that half stays with `--verify-cert`. The generated file says so
in its own header rather than leaving a reader to assume otherwise.
"""

from __future__ import annotations

import json
from pathlib import Path

_SCALARS = {"?": ".unknown", "any": ".any", "int": ".int", "bool": ".bool",
            "str": ".str", "float": ".float", "None": ".none"}
_KINDS = {"param": ".param", "return": ".returnType", "local": ".annotatedLocal",
          "call-arg": ".callArgument", "local-var": ".localVariable"}
_ORIGINS = {"body-use": ".bodyUse", "return-body": ".returnBody",
            "value-flow": ".valueFlow", "call-literal": ".callLiteral"}
_DIAGKINDS = {"use-conflict": ".useConflict", "annotation-mismatch": ".annotationMismatch",
              "value-rejected": ".valueRejected"}


def lean_name(stem: str) -> str:
    """A Lean identifier for the certificate of a file called `stem`. Non-identifier characters
    become `_`, and a name that would start with a digit is prefixed — `01_counter.py` is a real
    file name and `def 01_counterCert` is not a declaration."""
    cleaned = "".join(ch if ch.isalnum() else "_" for ch in stem).strip("_")
    if not cleaned:
        return "fileCert"
    return (cleaned if cleaned[0].isalpha() or cleaned[0] == "_" else "f_" + cleaned) + "Cert"


def _lit(s: str) -> str:
    return '"' + s.replace("\\", "\\\\").replace('"', '\\"') + '"'


def _ty(t, paren: bool = False) -> str:
    """One `PyType`, in the certificate's JSON encoding, as Lean source."""
    if isinstance(t, str):
        return _SCALARS[t]
    wrap = (lambda s: f"({s})") if paren else (lambda s: s)
    for key, ctor in (("list", ".list"), ("set", ".set"), ("opt", ".opt")):
        if key in t:
            return wrap(f"{ctor} {_ty(t[key], True)}")
    if "cls" in t:
        return wrap(f".cls {_lit(t['cls'])}")
    if "dict" in t:
        k, v = t["dict"]
        return wrap(f".dict {_ty(k, True)} {_ty(v, True)}")
    if "tuple" in t:
        return wrap(".tuple [" + ", ".join(_ty(e) for e in t["tuple"]) + "]")
    if "fn" in t:
        args = ", ".join(_ty(a) for a in t["fn"])
        return wrap(f".fn [{args}] {_ty(t['ret'], True)}")
    raise ValueError(f"not a certificate type: {t!r}")


def _judgment(j: dict) -> str:
    return ".uses" if j["judgment"] == "uses" else f"(.declared {_ty(j['declared'], True)})"


def _verdict(v: dict) -> str:
    kind = v["verdict"]
    if kind == "commits":
        return f"(.commits {_ty(v['type'], True)})"
    if kind in ("conflict", "rejects"):
        return f"(.{kind} {_ty(v['expected'], True)} {_ty(v['actual'], True)})"
    return f".{kind}"


def _slot(s: dict) -> str:
    ev = ", ".join(f"{{ origin := {_ORIGINS[e['origin']]}, req := {_ty(e['req'], True)} }}"
                   for e in s["evidence"])
    return (f"    {{ scope := {_lit(s['scope'])}, name := {_lit(s['slot'])}, "
            f"kind := {_KINDS[s['kind']]}, line := {s['line']}, col := {s['col']},\n"
            f"      judgment := {_judgment(s['judgment'])},\n"
            f"      evidence := [{ev}],\n"
            f"      verdict := {_verdict(s['verdict'])} }}")


def _diag(d: dict) -> str:
    return (f"    {{ scope := {_lit(d['scope'])}, slot := {_lit(d['slot'])}, "
            f"kind := {_DIAGKINDS[d['kind']]},\n"
            f"      expected := {_ty(d['expected'], True)}, actual := {_ty(d['actual'], True)}, "
            f"line := {d['line']}, col := {d['col']} }}")


def cert_to_lean(cert: dict, name: str, source: str | None = None) -> str:
    """The Lean source for one certificate, ready for `lake env lean`."""
    slots = ",\n".join(_slot(s) for s in cert["slots"]) or "    "
    diags = ",\n".join(_diag(d) for d in cert["diagnostics"]) or "    "
    about = f" for `{source}`" if source else ""
    verdict = "no type error" if cert["ok"] else f"{len(cert['diagnostics'])} type error(s)"
    return f'''import TypeInfer.Theorem.Certificate

/-!
# Certificate{about}

Generated by `pastalean typeinfer --emit-proof`. Checking this file IS checking the certificate:
`cert_replay` discharges `replayOk`, and `replay_sound` — proved once in
`TypeInfer/Theorem/Certificate.lean` — turns that into the semantic statement `CertSound`, namely
that wherever this certificate says a slot's uses narrow to a type, every runtime value of that type
satisfies every one of those uses.

The checker's verdict on the program was: **{verdict}**.

What this file does NOT establish: that the certificate is about any particular program. The identity
hash and the declaration grounding are the other half of `TypeInfer.validate`, and neither reduces in
the kernel (`String.hash` is an `extern`; hash-map lookups do not evaluate there), so that half is
checked by `pastalean typeinfer --verify-cert` instead. The hash is recorded below so the two can be
matched up.
-/

-- A certificate is a flat literal, so the only limits it meets are the default ones on how far
-- `simp` will walk it. A big file's certificate is a few hundred slots.
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

open TypeInfer

/-- The certificate, as the checker produced it. `irHash` names the program it is about. -/
def {name} : Cert :=
  {{ version := {cert["version"]}, irHash := {cert["ir_hash"]}, ok := {str(cert["ok"]).lower()},
    slots :=
      [
{slots}
      ],
    diagnostics :=
      [
{diags}
      ] }}

/-- Every verdict in the certificate follows from the evidence recorded beside it. -/
theorem {name}_replay : replayOk {name} = true := by cert_replay {name}

/-- Hence the semantic statement, by the once-proved `replay_sound`. -/
theorem {name}_sound : CertSound {name} := replay_sound {name} {name}_replay

/-- And every error it reports between two scalar types is a real one: no runtime value inhabits
both. -/
theorem {name}_errors_real :
    ∀ d ∈ {name}.diagnostics, isScalar d.expected = true → isScalar d.actual = true →
      ∀ v : PyType.Val, ¬ (PyType.HasType v d.expected ∧ PyType.HasType v d.actual) :=
  replay_error_sound {name} {name}_replay

#print axioms {name}_sound
#print axioms {name}_errors_real
'''


def write_proof(cert: dict, out: Path, name: str, source: str | None = None) -> Path:
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(cert_to_lean(cert, name, source), encoding="utf-8")
    return out

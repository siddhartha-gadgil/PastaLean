import TypeInfer.Certificate.Basic
import TypeInfer.Certificate.Check

/-!
# Certificates

The checker's positive output. `checkTypes` answers with one boolean; a certificate is the record
behind it — every slot judged, the evidence weighed, the verdict reached — and a validator that
re-checks the whole thing without running inference.

* `Certificate/Basic.lean` — the record (`Cert`, `Slot`, `Evidence`, `Judgment`, `Verdict`) and its
  JSON, written by hand so a certificate is readable.
* `Certificate/Check.lean` — `validate`, which imports nothing from `Solve/`: that is what shrinks
  the trusted base from the engine to a few hundred lines.
* `TypeInfer/Theorem/Certificate.lean` — what an accepted certificate means, and what it does not.
-/

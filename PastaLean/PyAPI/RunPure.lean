import PastaLean.PyAPI.Core
import PastaLean.PyAPI.TasteIngr
import PastaLean.PyAPI.ProofMode.InputM

/-!
# Running a raising computation for its value

A Python operation that can raise is monadic in both twins (`PyProofM` / `PyExcept`). Where a pure value
is required (an `LT`/`Ord` instance for `sorted`, a refute checker's verdict) it is run from an empty
state; an exception becomes Python's runtime error through `pyPanic` (recorded, the value defaulted).
-/

namespace PastaLean

class PyRunPure (β : Type) (α : outParam Type) where
  runPure : β → α

instance (priority := low) {α : Type} : PyRunPure α α := ⟨id⟩

instance {α : Type} : PyRunPure (Id α) α := ⟨Id.run⟩

instance {α : Type} [Inhabited α] : PyRunPure (ProofMode.PyProofM α) α where
  runPure m := match (m.run).run default with
    | (.ok a, _) => a
    | (.error e, _) => pyPanic s!"{e.kind}: {e.msg}"

instance {α : Type} [Inhabited α] : PyRunPure (PyExceptId α) α where
  runPure m := match m.run with
    | .ok a => a
    | .error e => pyPanic s!"{e.kind}: {e.msg}"

private unsafe def runPyExceptUnsafe {α : Type} [Inhabited α] (m : PyExcept α) : α :=
  match unsafeBaseIO m.run.toBaseIO with
  | .ok (.ok a) => a
  | .ok (.error e) => pyPanic s!"{e.kind}: {e.msg}"
  | .error e => pyPanic s!"IOError: {e}"

/-- The runnable twin's `IO`-based exception monad, run for its value. -/
@[implemented_by runPyExceptUnsafe]
opaque runPyExcept {α : Type} [Inhabited α] (m : PyExcept α) : α

instance {α : Type} [Inhabited α] : PyRunPure (PyExcept α) α := ⟨runPyExcept⟩
instance {α : Type} [Inhabited α] : PyRunPure (IO α) α := ⟨fun m => runPyExcept (liftM m)⟩

def runPure {β α : Type} [PyRunPure β α] (x : β) : α := PyRunPure.runPure x

@[simp] theorem runPure_id {α : Type} (x : Id α) : runPure x = x.run := rfl

/-- A pure value runs to itself (a refute checker of a function that cannot raise). -/
@[simp, taste_ingr] theorem runPure_self {α : Type} (x : α) : runPure (α := α) x = x := rfl

end PastaLean

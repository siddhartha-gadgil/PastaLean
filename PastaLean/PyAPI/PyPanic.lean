import PastaLean.Imports

namespace PastaLean

/-- The kind (`IndexError`, …) of the last Python error a runtime function hit. A compiled panic does not
stop the program, so `pastalean refute` resets and reads this around each run to see the error. -/
initialize pyErrorLog : IO.Ref (Option String) ← IO.mkRef none

@[never_extract, noinline]
unsafe def pyPanicImpl {α : Type u} [Inhabited α] (msg : String) : α :=
  let kind := (msg.splitOn ":").headD msg
  -- The message depends on the write, so the write cannot be dropped as dead code.
  panic (unsafeBaseIO (do pyErrorLog.set (some kind); pure msg))

/-- A Python runtime error (`"IndexError: …"`) in pure code: logically `default`, like `panic!`; at run
time it also records the error kind in `pyErrorLog`. -/
@[never_extract, implemented_by pyPanicImpl]
def pyPanic {α : Type u} [Inhabited α] (msg : String) : α := panic msg

end PastaLean

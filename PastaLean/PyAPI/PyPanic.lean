import PastaLean.Imports

namespace PastaLean

/-- Per thread, the kind (`IndexError`, …) of the last Python error a runtime function hit. -/
initialize pyErrorLogs : IO.Ref (Std.HashMap UInt64 String) ← IO.mkRef {}

/-- The kind (`IndexError`, …) of the last Python error a runtime function hit. A compiled panic does not
stop the program, so `pastalean refute` resets and reads this around each run to see the error. Kept per
thread: an evaluation that never terminates keeps its thread, and must not write into the others' runs. -/
structure PyErrorLog where

def pyErrorLog : PyErrorLog := {}

def PyErrorLog.get (_ : PyErrorLog) : BaseIO (Option String) := do
  return (← pyErrorLogs.get)[← IO.getTID]?

def PyErrorLog.set (_ : PyErrorLog) (kind : Option String) : BaseIO Unit := do
  let tid ← IO.getTID
  pyErrorLogs.modify fun m => match kind with | some k => m.insert tid k | none => m.erase tid

def PyErrorLog.swap (log : PyErrorLog) (kind : Option String) : BaseIO (Option String) := do
  let old ← log.get
  log.set kind
  return old

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

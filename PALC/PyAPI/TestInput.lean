import PastaLean.PyAPI.ProofMode.IOStream
import PastaLean.PyAPI.Operators
import PastaLean.PyAPI.Input

open PastaLean

/-- info: 42 -/
#guard_msgs in
#eval pyInt "42"

/-- info: -7 -/
#guard_msgs in
#eval pyInt "  -7  "

/-- info: 5 -/
#guard_msgs in
#eval pyInt (5 : Int)

/-- info: 1 -/
#guard_msgs in
#eval pyInt true

/-- info: 0 -/
#guard_msgs in
#eval pyInt "oops"

-- `IOStream.ofText` (the stdin of a proof-mode `main`): EOF past the last line; a final newline ends it.
#guard (PastaLean.ProofMode.IOStream.ofText "a\nb\n").str 1 == .success "b"
#guard (PastaLean.ProofMode.IOStream.ofText "a\nb\n").str 2 == .error .EndOfFile
#guard (PastaLean.ProofMode.IOStream.ofText "a\nb").str 2 == .error .EndOfFile
#guard (PastaLean.ProofMode.IOStream.ofText "a\n\nb\n").str 1 == .success ""
#guard (PastaLean.ProofMode.IOStream.ofText "").str 0 == .error .EndOfFile
#guard PastaLean.pyFloatDiv 6.0 4.0 == 1.5

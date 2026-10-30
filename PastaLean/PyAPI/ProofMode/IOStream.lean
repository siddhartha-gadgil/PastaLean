import PastaLean.Imports

namespace PastaLean.ProofMode

/-- IO errors that can occur when reading from the input stream. -/
inductive IOError where
  | EndOfFile : IOError
  | ReadError : String → IOError
  deriving Repr, BEq

/-- A result from reading the input stream can be either a successful string or an error. -/
inductive IOResult where
  | success : String → IOResult
  | error : IOError → IOResult
  deriving Repr, BEq

/-- An infinite stream of IOResult values indexed by position.
This models the input available to a program in proof mode.
Each position in the stream can yield either a successful string or an IO error. -/
structure IOStream where
  /-- Current position in the stream (how many inputs have been consumed) -/
  pos : Nat
  /-- The stream function: maps each position to the result at that position -/
  str : Nat → IOResult

namespace IOStream

/-- Get the current element (at position `pos`) from the stream. -/
def head (s : IOStream) : IOResult :=
  s.str s.pos

/-- Advance the stream by one position. -/
def tail (s : IOStream) : IOStream :=
  ⟨s.pos + 1, s.str⟩

/-- The lines of a program's stdin as a stream: `EndOfFile` past the last line, as Python's `input()`
raises `EOFError` there (a final "\n" ends the last line rather than starting an empty one). -/
def ofText (text : String) : IOStream :=
  let lines := text.splitOn "\n"
  let lines := if lines.getLast? == some "" then lines.dropLast else lines
  ⟨0, fun i => if h : i < lines.length then .success lines[i] else .error .EndOfFile⟩

/-- Create a stream from a constant IOResult (repeats forever). -/
def const (r : IOResult) : IOStream :=
  ⟨0, fun _ => r⟩

/-- Create a stream from a function, starting at position 0. -/
def fromFun (f : Nat → IOResult) : IOStream :=
  ⟨0, f⟩

end IOStream

end PastaLean.ProofMode

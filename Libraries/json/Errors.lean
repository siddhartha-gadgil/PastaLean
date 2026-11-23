import PastaLean.PyAPI
import Std.Tactic.Do

open PastaLean
open Std.Do

set_option linter.all false

set_option maxHeartbeats 200000

namespace Libraries.json

/-!
# Python's `json` module

`loads` and `dumps` (`indent`, `sort_keys`, `separators`, `ensure_ascii`), with both twins: the provable
definitions and their `'rn` runnable counterparts, which codegen picks per numeric mode. Derived from
CPython 3.14 `Lib/json/decoder.py`, `scanner.py` and `encoder.py` (Copyright (c) 2001-2025 Python
Software Foundation, PSF License Version 2), first translated from Python by PastaLean. Decode errors
raise `JSONDecodeError` (a `ValueError`) with the message of CPython's C scanner. JSON objects are
insertion-ordered `PyAny.dict`s; floats are exact rationals of their decimal text, so `NaN`/`Infinity`
and out-of-range literals are rejected.

Laid out as CPython's package: `Errors` (positions and messages), `Decoder` (`decoder.py` with
`scanner.py`, which recurse into each other and so share one `mutual` block), `Encoder`.
-/

def WHITESPACE_STR :=
  " \t\n\x0d"

def BACKSLASH :=
  Std.HashMap.ofList
    [("\"", "\""), ("\\", "\\"), ("/", "/"), ("b", "\x08"), ("f", "\x0c"), ("n", "\n"), ("r", "\x0d"), ("t", "\t")]

def _errmsg := fun (msg : String) ↦ fun (doc : String) ↦ fun (pos : Int) ↦
  Id.run
    (do
      let mut lineno : Int := (1 : Int)
      let mut last_nl : Int := -(1 : Int)
      for i in (PastaLean.pyRange pos)do
        if h_1 : doc⦋i⦌ = "\n" then 
          lineno := lineno +ₚ (1 : Int)
          last_nl := i
      let p'_ret_1 := s! "{msg }: line {lineno} column {(pos -ₚ last_nl)} (char {pos})"
      return p'_ret_1)

attribute [simp, taste_ingr] _errmsg

def _errmsg'rn := fun (msg : String) ↦ fun (doc : String) ↦ fun (pos : Int) ↦
  Id.run
    (do
      let mut lineno : Int := (1 : Int)
      let mut last_nl : Int := -(1 : Int)
      for i in (PastaLean.pyRange pos)do
        if h_1 : doc⦋i⦌ == "\n" then 
          lineno := lineno +ₚ (1 : Int)
          last_nl := i
      let p'_ret_1 := s! "{msg }: line {lineno} column {(pos -ₚ last_nl)} (char {pos})"
      return p'_ret_1)

def _skip_ws := fun (s : String) ↦ fun («end» : Int) ↦
  Id.run
    (do
      let mut «end» := «end»
      while («end» < PastaLean.pyLen s ∧ PastaLean.pyContains WHITESPACE_STR s⦋«end»⦌) do
        «end» := «end» +ₚ (1 : Int)
      return «end»)

attribute [simp, taste_ingr] _skip_ws

def _skip_ws'rn := fun (s : String) ↦ fun («end» : Int) ↦
  Id.run
    (do
      let mut «end» := «end»
      while (decide («end» < PastaLean.pyLen s) && PastaLean.pyContains WHITESPACE_STR s⦋«end»⦌) do
        «end» := «end» +ₚ (1 : Int)
      return «end»)

end Libraries.json

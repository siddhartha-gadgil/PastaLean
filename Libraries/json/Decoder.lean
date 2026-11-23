import Libraries.json.Errors
import Std.Tactic.Do

open PastaLean
open Std.Do

set_option linter.all false

set_option maxHeartbeats 200000

namespace Libraries.json

def _decode_uXXXX : String → Int → PastaLean.ProofMode.PyProofM Int := fun (s : String) ↦ fun (pos : Int) ↦ do
  let mut esc : String := PastaLean.pySlice s (some (pos +ₚ (1 : Int))) (some (pos +ₚ (5 : Int))) none
  if h_1 : PastaLean.pyLen esc = (4 : Int) then 
    let mut uni : Int := (0 : Int)
    let mut ok : Bool := Bool.true
    for c in (PastaLean.pyIter esc)do
      if h_2 : "0" ≤ c ∧ c ≤ "9" then 
        uni := uni *ₚ (16 : Int) +ₚ PastaLean.pyOrd c -ₚ (48 : Int)
      else
        if h_3 : "a" ≤ c ∧ c ≤ "f" then 
          uni := uni *ₚ (16 : Int) +ₚ PastaLean.pyOrd c -ₚ (87 : Int)
        else
          if h_4 : "A" ≤ c ∧ c ≤ "F" then 
            uni := uni *ₚ (16 : Int) +ₚ PastaLean.pyOrd c -ₚ (55 : Int)
          else
            ok := Bool.false
    if h_2 : PastaLean.pyTruthy ok then 
      return uni
  throw (PastaLean.PyException.Raise "JSONDecodeError" (ToString.toString (_errmsg "Invalid \\uXXXX escape" s pos)))

attribute [simp] _decode_uXXXX

def _decode_uXXXX'rn : String → Int → PastaLean.PyExcept Int := fun (s : String) ↦ fun (pos : Int) ↦ do
  let mut esc : String := PastaLean.pySlice s (some (pos +ₚ (1 : Int))) (some (pos +ₚ (5 : Int))) none
  if h_1 : PastaLean.pyLen esc == (4 : Int) then 
    let mut uni : Int := (0 : Int)
    let mut ok : Bool := Bool.true
    for c in (PastaLean.pyIter esc)do
      if h_2 : decide ("0" ≤ c) && decide (c ≤ "9") then 
        uni := uni *ₚ (16 : Int) +ₚ PastaLean.pyOrd c -ₚ (48 : Int)
      else
        if h_3 : decide ("a" ≤ c) && decide (c ≤ "f") then 
          uni := uni *ₚ (16 : Int) +ₚ PastaLean.pyOrd c -ₚ (87 : Int)
        else
          if h_4 : decide ("A" ≤ c) && decide (c ≤ "F") then 
            uni := uni *ₚ (16 : Int) +ₚ PastaLean.pyOrd c -ₚ (55 : Int)
          else
            ok := Bool.false
    if h_2 : PastaLean.pyTruthy ok then 
      return uni
  throw (PastaLean.PyException.Raise "JSONDecodeError" (ToString.toString (_errmsg'rn "Invalid \\uXXXX escape" s pos)))

def scanstring (s : String) («end» : Int) (strict : Bool := Bool.true) : PastaLean.ProofMode.PyProofM (String × Int) :=
  do
  let mut «end» := «end»
  let mut chunks : List String := []
  let mut begin : Int := «end» -ₚ (1 : Int)
  while (Bool.true) do
    let mut start : Int := «end»
    while (((«end» < PastaLean.pyLen s ∧ s⦋«end»⦌ ≠ "\"") ∧ s⦋«end»⦌ ≠ "\\") ∧ PastaLean.pyOrd s⦋«end»⦌ ≥ (32 : Int)) do
      «end» := «end» +ₚ (1 : Int)
    if h_1 : «end» ≥ PastaLean.pyLen s then 
      throw
          (PastaLean.PyException.Raise "JSONDecodeError"
            (ToString.toString (_errmsg "Unterminated string starting at" s begin)))
    if h_2 : «end» > start then 
      chunks := PastaLean.pyAppend chunks (PastaLean.pySlice s (some start) (some «end») none)
    let mut terminator : String := s⦋«end»⦌
    «end» := «end» +ₚ (1 : Int)
    if h_3 : terminator = "\"" then 
      break
    else
      if h_4 : terminator ≠ "\\" then 
        if h_5 : PastaLean.pyTruthy strict then 
          throw
              (PastaLean.PyException.Raise "JSONDecodeError"
                (ToString.toString (_errmsg "Invalid control character at" s («end» -ₚ (1 : Int)))))
        chunks := PastaLean.pyAppend chunks terminator
        continue
    if h_4 : «end» ≥ PastaLean.pyLen s then 
      throw
          (PastaLean.PyException.Raise "JSONDecodeError"
            (ToString.toString (_errmsg "Unterminated string starting at" s begin)))
    let mut esc : String := s⦋«end»⦌
    let mut char : String := default
    if h_5 : esc ≠ "u" then 
      if h_6 : !(PastaLean.pyContains BACKSLASH esc) then 
        throw
            (PastaLean.PyException.Raise "JSONDecodeError"
              (ToString.toString (_errmsg "Invalid \\escape" s («end» -ₚ (1 : Int)))))
      char := BACKSLASH⦋esc⦌
      «end» := «end» +ₚ (1 : Int)
    else
      let mut uni : Int := (← _decode_uXXXX s «end»)
      «end» := «end» +ₚ (5 : Int)
      if h_6 :
          ((55296 : Int) ≤ uni ∧ uni ≤ (56319 : Int)) ∧
            PastaLean.pySlice s (some «end») (some («end» +ₚ (2 : Int))) none = "\\u" then
        
        let mut uni2 : Int := (← _decode_uXXXX s («end» +ₚ (1 : Int)))
        if h_7 : (56320 : Int) ≤ uni2 ∧ uni2 ≤ (57343 : Int) then 
          uni :=
            (65536 : Int) +ₚ
              PastaLean.pyBitOr (PastaLean.pyShiftLeft (uni -ₚ (55296 : Int)) (10 : Int)) (uni2 -ₚ (56320 : Int))
          «end» := «end» +ₚ (6 : Int)
      char := PastaLean.pyChr uni
    chunks := PastaLean.pyAppend chunks char
  let p'_ret_1 := (PastaLean.pyStringJoin "" chunks, «end»)
  return p'_ret_1

attribute [simp] scanstring

def scanstring'rn (s : String) («end» : Int) (strict : Bool := Bool.true) : PastaLean.PyExcept (String × Int) := do
  let mut «end» := «end»
  let mut chunks : List String := []
  let mut begin : Int := «end» -ₚ (1 : Int)
  while (Bool.true) do
    let mut start : Int := «end»
    while
      (decide («end» < PastaLean.pyLen s) && s⦋«end»⦌ != "\"" && s⦋«end»⦌ != "\\" &&
        decide (PastaLean.pyOrd s⦋«end»⦌ ≥ (32 : Int))) do
      «end» := «end» +ₚ (1 : Int)
    if h_1 : «end» ≥ PastaLean.pyLen s then 
      throw
          (PastaLean.PyException.Raise "JSONDecodeError"
            (ToString.toString (_errmsg'rn "Unterminated string starting at" s begin)))
    if h_2 : «end» > start then 
      chunks := PastaLean.pyAppend chunks (PastaLean.pySlice s (some start) (some «end») none)
    let mut terminator : String := s⦋«end»⦌
    «end» := «end» +ₚ (1 : Int)
    if h_3 : terminator == "\"" then 
      break
    else
      if h_4 : terminator != "\\" then 
        if h_5 : PastaLean.pyTruthy strict then 
          throw
              (PastaLean.PyException.Raise "JSONDecodeError"
                (ToString.toString (_errmsg'rn "Invalid control character at" s («end» -ₚ (1 : Int)))))
        chunks := PastaLean.pyAppend chunks terminator
        continue
    if h_4 : «end» ≥ PastaLean.pyLen s then 
      throw
          (PastaLean.PyException.Raise "JSONDecodeError"
            (ToString.toString (_errmsg'rn "Unterminated string starting at" s begin)))
    let mut esc : String := s⦋«end»⦌
    let mut char : String := default
    if h_5 : esc != "u" then 
      if h_6 : !(PastaLean.pyContains BACKSLASH esc) then 
        throw
            (PastaLean.PyException.Raise "JSONDecodeError"
              (ToString.toString (_errmsg'rn "Invalid \\escape" s («end» -ₚ (1 : Int)))))
      char := BACKSLASH⦋esc⦌
      «end» := «end» +ₚ (1 : Int)
    else
      let mut uni : Int := (← _decode_uXXXX'rn s «end»)
      «end» := «end» +ₚ (5 : Int)
      if h_6 :
          decide ((55296 : Int) ≤ uni) && decide (uni ≤ (56319 : Int)) &&
            PastaLean.pySlice s (some «end») (some («end» +ₚ (2 : Int))) none == "\\u" then
        
        let mut uni2 : Int := (← _decode_uXXXX'rn s («end» +ₚ (1 : Int)))
        if h_7 : decide ((56320 : Int) ≤ uni2) && decide (uni2 ≤ (57343 : Int)) then 
          uni :=
            (65536 : Int) +ₚ
              PastaLean.pyBitOr (PastaLean.pyShiftLeft (uni -ₚ (55296 : Int)) (10 : Int)) (uni2 -ₚ (56320 : Int))
          «end» := «end» +ₚ (6 : Int)
      char := PastaLean.pyChr uni
    chunks := PastaLean.pyAppend chunks char
  let p'_ret_1 := (PastaLean.pyStringJoin "" chunks, «end»)
  return p'_ret_1

def _match_number := fun (s : String) ↦ fun (idx : Int) ↦
  Id.run
    (do
      let mut «end» : Int := idx
      if h_1 : «end» < PastaLean.pyLen s ∧ s⦋«end»⦌ = "-" then 
        «end» := «end» +ₚ (1 : Int)
      if h_2 : «end» < PastaLean.pyLen s ∧ s⦋«end»⦌ = "0" then 
        «end» := «end» +ₚ (1 : Int)
      else
        if h_3 : «end» < PastaLean.pyLen s ∧ "1" ≤ s⦋«end»⦌ ∧ s⦋«end»⦌ ≤ "9" then 
          while («end» < PastaLean.pyLen s ∧ "0" ≤ s⦋«end»⦌ ∧ s⦋«end»⦌ ≤ "9") do
            «end» := «end» +ₚ (1 : Int)
        else
          let p'_ret_1 := ((PastaLean.PyAny.none : PastaLean.PyAny), -(1 : Int))
          return p'_ret_1
      let mut is_float : Bool := Bool.false
      if h_3 :
          («end» +ₚ (1 : Int) < PastaLean.pyLen s ∧ s⦋«end»⦌ = ".") ∧
            "0" ≤ s⦋«end» +ₚ (1 : Int)⦌ ∧ s⦋«end» +ₚ (1 : Int)⦌ ≤ "9" then
        
        is_float := Bool.true
        «end» := «end» +ₚ (1 : Int)
        while («end» < PastaLean.pyLen s ∧ "0" ≤ s⦋«end»⦌ ∧ s⦋«end»⦌ ≤ "9") do
          «end» := «end» +ₚ (1 : Int)
      if h_4 : «end» < PastaLean.pyLen s ∧ (s⦋«end»⦌ = "e" ∨ s⦋«end»⦌ = "E") then 
        let mut k : Int := «end» +ₚ (1 : Int)
        if h_5 : k < PastaLean.pyLen s ∧ (s⦋k⦌ = "-" ∨ s⦋k⦌ = "+") then 
          k := k +ₚ (1 : Int)
        if h_6 : k < PastaLean.pyLen s ∧ "0" ≤ s⦋k⦌ ∧ s⦋k⦌ ≤ "9" then 
          is_float := Bool.true
          «end» := k
          while («end» < PastaLean.pyLen s ∧ "0" ≤ s⦋«end»⦌ ∧ s⦋«end»⦌ ≤ "9") do
            «end» := «end» +ₚ (1 : Int)
      if h_5 : PastaLean.pyTruthy is_float then 
        let p'_ret_1 :=
          ((PastaLean.pyRat (PastaLean.pySlice s (some idx) (some «end») none) : PastaLean.PyAny), «end»)
        return p'_ret_1
      let p'_ret_1 :=
        ((PastaLean.pyInt (PastaLean.pySlice s (some idx) (some «end») none) : PastaLean.PyAny), «end»)
      return p'_ret_1)

attribute [simp, taste_ingr] _match_number

def _match_number'rn := fun (s : String) ↦ fun (idx : Int) ↦
  Id.run
    (do
      let mut «end» : Int := idx
      if h_1 : decide («end» < PastaLean.pyLen s) && s⦋«end»⦌ == "-" then 
        «end» := «end» +ₚ (1 : Int)
      if h_2 : decide («end» < PastaLean.pyLen s) && s⦋«end»⦌ == "0" then 
        «end» := «end» +ₚ (1 : Int)
      else
        if h_3 : decide («end» < PastaLean.pyLen s) && (decide ("1" ≤ s⦋«end»⦌) && decide (s⦋«end»⦌ ≤ "9")) then 
          while (decide («end» < PastaLean.pyLen s) && (decide ("0" ≤ s⦋«end»⦌) && decide (s⦋«end»⦌ ≤ "9"))) do
            «end» := «end» +ₚ (1 : Int)
        else
          let p'_ret_1 := ((PastaLean.PyAny.none : PastaLean.PyAny), -(1 : Int))
          return p'_ret_1
      let mut is_float : Bool := Bool.false
      if h_3 :
          decide («end» +ₚ (1 : Int) < PastaLean.pyLen s) && s⦋«end»⦌ == "." &&
            (decide ("0" ≤ s⦋«end» +ₚ (1 : Int)⦌) && decide (s⦋«end» +ₚ (1 : Int)⦌ ≤ "9")) then
        
        is_float := Bool.true
        «end» := «end» +ₚ (1 : Int)
        while (decide («end» < PastaLean.pyLen s) && (decide ("0" ≤ s⦋«end»⦌) && decide (s⦋«end»⦌ ≤ "9"))) do
          «end» := «end» +ₚ (1 : Int)
      if h_4 : decide («end» < PastaLean.pyLen s) && (s⦋«end»⦌ == "e" || s⦋«end»⦌ == "E") then 
        let mut k : Int := «end» +ₚ (1 : Int)
        if h_5 : decide (k < PastaLean.pyLen s) && (s⦋k⦌ == "-" || s⦋k⦌ == "+") then 
          k := k +ₚ (1 : Int)
        if h_6 : decide (k < PastaLean.pyLen s) && (decide ("0" ≤ s⦋k⦌) && decide (s⦋k⦌ ≤ "9")) then 
          is_float := Bool.true
          «end» := k
          while (decide («end» < PastaLean.pyLen s) && (decide ("0" ≤ s⦋«end»⦌) && decide (s⦋«end»⦌ ≤ "9"))) do
            «end» := «end» +ₚ (1 : Int)
      if h_5 : PastaLean.pyTruthy is_float then 
        let p'_ret_1 :=
          ((PastaLean.pyFloat (PastaLean.pySlice s (some idx) (some «end») none) : PastaLean.PyAny), «end»)
        return p'_ret_1
      let p'_ret_1 :=
        ((PastaLean.pyInt (PastaLean.pySlice s (some idx) (some «end») none) : PastaLean.PyAny), «end»)
      return p'_ret_1)

mutual
  partial def scan_once : String → Int → PastaLean.ProofMode.PyProofM (PyAny × Int) := fun (s : String) ↦
    fun (idx : Int) ↦
    ((do
        if h_1 : idx ≥ PastaLean.pyLen s then 
          throw (PastaLean.PyException.Raise "JSONDecodeError" (ToString.toString (_errmsg "Expecting value" s idx)))
        let mut nextchar : String := s⦋idx⦌
        if h_2 : nextchar = "\"" then 
          let p'_ret_1 :=
            match (← scanstring s (idx +ₚ (1 : Int))) with
            | (p'_part_1, p'_part_2) => ((p'_part_1 : PastaLean.PyAny), p'_part_2)
          return p'_ret_1
        if h_3 : nextchar = "{" then 
          let p'_ret_1 :=
            match (← parse_object s (idx +ₚ (1 : Int))) with
            | (p'_part_1, p'_part_2) => ((p'_part_1 : PastaLean.PyAny), p'_part_2)
          return p'_ret_1
        if h_4 : nextchar = "[" then 
          let p'_ret_1 :=
            match (← parse_array s (idx +ₚ (1 : Int))) with
            | (p'_part_1, p'_part_2) => ((p'_part_1 : PastaLean.PyAny), p'_part_2)
          return p'_ret_1
        if h_5 : nextchar = "n" ∧ PastaLean.pySlice s (some idx) (some (idx +ₚ (4 : Int))) none = "null" then 
          let p'_ret_1 := ((PastaLean.PyAny.none : PastaLean.PyAny), idx +ₚ (4 : Int))
          return p'_ret_1
        if h_6 : nextchar = "t" ∧ PastaLean.pySlice s (some idx) (some (idx +ₚ (4 : Int))) none = "true" then 
          let p'_ret_1 := ((Bool.true : PastaLean.PyAny), idx +ₚ (4 : Int))
          return p'_ret_1
        if h_7 : nextchar = "f" ∧ PastaLean.pySlice s (some idx) (some (idx +ₚ (5 : Int))) none = "false" then 
          let p'_ret_1 := ((Bool.false : PastaLean.PyAny), idx +ₚ (5 : Int))
          return p'_ret_1
        let p'_unpack_value_1 := _match_number s idx
        let p'_unpack_pair_1 := p'_unpack_value_1
        let mut value : PyAny := Prod.fst p'_unpack_pair_1
        let mut «end» : Int := Prod.snd p'_unpack_pair_1
        if h_8 : «end» ≥ (0 : Int) then 
          let p'_ret_1 := ((value : PastaLean.PyAny), «end»)
          return p'_ret_1
        throw (PastaLean.PyException.Raise "JSONDecodeError" (ToString.toString (_errmsg "Expecting value" s idx)))) :
      PastaLean.ProofMode.PyProofM _)
  partial def parse_object : String → Int → PastaLean.ProofMode.PyProofM (PyAny × Int) := fun (s : String) ↦
    fun («end» : Int) ↦
    ((do
        let mut «end» := «end»
        let mut pairs : PyAny := PastaLean.PyAny.dict []
        let mut nextchar : String := PastaLean.pySlice s (some «end») (some («end» +ₚ (1 : Int))) none
        if h_1 : nextchar ≠ "\"" then 
          if h_2 : PastaLean.pyContains WHITESPACE_STR nextchar then 
            «end» := _skip_ws s «end»
            nextchar := PastaLean.pySlice s (some «end») (some («end» +ₚ (1 : Int))) none
          if h_3 : nextchar = "}" then 
            let p'_ret_1 := ((pairs : PastaLean.PyAny), «end» +ₚ (1 : Int))
            return p'_ret_1
          else
            if h_4 : nextchar ≠ "\"" then 
              throw
                  (PastaLean.PyException.Raise "JSONDecodeError"
                    (ToString.toString (_errmsg "Expecting property name enclosed in double quotes" s «end»)))
        «end» := «end» +ₚ (1 : Int)
        while (Bool.true) do
          let p'_unpack_value_1 ← scanstring s «end»
          let p'_unpack_pair_1 := p'_unpack_value_1
          let mut key : String := Prod.fst p'_unpack_pair_1
          «end» := Prod.snd p'_unpack_pair_1
          if h_2 : PastaLean.pySlice s (some «end») (some («end» +ₚ (1 : Int))) none ≠ ":" then 
            «end» := _skip_ws s «end»
            if h_3 : PastaLean.pySlice s (some «end») (some («end» +ₚ (1 : Int))) none ≠ ":" then 
              throw
                  (PastaLean.PyException.Raise "JSONDecodeError"
                    (ToString.toString (_errmsg "Expecting ':' delimiter" s «end»)))
          «end» := _skip_ws s («end» +ₚ (1 : Int))
          let p'_unpack_value_2 ← scan_once s «end»
          let p'_unpack_pair_2 := p'_unpack_value_2
          let mut value : PyAny := Prod.fst p'_unpack_pair_2
          «end» := Prod.snd p'_unpack_pair_2
          pairs := PastaLean.pySetItem pairs (key : PastaLean.PyAny) (value : PastaLean.PyAny)
          «end» := _skip_ws s «end»
          nextchar := PastaLean.pySlice s (some «end») (some («end» +ₚ (1 : Int))) none
          «end» := «end» +ₚ (1 : Int)
          if h_3 : nextchar = "}" then 
            break
          else
            if h_4 : nextchar ≠ "," then 
              throw
                  (PastaLean.PyException.Raise "JSONDecodeError"
                    (ToString.toString (_errmsg "Expecting ',' delimiter" s («end» -ₚ (1 : Int)))))
          let mut comma_idx : Int := «end» -ₚ (1 : Int)
          «end» := _skip_ws s «end»
          nextchar := PastaLean.pySlice s (some «end») (some («end» +ₚ (1 : Int))) none
          «end» := «end» +ₚ (1 : Int)
          if h_4 : nextchar ≠ "\"" then 
            if h_5 : nextchar = "}" then 
              throw
                  (PastaLean.PyException.Raise "JSONDecodeError"
                    (ToString.toString (_errmsg "Illegal trailing comma before end of object" s comma_idx)))
            throw
                (PastaLean.PyException.Raise "JSONDecodeError"
                  (ToString.toString
                    (_errmsg "Expecting property name enclosed in double quotes" s («end» -ₚ (1 : Int)))))
        let p'_ret_1 := ((pairs : PastaLean.PyAny), «end»)
        return p'_ret_1) :
      PastaLean.ProofMode.PyProofM _)
  partial def parse_array : String → Int → PastaLean.ProofMode.PyProofM (PyAny × Int) := fun (s : String) ↦
    fun («end» : Int) ↦
    ((do
        let mut «end» := «end»
        let mut values : List PyAny := ([] : List PastaLean.PyAny)
        «end» := _skip_ws s «end»
        if h_1 : PastaLean.pySlice s (some «end») (some («end» +ₚ (1 : Int))) none = "]" then 
          let p'_ret_1 := ((values : PastaLean.PyAny), «end» +ₚ (1 : Int))
          return p'_ret_1
        while (Bool.true) do
          let p'_unpack_value_1 ← scan_once s «end»
          let p'_unpack_pair_1 := p'_unpack_value_1
          let mut value : PyAny := Prod.fst p'_unpack_pair_1
          «end» := Prod.snd p'_unpack_pair_1
          values := PastaLean.pyAppend values value
          «end» := _skip_ws s «end»
          let mut nextchar : String := PastaLean.pySlice s (some «end») (some («end» +ₚ (1 : Int))) none
          «end» := «end» +ₚ (1 : Int)
          if h_2 : nextchar = "]" then 
            break
          else
            if h_3 : nextchar ≠ "," then 
              throw
                  (PastaLean.PyException.Raise "JSONDecodeError"
                    (ToString.toString (_errmsg "Expecting ',' delimiter" s («end» -ₚ (1 : Int)))))
          let mut comma_idx : Int := «end» -ₚ (1 : Int)
          «end» := _skip_ws s «end»
          if h_3 : PastaLean.pySlice s (some «end») (some («end» +ₚ (1 : Int))) none = "]" then 
            throw
                (PastaLean.PyException.Raise "JSONDecodeError"
                  (ToString.toString (_errmsg "Illegal trailing comma before end of array" s comma_idx)))
        let p'_ret_1 := ((values : PastaLean.PyAny), «end»)
        return p'_ret_1) :
      PastaLean.ProofMode.PyProofM _)
end

mutual
  partial def scan_once'rn : String → Int → PastaLean.PyExcept (PyAny × Int) := fun (s : String) ↦ fun (idx : Int) ↦
    ((do
        if h_1 : idx ≥ PastaLean.pyLen s then 
          throw (PastaLean.PyException.Raise "JSONDecodeError" (ToString.toString (_errmsg'rn "Expecting value" s idx)))
        let mut nextchar : String := s⦋idx⦌
        if h_2 : nextchar == "\"" then 
          let p'_ret_1 :=
            match (← scanstring'rn s (idx +ₚ (1 : Int))) with
            | (p'_part_1, p'_part_2) => ((p'_part_1 : PastaLean.PyAny), p'_part_2)
          return p'_ret_1
        if h_3 : nextchar == "{" then 
          let p'_ret_1 :=
            match (← parse_object'rn s (idx +ₚ (1 : Int))) with
            | (p'_part_1, p'_part_2) => ((p'_part_1 : PastaLean.PyAny), p'_part_2)
          return p'_ret_1
        if h_4 : nextchar == "[" then 
          let p'_ret_1 :=
            match (← parse_array'rn s (idx +ₚ (1 : Int))) with
            | (p'_part_1, p'_part_2) => ((p'_part_1 : PastaLean.PyAny), p'_part_2)
          return p'_ret_1
        if h_5 : nextchar == "n" && PastaLean.pySlice s (some idx) (some (idx +ₚ (4 : Int))) none == "null" then 
          let p'_ret_1 := ((PastaLean.PyAny.none : PastaLean.PyAny), idx +ₚ (4 : Int))
          return p'_ret_1
        if h_6 : nextchar == "t" && PastaLean.pySlice s (some idx) (some (idx +ₚ (4 : Int))) none == "true" then 
          let p'_ret_1 := ((Bool.true : PastaLean.PyAny), idx +ₚ (4 : Int))
          return p'_ret_1
        if h_7 : nextchar == "f" && PastaLean.pySlice s (some idx) (some (idx +ₚ (5 : Int))) none == "false" then 
          let p'_ret_1 := ((Bool.false : PastaLean.PyAny), idx +ₚ (5 : Int))
          return p'_ret_1
        let p'_unpack_value_1 := _match_number'rn s idx
        let p'_unpack_pair_1 := p'_unpack_value_1
        let mut value : PyAny := Prod.fst p'_unpack_pair_1
        let mut «end» : Int := Prod.snd p'_unpack_pair_1
        if h_8 : «end» ≥ (0 : Int) then 
          let p'_ret_1 := ((value : PastaLean.PyAny), «end»)
          return p'_ret_1
        throw (PastaLean.PyException.Raise "JSONDecodeError" (ToString.toString (_errmsg'rn "Expecting value" s idx)))) :
      PastaLean.PyExcept _)
  partial def parse_object'rn : String → Int → PastaLean.PyExcept (PyAny × Int) := fun (s : String) ↦
    fun («end» : Int) ↦
    ((do
        let mut «end» := «end»
        let mut pairs : PyAny := PastaLean.PyAny.dict []
        let mut nextchar : String := PastaLean.pySlice s (some «end») (some («end» +ₚ (1 : Int))) none
        if h_1 : nextchar != "\"" then 
          if h_2 : PastaLean.pyContains WHITESPACE_STR nextchar then 
            «end» := _skip_ws'rn s «end»
            nextchar := PastaLean.pySlice s (some «end») (some («end» +ₚ (1 : Int))) none
          if h_3 : nextchar == "}" then 
            let p'_ret_1 := ((pairs : PastaLean.PyAny), «end» +ₚ (1 : Int))
            return p'_ret_1
          else
            if h_4 : nextchar != "\"" then 
              throw
                  (PastaLean.PyException.Raise "JSONDecodeError"
                    (ToString.toString (_errmsg'rn "Expecting property name enclosed in double quotes" s «end»)))
        «end» := «end» +ₚ (1 : Int)
        while (Bool.true) do
          let p'_unpack_value_1 ← scanstring'rn s «end»
          let p'_unpack_pair_1 := p'_unpack_value_1
          let mut key : String := Prod.fst p'_unpack_pair_1
          «end» := Prod.snd p'_unpack_pair_1
          if h_2 : PastaLean.pySlice s (some «end») (some («end» +ₚ (1 : Int))) none != ":" then 
            «end» := _skip_ws'rn s «end»
            if h_3 : PastaLean.pySlice s (some «end») (some («end» +ₚ (1 : Int))) none != ":" then 
              throw
                  (PastaLean.PyException.Raise "JSONDecodeError"
                    (ToString.toString (_errmsg'rn "Expecting ':' delimiter" s «end»)))
          «end» := _skip_ws'rn s («end» +ₚ (1 : Int))
          let p'_unpack_value_2 ← scan_once'rn s «end»
          let p'_unpack_pair_2 := p'_unpack_value_2
          let mut value : PyAny := Prod.fst p'_unpack_pair_2
          «end» := Prod.snd p'_unpack_pair_2
          pairs := PastaLean.pySetItem pairs (key : PastaLean.PyAny) (value : PastaLean.PyAny)
          «end» := _skip_ws'rn s «end»
          nextchar := PastaLean.pySlice s (some «end») (some («end» +ₚ (1 : Int))) none
          «end» := «end» +ₚ (1 : Int)
          if h_3 : nextchar == "}" then 
            break
          else
            if h_4 : nextchar != "," then 
              throw
                  (PastaLean.PyException.Raise "JSONDecodeError"
                    (ToString.toString (_errmsg'rn "Expecting ',' delimiter" s («end» -ₚ (1 : Int)))))
          let mut comma_idx : Int := «end» -ₚ (1 : Int)
          «end» := _skip_ws'rn s «end»
          nextchar := PastaLean.pySlice s (some «end») (some («end» +ₚ (1 : Int))) none
          «end» := «end» +ₚ (1 : Int)
          if h_4 : nextchar != "\"" then 
            if h_5 : nextchar == "}" then 
              throw
                  (PastaLean.PyException.Raise "JSONDecodeError"
                    (ToString.toString (_errmsg'rn "Illegal trailing comma before end of object" s comma_idx)))
            throw
                (PastaLean.PyException.Raise "JSONDecodeError"
                  (ToString.toString
                    (_errmsg'rn "Expecting property name enclosed in double quotes" s («end» -ₚ (1 : Int)))))
        let p'_ret_1 := ((pairs : PastaLean.PyAny), «end»)
        return p'_ret_1) :
      PastaLean.PyExcept _)
  partial def parse_array'rn : String → Int → PastaLean.PyExcept (PyAny × Int) := fun (s : String) ↦ fun («end» : Int) ↦
    ((do
        let mut «end» := «end»
        let mut values : List PyAny := ([] : List PastaLean.PyAny)
        «end» := _skip_ws'rn s «end»
        if h_1 : PastaLean.pySlice s (some «end») (some («end» +ₚ (1 : Int))) none == "]" then 
          let p'_ret_1 := ((values : PastaLean.PyAny), «end» +ₚ (1 : Int))
          return p'_ret_1
        while (Bool.true) do
          let p'_unpack_value_1 ← scan_once'rn s «end»
          let p'_unpack_pair_1 := p'_unpack_value_1
          let mut value : PyAny := Prod.fst p'_unpack_pair_1
          «end» := Prod.snd p'_unpack_pair_1
          values := PastaLean.pyAppend values value
          «end» := _skip_ws'rn s «end»
          let mut nextchar : String := PastaLean.pySlice s (some «end») (some («end» +ₚ (1 : Int))) none
          «end» := «end» +ₚ (1 : Int)
          if h_2 : nextchar == "]" then 
            break
          else
            if h_3 : nextchar != "," then 
              throw
                  (PastaLean.PyException.Raise "JSONDecodeError"
                    (ToString.toString (_errmsg'rn "Expecting ',' delimiter" s («end» -ₚ (1 : Int)))))
          let mut comma_idx : Int := «end» -ₚ (1 : Int)
          «end» := _skip_ws'rn s «end»
          if h_3 : PastaLean.pySlice s (some «end») (some («end» +ₚ (1 : Int))) none == "]" then 
            throw
                (PastaLean.PyException.Raise "JSONDecodeError"
                  (ToString.toString (_errmsg'rn "Illegal trailing comma before end of array" s comma_idx)))
        let p'_ret_1 := ((values : PastaLean.PyAny), «end»)
        return p'_ret_1) :
      PastaLean.PyExcept _)
end

def loads : String → PastaLean.ProofMode.PyProofM PastaLean.PyAny := fun (s : String) ↦ do
  let p'_unpack_value_1 ← scan_once s (_skip_ws s (0 : Int))
  let p'_unpack_pair_1 := p'_unpack_value_1
  let mut obj : PyAny := Prod.fst p'_unpack_pair_1
  let mut «end» : Int := Prod.snd p'_unpack_pair_1
  «end» := _skip_ws s «end»
  if h_1 : «end» ≠ PastaLean.pyLen s then 
    throw (PastaLean.PyException.Raise "JSONDecodeError" (ToString.toString (_errmsg "Extra data" s «end»)))
  return ((obj : PastaLean.PyAny) : PastaLean.PyAny)

attribute [simp] loads

def loads'rn : String → PastaLean.PyExcept PastaLean.PyAny := fun (s : String) ↦ do
  let p'_unpack_value_1 ← scan_once'rn s (_skip_ws'rn s (0 : Int))
  let p'_unpack_pair_1 := p'_unpack_value_1
  let mut obj : PyAny := Prod.fst p'_unpack_pair_1
  let mut «end» : Int := Prod.snd p'_unpack_pair_1
  «end» := _skip_ws'rn s «end»
  if h_1 : «end» != PastaLean.pyLen s then 
    throw (PastaLean.PyException.Raise "JSONDecodeError" (ToString.toString (_errmsg'rn "Extra data" s «end»)))
  return ((obj : PastaLean.PyAny) : PastaLean.PyAny)

end Libraries.json

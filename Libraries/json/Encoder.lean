import Libraries.json.Errors
import Std.Tactic.Do

open PastaLean
open Std.Do

set_option linter.all false

set_option maxHeartbeats 200000

namespace Libraries.json

def ESCAPE_DCT :=
  Std.HashMap.ofList
    [("\\", "\\\\"), ("\"", "\\\""), ("\x08", "\\b"), ("\x0c", "\\f"), ("\n", "\\n"), ("\x0d", "\\r"), ("\t", "\\t")]

def HEX :=
  "0123456789abcdef"

def _u4 := fun (n : Int) ↦
  "\\u" +ₚ HEX⦋PastaLean.pyBitAnd (PastaLean.pyShiftRight n (12 : Int)) (15 : Int)⦌ +ₚ
        HEX⦋PastaLean.pyBitAnd (PastaLean.pyShiftRight n (8 : Int)) (15 : Int)⦌ +ₚ
      HEX⦋PastaLean.pyBitAnd (PastaLean.pyShiftRight n (4 : Int)) (15 : Int)⦌ +ₚ
    HEX⦋PastaLean.pyBitAnd n (15 : Int)⦌

attribute [simp, taste_ingr] _u4

def _u4'rn := fun (n : Int) ↦
  "\\u" +ₚ HEX⦋PastaLean.pyBitAnd (PastaLean.pyShiftRight n (12 : Int)) (15 : Int)⦌ +ₚ
        HEX⦋PastaLean.pyBitAnd (PastaLean.pyShiftRight n (8 : Int)) (15 : Int)⦌ +ₚ
      HEX⦋PastaLean.pyBitAnd (PastaLean.pyShiftRight n (4 : Int)) (15 : Int)⦌ +ₚ
    HEX⦋PastaLean.pyBitAnd n (15 : Int)⦌

def encode_basestring := fun (s : String) ↦ fun (ensure_ascii : Bool) ↦
  Id.run
    (do
      let mut chunks : List String := ["\""]
      for c in (PastaLean.pyIter s)do
        let mut n : Int := PastaLean.pyOrd c
        if h_1 : PastaLean.pyContains ESCAPE_DCT c then 
          chunks := PastaLean.pyAppend chunks ESCAPE_DCT⦋c⦌
        else
          if h_2 : n < (32 : Int) then 
            chunks := PastaLean.pyAppend chunks (_u4 n)
          else
            if h_3 : n > (126 : Int) ∧ PastaLean.pyTruthy ensure_ascii = true then 
              if h_4 : n < (65536 : Int) then 
                chunks := PastaLean.pyAppend chunks (_u4 n)
              else
                n := n -ₚ (65536 : Int)
                chunks :=
                  PastaLean.pyAppend chunks
                    (_u4
                      (PastaLean.pyBitOr (55296 : Int)
                        (PastaLean.pyBitAnd (PastaLean.pyShiftRight n (10 : Int)) (1023 : Int))))
                chunks :=
                  PastaLean.pyAppend chunks (_u4 (PastaLean.pyBitOr (56320 : Int) (PastaLean.pyBitAnd n (1023 : Int))))
            else
              chunks := PastaLean.pyAppend chunks c
      chunks := PastaLean.pyAppend chunks "\""
      let p'_ret_1 := PastaLean.pyStringJoin "" chunks
      return p'_ret_1)

attribute [simp, taste_ingr] encode_basestring

def encode_basestring'rn := fun (s : String) ↦ fun (ensure_ascii : Bool) ↦
  Id.run
    (do
      let mut chunks : List String := ["\""]
      for c in (PastaLean.pyIter s)do
        let mut n : Int := PastaLean.pyOrd c
        if h_1 : PastaLean.pyContains ESCAPE_DCT c then 
          chunks := PastaLean.pyAppend chunks ESCAPE_DCT⦋c⦌
        else
          if h_2 : n < (32 : Int) then 
            chunks := PastaLean.pyAppend chunks (_u4'rn n)
          else
            if h_3 : decide (n > (126 : Int)) && PastaLean.pyTruthy ensure_ascii then 
              if h_4 : n < (65536 : Int) then 
                chunks := PastaLean.pyAppend chunks (_u4'rn n)
              else
                n := n -ₚ (65536 : Int)
                chunks :=
                  PastaLean.pyAppend chunks
                    (_u4'rn
                      (PastaLean.pyBitOr (55296 : Int)
                        (PastaLean.pyBitAnd (PastaLean.pyShiftRight n (10 : Int)) (1023 : Int))))
                chunks :=
                  PastaLean.pyAppend chunks
                    (_u4'rn (PastaLean.pyBitOr (56320 : Int) (PastaLean.pyBitAnd n (1023 : Int))))
            else
              chunks := PastaLean.pyAppend chunks c
      chunks := PastaLean.pyAppend chunks "\""
      let p'_ret_1 := PastaLean.pyStringJoin "" chunks
      return p'_ret_1)

def _encode_key : PastaLean.PyAny → PastaLean.ProofMode.PyProofM String := fun (k : PastaLean.PyAny) ↦ do
  if h_1 : PastaLean.pyTruthy (PastaLean.pyIsInstance k TypeInfer.PyType.str) then 
    let p'_ret_1 := PastaLean.pyStr k
    return p'_ret_1
  if h_2 : PastaLean.pyIsBool k Bool.true then 
    return "true"
  if h_3 : PastaLean.pyIsBool k Bool.false then 
    return "false"
  if h_4 : PastaLean.pyIsNone k then 
    return "null"
  if h_5 :
      PastaLean.pyTruthy (PastaLean.pyIsInstance k TypeInfer.PyType.int) = true ∨
        PastaLean.pyTruthy (PastaLean.pyIsInstance k TypeInfer.PyType.float) = true then
    
    let p'_ret_1 := PastaLean.PyPrintable.pyReprify k
    return p'_ret_1
  throw
      (PastaLean.PyException.Raise "TypeError"
        (ToString.toString ("keys must be str, int, float, bool or None, not " +ₚ (PastaLean.pyType k).__name__)))

attribute [simp] _encode_key

def _encode_key'rn : PastaLean.PyAny → PastaLean.PyExcept String := fun (k : PastaLean.PyAny) ↦ do
  if h_1 : PastaLean.pyTruthy (PastaLean.pyIsInstance k TypeInfer.PyType.str) then 
    let p'_ret_1 := PastaLean.pyStr k
    return p'_ret_1
  if h_2 : PastaLean.pyIsBool k Bool.true then 
    return "true"
  if h_3 : PastaLean.pyIsBool k Bool.false then 
    return "false"
  if h_4 : PastaLean.pyIsNone k then 
    return "null"
  if h_5 :
      PastaLean.pyTruthy (PastaLean.pyIsInstance k TypeInfer.PyType.int) ||
        PastaLean.pyTruthy (PastaLean.pyIsInstance k TypeInfer.PyType.float) then
    
    let p'_ret_1 := PastaLean.PyPrintable.pyReprify k
    return p'_ret_1
  throw
      (PastaLean.PyException.Raise "TypeError"
        (ToString.toString ("keys must be str, int, float, bool or None, not " +ₚ (PastaLean.pyType k).__name__)))

partial def _encode :
    PastaLean.PyAny → Bool → String → Int → String → String → Bool → Bool → PastaLean.ProofMode.PyProofM String :=
  fun (o : PastaLean.PyAny) ↦ fun (pretty : Bool) ↦ fun (indent : String) ↦ fun (level : Int) ↦
  fun (item_sep : String) ↦ fun (key_sep : String) ↦ fun (sort_keys : Bool) ↦ fun (ensure_ascii : Bool) ↦ do
  if h_1 : PastaLean.pyTruthy (PastaLean.pyIsInstance o TypeInfer.PyType.str) then 
    let p'_ret_1 := encode_basestring (PastaLean.pyStr o) ensure_ascii
    return p'_ret_1
  if h_2 : PastaLean.pyIsNone o then 
    return "null"
  if h_3 : PastaLean.pyIsBool o Bool.true then 
    return "true"
  if h_4 : PastaLean.pyIsBool o Bool.false then 
    return "false"
  if h_5 :
      PastaLean.pyTruthy (PastaLean.pyIsInstance o TypeInfer.PyType.int) = true ∨
        PastaLean.pyTruthy (PastaLean.pyIsInstance o TypeInfer.PyType.float) = true then
    
    let p'_ret_1 := PastaLean.PyPrintable.pyReprify o
    return p'_ret_1
  let mut closing : String := default
  let mut newline : String := default
  let mut parts : List String := default
  let mut sep : String := default
  if h_6 : PastaLean.pyTruthy (PastaLean.pyIsInstance o (TypeInfer.PyType.list TypeInfer.PyType.unknown)) then 
    if h_7 : PastaLean.pyLen o = (0 : Int) then 
      return "[]"
    sep := item_sep
    newline := ""
    closing := ""
    if h_8 : PastaLean.pyTruthy pretty then 
      newline := "\n" +ₚ indent *ₚ (level +ₚ (1 : Int))
      closing := "\n" +ₚ indent *ₚ level
      sep := item_sep +ₚ newline
    parts := []
    for v in (PastaLean.pyIter o)do
      parts :=
        PastaLean.pyAppend parts
          (← _encode v pretty indent (level +ₚ (1 : Int)) item_sep key_sep sort_keys ensure_ascii)
    let p'_ret_1 := "[" +ₚ newline +ₚ PastaLean.pyStringJoin sep parts +ₚ closing +ₚ "]"
    return p'_ret_1
  if h_7 :
      PastaLean.pyTruthy
        (PastaLean.pyIsInstance o (TypeInfer.PyType.dict TypeInfer.PyType.unknown TypeInfer.PyType.unknown)) then
    
    if h_8 : PastaLean.pyLen o = (0 : Int) then 
      return "{}"
    sep := item_sep
    newline := ""
    closing := ""
    if h_9 : PastaLean.pyTruthy pretty then 
      newline := "\n" +ₚ indent *ₚ (level +ₚ (1 : Int))
      closing := "\n" +ₚ indent *ₚ level
      sep := item_sep +ₚ newline
    let mut keys : List PyAny := ([] : List PastaLean.PyAny)
    for k in (PastaLean.pyIter o)do
      keys := PastaLean.pyAppend keys k
    if h_10 : PastaLean.pyTruthy sort_keys then 
      keys := PastaLean.pySort keys
    parts := []
    for k in (PastaLean.pyIter keys)do
      parts :=
        PastaLean.pyAppend parts
          (encode_basestring (← _encode_key k) ensure_ascii +ₚ key_sep +ₚ
            (← _encode o⦋k⦌ pretty indent (level +ₚ (1 : Int)) item_sep key_sep sort_keys ensure_ascii))
    let p'_ret_1 := "{" +ₚ newline +ₚ PastaLean.pyStringJoin sep parts +ₚ closing +ₚ "}"
    return p'_ret_1
  throw (PastaLean.PyException.Raise "TypeError" (ToString.toString "Object of this type is not JSON serializable"))

partial def _encode'rn :
    PastaLean.PyAny → Bool → String → Int → String → String → Bool → Bool → PastaLean.PyExcept String :=
  fun (o : PastaLean.PyAny) ↦ fun (pretty : Bool) ↦ fun (indent : String) ↦ fun (level : Int) ↦
  fun (item_sep : String) ↦ fun (key_sep : String) ↦ fun (sort_keys : Bool) ↦ fun (ensure_ascii : Bool) ↦ do
  if h_1 : PastaLean.pyTruthy (PastaLean.pyIsInstance o TypeInfer.PyType.str) then 
    let p'_ret_1 := encode_basestring'rn (PastaLean.pyStr o) ensure_ascii
    return p'_ret_1
  if h_2 : PastaLean.pyIsNone o then 
    return "null"
  if h_3 : PastaLean.pyIsBool o Bool.true then 
    return "true"
  if h_4 : PastaLean.pyIsBool o Bool.false then 
    return "false"
  if h_5 :
      PastaLean.pyTruthy (PastaLean.pyIsInstance o TypeInfer.PyType.int) ||
        PastaLean.pyTruthy (PastaLean.pyIsInstance o TypeInfer.PyType.float) then
    
    let p'_ret_1 := PastaLean.PyPrintable.pyReprify o
    return p'_ret_1
  let mut closing : String := default
  let mut newline : String := default
  let mut parts : List String := default
  let mut sep : String := default
  if h_6 : PastaLean.pyTruthy (PastaLean.pyIsInstance o (TypeInfer.PyType.list TypeInfer.PyType.unknown)) then 
    if h_7 : PastaLean.pyLen o == (0 : Int) then 
      return "[]"
    sep := item_sep
    newline := ""
    closing := ""
    if h_8 : PastaLean.pyTruthy pretty then 
      newline := "\n" +ₚ indent *ₚ (level +ₚ (1 : Int))
      closing := "\n" +ₚ indent *ₚ level
      sep := item_sep +ₚ newline
    parts := []
    for v in (PastaLean.pyIter o)do
      parts :=
        PastaLean.pyAppend parts
          (← _encode'rn v pretty indent (level +ₚ (1 : Int)) item_sep key_sep sort_keys ensure_ascii)
    let p'_ret_1 := "[" +ₚ newline +ₚ PastaLean.pyStringJoin sep parts +ₚ closing +ₚ "]"
    return p'_ret_1
  if h_7 :
      PastaLean.pyTruthy
        (PastaLean.pyIsInstance o (TypeInfer.PyType.dict TypeInfer.PyType.unknown TypeInfer.PyType.unknown)) then
    
    if h_8 : PastaLean.pyLen o == (0 : Int) then 
      return "{}"
    sep := item_sep
    newline := ""
    closing := ""
    if h_9 : PastaLean.pyTruthy pretty then 
      newline := "\n" +ₚ indent *ₚ (level +ₚ (1 : Int))
      closing := "\n" +ₚ indent *ₚ level
      sep := item_sep +ₚ newline
    let mut keys : List PyAny := ([] : List PastaLean.PyAny)
    for k in (PastaLean.pyIter o)do
      keys := PastaLean.pyAppend keys k
    if h_10 : PastaLean.pyTruthy sort_keys then 
      keys := PastaLean.pySort keys
    parts := []
    for k in (PastaLean.pyIter keys)do
      parts :=
        PastaLean.pyAppend parts
          (encode_basestring'rn (← _encode_key'rn k) ensure_ascii +ₚ key_sep +ₚ
            (← _encode'rn o⦋k⦌ pretty indent (level +ₚ (1 : Int)) item_sep key_sep sort_keys ensure_ascii))
    let p'_ret_1 := "{" +ₚ newline +ₚ PastaLean.pyStringJoin sep parts +ₚ closing +ₚ "}"
    return p'_ret_1
  throw (PastaLean.PyException.Raise "TypeError" (ToString.toString "Object of this type is not JSON serializable"))

def dumps (obj : PastaLean.PyAny) (indent : Option Int := Option.none) (sort_keys : Bool := Bool.false)
    (separators : Option (String × String) := Option.none) (ensure_ascii : Bool := Bool.true) :
    PastaLean.ProofMode.PyProofM String := do
  let mut item_sep : String := ", "
  let mut key_sep : String := ": "
  if let some indent := indent then 
    item_sep := ","
  if let some separators := separators then 
    let p'_unpack_value_1 := separators
    let p'_unpack_pair_1 := p'_unpack_value_1
    item_sep := Prod.fst p'_unpack_pair_1
    key_sep := Prod.snd p'_unpack_pair_1
  let mut ind : String := ""
  if let some indent := indent then 
    ind := " " *ₚ indent
  let p'_ret_1 := (← _encode obj (!PastaLean.pyIsNone indent) ind (0 : Int) item_sep key_sep sort_keys ensure_ascii)
  return p'_ret_1

attribute [simp] dumps

def dumps'rn (obj : PastaLean.PyAny) (indent : Option Int := Option.none) (sort_keys : Bool := Bool.false)
    (separators : Option (String × String) := Option.none) (ensure_ascii : Bool := Bool.true) :
    PastaLean.PyExcept String := do
  let mut item_sep : String := ", "
  let mut key_sep : String := ": "
  if let some indent := indent then 
    item_sep := ","
  if let some separators := separators then 
    let p'_unpack_value_1 := separators
    let p'_unpack_pair_1 := p'_unpack_value_1
    item_sep := Prod.fst p'_unpack_pair_1
    key_sep := Prod.snd p'_unpack_pair_1
  let mut ind : String := ""
  if let some indent := indent then 
    ind := " " *ₚ indent
  let p'_ret_1 := (← _encode'rn obj (!PastaLean.pyIsNone indent) ind (0 : Int) item_sep key_sep sort_keys ensure_ascii)
  return p'_ret_1

end Libraries.json

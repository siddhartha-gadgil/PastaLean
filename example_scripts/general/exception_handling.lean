import PastaLean
import Libraries
import Std.Tactic.Do

open PastaLean
open Libraries
open Std.Do

set_option linter.all false
set_option mvcgen.warning false

set_option maxHeartbeats 200000

namespace PastaLean.User.Root

def fail : Int → PastaLean.ProofMode.PyProofM String := fun (x : Int) ↦ do
  if h_1 : x < (0 : Int) then 
    throw (PastaLean.PyException.Raise "ValueError" (ToString.toString "negative"))
  let p'_ret_1 := s! "value {x}"
  return p'_ret_1

attribute [simp] fail

def fail'rn : Int → PastaLean.PyExcept String := fun (x : Int) ↦ do
  if h_1 : x < (0 : Int) then 
    throw (PastaLean.PyException.Raise "ValueError" (ToString.toString "negative"))
  let p'_ret_1 := s! "value {x}"
  return p'_ret_1

def call_fail := fun x ↦
  ((do
      let mut y : String := (← fail x)
      return y) :
    PastaLean.ProofMode.PyProofM _)

attribute [simp] call_fail

def call_fail'rn := fun x ↦
  ((do
      let mut y : String := (← fail'rn x)
      return y) :
    PastaLean.PyExcept _)

def safe := fun n ↦
  ((do
      try
        let p'_ret_1 := (← fail n)
        return p'_ret_1
      catch caught =>
        if (caught).OfKind == "ValueError" then 
          let err := caught
          let p'_ret_2 := s! "bad value: {err}"
          return p'_ret_2
        else
          throw caught) :
    PastaLean.ProofMode.PyProofM _)

attribute [simp] safe

def safe'rn := fun n ↦
  ((do
      try
        let p'_ret_1 := (← fail'rn n)
        return p'_ret_1
      catch caught =>
        if (caught).OfKind == "ValueError" then 
          let err := caught
          let p'_ret_2 := s! "bad value: {err}"
          return p'_ret_2
        else
          throw caught) :
    PastaLean.PyExcept _)

private def _simple_catch'helper := fun (x : Int) ↦ x +ₚ (1 : Int)

attribute [simp, taste_ingr] _simple_catch'helper

def simple_catch : PastaLean.ProofMode.PyProofM String := do
  let mut x : Int := (1 : Int)
  x := _simple_catch'helper x
  try
    throw (PastaLean.PyException.Raise "Exception" (ToString.toString "boom"))
  catch caught =>
    if Bool.true then 
      let e := caught
      let p'_ret_1 := s! "Caught exception: {e}"
      return p'_ret_1
    else
      throw caught

attribute [simp] simple_catch

private def _simple_catch'helper'rn := fun (x : Int) ↦ x +ₚ (1 : Int)

def simple_catch'rn : PastaLean.PyExcept String := do
  let mut x : Int := (1 : Int)
  x := _simple_catch'helper'rn x
  try
    throw (PastaLean.PyException.Raise "Exception" (ToString.toString "boom"))
  catch caught =>
    if Bool.true then 
      let e := caught
      let p'_ret_1 := s! "Caught exception: {e}"
      return p'_ret_1
    else
      throw caught

def fixed_catch : PastaLean.ProofMode.PyProofM String := do
  try
    let mut _ := (1 : Int) /ₚ (0 : Int)
    return "1 just got divided by 0"
  catch caught =>
    if (caught).OfKind == "ZeroDivisionError" then 
      let e := caught
      let p'_ret_1 := s! "Caught ZeroDivisionError: {e}"
      return p'_ret_1
    else
      if Bool.true then 
        let e := caught
        let p'_ret_2 := s! "Caught other exception: {e}"
        return p'_ret_2
      else
        throw caught

attribute [simp] fixed_catch

def fixed_catch'rn : PastaLean.PyExcept String := do
  try
    let mut _ := PastaLean.pyFloat (1 : Int) /ₚ (0 : Int)
    return "1 just got divided by 0"
  catch caught =>
    if (caught).OfKind == "ZeroDivisionError" then 
      let e := caught
      let p'_ret_1 := s! "Caught ZeroDivisionError: {e}"
      return p'_ret_1
    else
      if Bool.true then 
        let e := caught
        let p'_ret_2 := s! "Caught other exception: {e}"
        return p'_ret_2
      else
        throw caught

def nested_try : PastaLean.ProofMode.PyProofM String := do
  try
    ((do
          try
            let mut _ := (1 : Int) /ₚ (0 : Int)
            return "1 just got divided by 0"
          catch caught =>
            if (caught).OfKind == "ZeroDivisionError" then 
              let e := caught
              let p'_ret_1 := s! "Caught inner ZeroDivisionError: {e}"
              return p'_ret_1
            else
              throw caught) :
        PastaLean.ProofMode.PyProofM _)
  catch caught =>
    if Bool.true then 
      let e := caught
      let p'_ret_2 := s! "Caught outer exception: {e}"
      return p'_ret_2
    else
      throw caught

attribute [simp] nested_try

def nested_try'rn : PastaLean.PyExcept String := do
  try
    ((do
          try
            let mut _ := PastaLean.pyFloat (1 : Int) /ₚ (0 : Int)
            return "1 just got divided by 0"
          catch caught =>
            if (caught).OfKind == "ZeroDivisionError" then 
              let e := caught
              let p'_ret_1 := s! "Caught inner ZeroDivisionError: {e}"
              return p'_ret_1
            else
              throw caught) :
        PastaLean.PyExcept _)
  catch caught =>
    if Bool.true then 
      let e := caught
      let p'_ret_2 := s! "Caught outer exception: {e}"
      return p'_ret_2
    else
      throw caught

def try_with_else_finally : Int → PastaLean.ProofMode.PyProofM String := fun (num : Int) ↦ do
  try
    if h_1 : num < (0 : Int) then 
      throw (PastaLean.PyException.Raise "ValueError" (ToString.toString "Negative number"))
    else
      if h_2 : num = (0 : Int) then 
        throw (PastaLean.PyException.Raise "ZeroDivisionError" (ToString.toString "Zero is not allowed"))
      else
        let p'_ret_1 := s! "Number is {num}"
        return p'_ret_1
  catch caught =>
    if (caught).OfKind == "ValueError" then 
      let e := caught
      let p'_ret_1 := s! "Caught ValueError: {e}"
      return p'_ret_1
    else
      if (caught).OfKind == "ZeroDivisionError" then 
        let e := caught
        let p'_ret_2 := s! "Caught ZeroDivisionError: {e}"
        return p'_ret_2
      else
        throw caught
  finally
    do
      let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg "Finally block executed"]

attribute [simp] try_with_else_finally

def try_with_else_finally'rn : Int → PastaLean.PyExcept String := fun (num : Int) ↦ do
  try
    if h_1 : num < (0 : Int) then 
      throw (PastaLean.PyException.Raise "ValueError" (ToString.toString "Negative number"))
    else
      if h_2 : num == (0 : Int) then 
        throw (PastaLean.PyException.Raise "ZeroDivisionError" (ToString.toString "Zero is not allowed"))
      else
        let p'_ret_1 := s! "Number is {num}"
        return p'_ret_1
  catch caught =>
    if (caught).OfKind == "ValueError" then 
      let e := caught
      let p'_ret_1 := s! "Caught ValueError: {e}"
      return p'_ret_1
    else
      if (caught).OfKind == "ZeroDivisionError" then 
        let e := caught
        let p'_ret_2 := s! "Caught ZeroDivisionError: {e}"
        return p'_ret_2
      else
        throw caught
  finally
    do
      let _ ← pyPrintIO [pyPrintArg "Finally block executed"]

def raise_error : Int → PastaLean.ProofMode.PyProofM String := fun (num : Int) ↦ do
  if h_1 : num < (0 : Int) then 
    throw (PastaLean.PyException.Raise "ValueError" (ToString.toString "Negative number"))
  else
    if h_2 : num = (0 : Int) then 
      throw (PastaLean.PyException.Raise "ZeroDivisionError" (ToString.toString "Zero is not allowed"))
    else
      let p'_ret_1 := s! "Number is {num}"
      return p'_ret_1

attribute [simp] raise_error

def raise_error'rn : Int → PastaLean.PyExcept String := fun (num : Int) ↦ do
  if h_1 : num < (0 : Int) then 
    throw (PastaLean.PyException.Raise "ValueError" (ToString.toString "Negative number"))
  else
    if h_2 : num == (0 : Int) then 
      throw (PastaLean.PyException.Raise "ZeroDivisionError" (ToString.toString "Zero is not allowed"))
    else
      let p'_ret_1 := s! "Number is {num}"
      return p'_ret_1

def catch_loop := fun (num : Int) ↦
  ((do
      for i in (PastaLean.pyRange num)do
        try
          if h_1 : i = (3 : Int) then 
            throw (PastaLean.PyException.Raise "ValueError" (ToString.toString "i cannot be 3"))
          else
            if h_2 : i = (5 : Int) then 
              throw (PastaLean.PyException.Raise "ZeroDivisionError" (ToString.toString "i cannot be 5"))
        catch caught =>
          if (caught).OfKind == "ValueError" then 
            let e := caught
            let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg s! "Caught ValueError at i={i }: {e}"]
          else
            if (caught).OfKind == "ZeroDivisionError" then 
              let e := caught
              let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg s! "Caught ZeroDivisionError at i={i }: {e}"]
            else
              throw caught) :
    PastaLean.ProofMode.PyProofM _)

attribute [simp] catch_loop

def catch_loop'rn := fun (num : Int) ↦
  ((do
      for i in (PastaLean.pyRange num)do
        try
          if h_1 : i == (3 : Int) then 
            throw (PastaLean.PyException.Raise "ValueError" (ToString.toString "i cannot be 3"))
          else
            if h_2 : i == (5 : Int) then 
              throw (PastaLean.PyException.Raise "ZeroDivisionError" (ToString.toString "i cannot be 5"))
        catch caught =>
          if (caught).OfKind == "ValueError" then 
            let e := caught
            let _ ← pyPrintIO [pyPrintArg s! "Caught ValueError at i={i }: {e}"]
          else
            if (caught).OfKind == "ZeroDivisionError" then 
              let e := caught
              let _ ← pyPrintIO [pyPrintArg s! "Caught ZeroDivisionError at i={i }: {e}"]
            else
              throw caught) :
    PastaLean.PyExcept _)

end PastaLean.User.Root

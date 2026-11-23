import PastaLean
import Libraries
import Std.Tactic.Do

open PastaLean
open Libraries
open Std.Do

set_option linter.all false

set_option maxHeartbeats 200000

namespace PastaLean.User.Root

def func := fun (a : PyAny) ↦ fun (b : PyAny) ↦ fun (c : PyAny) ↦
  (show PastaLean.PyAny from
    if PastaLean.pyTruthy (if PastaLean.pyTruthy a then if PastaLean.pyTruthy b then c else b else a) then
      if PastaLean.pyTruthy a then if PastaLean.pyTruthy b then c else b else a
    else if PastaLean.pyTruthy a then b else a)

attribute [simp] func

def func'rn := fun (a : PyAny) ↦ fun (b : PyAny) ↦ fun (c : PyAny) ↦
  (show PastaLean.PyAny from
    if PastaLean.pyTruthy (if PastaLean.pyTruthy a then if PastaLean.pyTruthy b then c else b else a) then
      if PastaLean.pyTruthy a then if PastaLean.pyTruthy b then c else b else a
    else if PastaLean.pyTruthy a then b else a)

end PastaLean.User.Root

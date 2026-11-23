import PastaLean
import Libraries
import Std.Tactic.Do

open PastaLean
open Libraries
open Std.Do

set_option linter.all false

set_option maxHeartbeats 200000

namespace PastaLean.User.Root

def f := fun (a : PyAny) ↦
  (show PastaLean.PyAny from if PastaLean.pyTruthy !PastaLean.pyTruthy a then a else !PastaLean.pyTruthy a)

attribute [simp] f

def f'rn := fun (a : PyAny) ↦
  (show PastaLean.PyAny from if PastaLean.pyTruthy !PastaLean.pyTruthy a then a else !PastaLean.pyTruthy a)

end PastaLean.User.Root

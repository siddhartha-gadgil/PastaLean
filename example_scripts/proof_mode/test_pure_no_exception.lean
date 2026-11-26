import PastaLean
import Libraries
import Std.Tactic.Do

open PastaLean
open Libraries
open Std.Do

set_option linter.all false

set_option maxHeartbeats 200000

namespace PastaLean.User.Root

-- Test: Pure computation (no IO, no exceptions)
def add := fun (a : PyAny) ↦ fun (b : PyAny) ↦ (show PastaLean.PyAny from a +ₚ b)

attribute [simp] add

def add'rn := fun (a : PyAny) ↦ fun (b : PyAny) ↦ (show PastaLean.PyAny from a +ₚ b)

end PastaLean.User.Root

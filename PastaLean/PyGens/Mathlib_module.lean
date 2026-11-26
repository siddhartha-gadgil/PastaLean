import PastaLean
import Libraries
import Std.Tactic.Do

open PastaLean
open Libraries
open Std.Do

set_option linter.all false

set_option maxHeartbeats 800000

-- A "library" Python module: it defines public functions/constants that another file
-- imports, plus private (`_`-prefixed) helpers that must NOT be importable.
--
-- When converted to Lean this becomes a module whose top-level `def`s are globally
-- available after `import`, except the `private def`s (the `_`/`__`-prefixed names).
def add := fun a ↦ fun b ↦ a +ₚ b

attribute [simp, taste_ingr] add

def add'rn := fun a ↦ fun b ↦ a +ₚ b

def scale := fun xs ↦ fun factor ↦ (PastaLean.pyIter xs).map fun x => x *ₚ factor

attribute [simp, taste_ingr] scale

def scale'rn := fun xs ↦ fun factor ↦ (PastaLean.pyIter xs).map fun x => x *ₚ factor

def PUBLIC_CONST :=
  (42 : Int)

def __version__ :=
  (1 : Int)

attribute [simp, taste_ingr] __version__

private def __version__'rn :=
  (1 : Int)

private def _internal_helper := fun x ↦ x +ₚ (1 : Int)

attribute [simp, taste_ingr] _internal_helper

private def _internal_helper'rn := fun x ↦ x +ₚ (1 : Int)

private def __SECRET :=
  (99 : Int)

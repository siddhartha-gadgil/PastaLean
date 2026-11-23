import PastaLean
import Libraries
import Std.Tactic.Do

open PastaLean
open Libraries
open Std.Do

set_option linter.all false

set_option maxHeartbeats 200000

namespace PastaLean.User.Root

-- Python privacy mirrors what `from module import *` excludes: any underscore-prefixed name
-- is private, EXCEPT dunders (`__x__`), which are the public protocol.
-- foo       -> public            __foo   -> private (strong / name-mangled)
-- _foo      -> private           __foo__ -> public  (dunder)
-- Private names become Lean `private def`s (genuinely non-importable); names are otherwise
-- preserved verbatim (`_foo` stays `_foo`).
def public_fn :=
  (1 : Int)

attribute [simp, taste_ingr] public_fn

def public_fn'rn :=
  (1 : Int)

private def _single_underscore :=
  (2 : Int)

attribute [simp, taste_ingr] _single_underscore

private def _single_underscore'rn :=
  (2 : Int)

private def __double_underscore :=
  (3 : Int)

attribute [simp, taste_ingr] __double_underscore

private def __double_underscore'rn :=
  (3 : Int)

def __dunder__ :=
  (4 : Int)

attribute [simp, taste_ingr] __dunder__

private def __dunder__'rn :=
  (4 : Int)

def PUBLIC_CONST :=
  (10 : Int)

private def _secret :=
  (20 : Int)

end PastaLean.User.Root

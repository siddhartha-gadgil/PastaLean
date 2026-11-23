import PastaLean
import Libraries
import Std.Tactic.Do

open PastaLean
open Libraries
open Std.Do

set_option linter.all false

set_option maxHeartbeats 200000

namespace PastaLean.User.Root

def l :=
  PastaLean.pyStringSplit "gh yy uu"

def t :=
  PastaLean.pyStringJoin " " l

def s :=
  PastaLean.pyStringStrip t "g"

def b1 :=
  PastaLean.pyStringStartswith s "h"

def b2 :=
  PastaLean.pyStringEndswith s "u"

def s1 :=
  PastaLean.pyStringUpper s

def s2 :=
  PastaLean.pyStringLower s

end PastaLean.User.Root

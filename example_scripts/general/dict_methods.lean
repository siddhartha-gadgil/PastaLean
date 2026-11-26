import PastaLean
import Libraries
import Std.Tactic.Do

open PastaLean
open Libraries
open Std.Do

set_option linter.all false

set_option maxHeartbeats 200000

namespace PastaLean.User.Root

def dict_views :=
  let d := (Std.HashMap.ofList [("a", (1 : Int)), ("b", (2 : Int)), ("c", (3 : Int))] : Std.HashMap String Int)
  let its := (PastaLean.pyItems d : List (String × Int))
  let ks := (PastaLean.pyKeys d : List String)
  let vs := (PastaLean.pyAnys d : List Int)
  (its, (ks, vs))

attribute [simp, taste_ingr] dict_views

def dict_views'rn :=
  let d := (Std.HashMap.ofList [("a", (1 : Int)), ("b", (2 : Int)), ("c", (3 : Int))] : Std.HashMap String Int)
  let its := (PastaLean.pyItems d : List (String × Int))
  let ks := (PastaLean.pyKeys d : List String)
  let vs := (PastaLean.pyAnys d : List Int)
  (its, (ks, vs))

def dict_len :=
  let d := (Std.HashMap.ofList [("x", (10 : Int)), ("y", (20 : Int))] : Std.HashMap String Int)
  PastaLean.pyLen d

attribute [simp, taste_ingr] dict_len

def dict_len'rn :=
  let d := (Std.HashMap.ofList [("x", (10 : Int)), ("y", (20 : Int))] : Std.HashMap String Int)
  PastaLean.pyLen d

def dict_spread_merge :=
  -- `{**d1, **d2}` merges dicts (later wins on duplicate keys); a bare `k: v` mixed with spreads
  -- overrides too. Here "b" resolves to 20 (from d2), "d" to 99.
  let d1 := (Std.HashMap.ofList [("a", (1 : Int)), ("b", (2 : Int))] : Std.HashMap String Int)
  let d2 := (Std.HashMap.ofList [("b", (20 : Int)), ("c", (3 : Int))] : Std.HashMap String Int)
  Std.HashMap.ofList (Std.HashMap.toList d1 ++ Std.HashMap.toList d2 ++ [("d", (99 : Int))])

attribute [simp, taste_ingr] dict_spread_merge

def dict_spread_merge'rn :=
  -- `{**d1, **d2}` merges dicts (later wins on duplicate keys); a bare `k: v` mixed with spreads
  -- overrides too. Here "b" resolves to 20 (from d2), "d" to 99.
  let d1 := (Std.HashMap.ofList [("a", (1 : Int)), ("b", (2 : Int))] : Std.HashMap String Int)
  let d2 := (Std.HashMap.ofList [("b", (20 : Int)), ("c", (3 : Int))] : Std.HashMap String Int)
  Std.HashMap.ofList (Std.HashMap.toList d1 ++ Std.HashMap.toList d2 ++ [("d", (99 : Int))])

end PastaLean.User.Root

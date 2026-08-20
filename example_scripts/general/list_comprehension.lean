import PastaLean
import Libraries
import Std.Tactic.Do

open PastaLean
open Libraries
open Std.Do

set_option linter.all false
set_option mvcgen.warning false

set_option maxHeartbeats 0

def simple_lc :=
  (PastaLean.pyRange (10 : Int)).map fun x => x

attribute [simp, taste_ingr] simple_lc

def simple_lc'rn :=
  (PastaLean.pyRange (10 : Int)).map fun x => x

def lc_with_condition :=
  (List.filter (fun x => x %ₚ (2 : Int) = (0 : Int)) (PastaLean.pyRange (10 : Int))).map fun x => x

attribute [simp, taste_ingr] lc_with_condition

def lc_with_condition'rn :=
  (List.filter (fun x => x %ₚ (2 : Int) == (0 : Int)) (PastaLean.pyRange (10 : Int))).map fun x => x

def lc_with_array :=
  let a := ([(1 : Int), (2 : Int), (3 : Int), (4 : Int), (5 : Int)] : List Int)
  (PastaLean.pyIter a).map fun x => x *ₚ x

attribute [simp, taste_ingr] lc_with_array

def lc_with_array'rn :=
  let a := ([(1 : Int), (2 : Int), (3 : Int), (4 : Int), (5 : Int)] : List Int)
  (PastaLean.pyIter a).map fun x => x *ₚ x

def lc_with_string :=
  let s := ("hello" : String)
  (PastaLean.pyIter (s +ₚ " world")).map fun char => char

attribute [simp, taste_ingr] lc_with_string

def lc_with_string'rn :=
  let s := ("hello" : String)
  (PastaLean.pyIter (s +ₚ " world")).map fun char => char

def nested_lc :=
  let a := ((PastaLean.pyRange (3 : Int)).map fun _ => (PastaLean.pyRange (5 : Int)).map fun x => x : List (List Int))
  a

attribute [simp, taste_ingr] nested_lc

def nested_lc'rn :=
  let a := ((PastaLean.pyRange (3 : Int)).map fun _ => (PastaLean.pyRange (5 : Int)).map fun x => x : List (List Int))
  a

private def _lc_with_function_call'add_one := fun (x : Int) ↦ x +ₚ (1 : Int)

attribute [simp, taste_ingr] _lc_with_function_call'add_one

def lc_with_function_call :=
  let a := (PastaLean.pyRange (5 : Int)).map fun x => _lc_with_function_call'add_one x
  a

attribute [simp, taste_ingr] lc_with_function_call

private def _lc_with_function_call'add_one'rn := fun (x : Int) ↦ x +ₚ (1 : Int)

def lc_with_function_call'rn :=
  let a := (PastaLean.pyRange (5 : Int)).map fun x => _lc_with_function_call'add_one'rn x
  a

def lc_with_multiple_conditions :=
  (List.filter (fun x => x %ₚ (2 : Int) = (0 : Int) ∧ x %ₚ (3 : Int) = (0 : Int)) (PastaLean.pyRange (20 : Int))).map
    fun x => x

attribute [simp, taste_ingr] lc_with_multiple_conditions

def lc_with_multiple_conditions'rn :=
  (List.filter (fun x => x %ₚ (2 : Int) == (0 : Int) && x %ₚ (3 : Int) == (0 : Int))
        (PastaLean.pyRange (20 : Int))).map
    fun x => x

def lc_with_tuple_unpacking :=
  let pairs := ([((1 : Int), "a"), ((2 : Int), "b"), ((3 : Int), "c")] : List (Int × String))
  let another_pairs := ([((4 : Int), "d"), ((5 : Int), "e")] : List (Int × String))
  let another_pairs :=
    ((List.filter
            (fun _pair_3 =>
              let num := Prod.fst _pair_3;
              let char := Prod.snd _pair_3;
              num %ₚ (2 : Int) = (0 : Int))
            (PastaLean.pyIter another_pairs)).map
        fun _pair_2 =>
        let num := Prod.fst _pair_2;
        let char := Prod.snd _pair_2;
        (num, char) :
      List (Int × String))
  let _ := another_pairs
  (PastaLean.pyIter pairs).map fun _pair_1 =>
    let num := Prod.fst _pair_1;
    let char := Prod.snd _pair_1;
    s! "{num }:{char}"

attribute [simp, taste_ingr] lc_with_tuple_unpacking

def lc_with_tuple_unpacking'rn :=
  let pairs := ([((1 : Int), "a"), ((2 : Int), "b"), ((3 : Int), "c")] : List (Int × String))
  let another_pairs := ([((4 : Int), "d"), ((5 : Int), "e")] : List (Int × String))
  let another_pairs :=
    ((List.filter
            (fun _pair_3 =>
              let num := Prod.fst _pair_3;
              let char := Prod.snd _pair_3;
              num %ₚ (2 : Int) == (0 : Int))
            (PastaLean.pyIter another_pairs)).map
        fun _pair_2 =>
        let num := Prod.fst _pair_2;
        let char := Prod.snd _pair_2;
        (num, char) :
      List (Int × String))
  let _ := another_pairs
  (PastaLean.pyIter pairs).map fun _pair_1 =>
    let num := Prod.fst _pair_1;
    let char := Prod.snd _pair_1;
    s! "{num }:{char}"

def lc_with_nested_conditions :=
  (List.filter (fun x => x %ₚ (2 : Int) = (0 : Int) ∧ x %ₚ (3 : Int) = (0 : Int) ∨ x %ₚ (5 : Int) = (0 : Int))
        (PastaLean.pyRange (20 : Int))).map
    fun x => x

attribute [simp, taste_ingr] lc_with_nested_conditions

def lc_with_nested_conditions'rn :=
  (List.filter (fun x => x %ₚ (2 : Int) == (0 : Int) && x %ₚ (3 : Int) == (0 : Int) || x %ₚ (5 : Int) == (0 : Int))
        (PastaLean.pyRange (20 : Int))).map
    fun x => x

def lc_with_nested_tuple_unpacking :=
  let triples :=
    ([((1 : Int), ((2 : Int), (3 : Int))), ((4 : Int), ((5 : Int), (6 : Int))), ((7 : Int), ((8 : Int), (9 : Int)))] :
      List (Int × Int × Int))
  (PastaLean.pyIter triples).map fun _pair_1 =>
    let a := Prod.fst _pair_1;
    let _pair_2 := Prod.snd _pair_1;
    let b := Prod.fst _pair_2;
    let c := Prod.snd _pair_2;
    a +ₚ b +ₚ c

attribute [simp, taste_ingr] lc_with_nested_tuple_unpacking

def lc_with_nested_tuple_unpacking'rn :=
  let triples :=
    ([((1 : Int), ((2 : Int), (3 : Int))), ((4 : Int), ((5 : Int), (6 : Int))), ((7 : Int), ((8 : Int), (9 : Int)))] :
      List (Int × Int × Int))
  (PastaLean.pyIter triples).map fun _pair_1 =>
    let a := Prod.fst _pair_1;
    let _pair_2 := Prod.snd _pair_1;
    let b := Prod.fst _pair_2;
    let c := Prod.snd _pair_2;
    a +ₚ b +ₚ c

def dc_with_nested_tuple_unpacking :=
  let triples := ([((1 : Int), ((2 : Int), (3 : Int))), ((4 : Int), ((5 : Int), (6 : Int)))] : List (Int × Int × Int))
  Std.HashMap.ofList
    ((PastaLean.pyIter triples).map fun _pair_1 =>
      let a := Prod.fst _pair_1;
      let _pair_2 := Prod.snd _pair_1;
      let b := Prod.fst _pair_2;
      let c := Prod.snd _pair_2;
      (a, b *ₚ c))

attribute [simp, taste_ingr] dc_with_nested_tuple_unpacking

def dc_with_nested_tuple_unpacking'rn :=
  let triples := ([((1 : Int), ((2 : Int), (3 : Int))), ((4 : Int), ((5 : Int), (6 : Int)))] : List (Int × Int × Int))
  Std.HashMap.ofList
    ((PastaLean.pyIter triples).map fun _pair_1 =>
      let a := Prod.fst _pair_1;
      let _pair_2 := Prod.snd _pair_1;
      let b := Prod.fst _pair_2;
      let c := Prod.snd _pair_2;
      (a, b *ₚ c))

def lc_with_side_effects :=
  Id.run
    (do
      let mut result : List Int := []
      for x in (PastaLean.pyRange (5 : Int)) do
        result := PastaLean.pyAppend result (x *ₚ x)
      let __py_ret_1 := (PastaLean.pyIter result).map fun y => y
      return __py_ret_1)

attribute [simp, taste_ingr] lc_with_side_effects

def lc_with_side_effects'rn :=
  Id.run
    (do
      let mut result : List Int := []
      for x in (PastaLean.pyRange (5 : Int)) do
        result := PastaLean.pyAppend result (x *ₚ x)
      let __py_ret_1 := (PastaLean.pyIter result).map fun y => y
      return __py_ret_1)

def lc_with_generator_expression :=
  (PastaLean.pyIter ((PastaLean.pyRange (5 : Int)).map fun i => i)).map fun x => x *ₚ x

attribute [simp, taste_ingr] lc_with_generator_expression

def lc_with_generator_expression'rn :=
  (PastaLean.pyIter ((PastaLean.pyRange (5 : Int)).map fun i => i)).map fun x => x *ₚ x

def lc_with_if_else :=
  let a := ((PastaLean.pyRange (10 : Int)).map fun x => x : List Int)
  (PastaLean.pyRange (10 : Int)).map fun x => if x %ₚ (2 : Int) = (0 : Int) then x else -x

attribute [simp, taste_ingr] lc_with_if_else

def lc_with_if_else'rn :=
  let a := ((PastaLean.pyRange (10 : Int)).map fun x => x : List Int)
  (PastaLean.pyRange (10 : Int)).map fun x => if x %ₚ (2 : Int) == (0 : Int) then x else -x

def lc_with_string_literal_list :=
  (PastaLean.pyIter ["me", "you"]).map fun x => x

attribute [simp, taste_ingr] lc_with_string_literal_list

def lc_with_string_literal_list'rn :=
  (PastaLean.pyIter ["me", "you"]).map fun x => x

def lc_with_dict :=
  let d := (Std.HashMap.ofList [("a", (1 : Int)), ("b", (2 : Int)), ("c", (3 : Int))] : Std.HashMap String Int)
  (PastaLean.pyIter (PastaLean.pyItems d)).map fun _pair_1 =>
    let k := Prod.fst _pair_1;
    let v := Prod.snd _pair_1;
    s! "{k }:{v}"

attribute [simp, taste_ingr] lc_with_dict

def lc_with_dict'rn :=
  let d := (Std.HashMap.ofList [("a", (1 : Int)), ("b", (2 : Int)), ("c", (3 : Int))] : Std.HashMap String Int)
  (PastaLean.pyIter (PastaLean.pyItems d)).map fun _pair_1 =>
    let k := Prod.fst _pair_1;
    let v := Prod.snd _pair_1;
    s! "{k }:{v}"

def lc_multi_list :=
  let ll :=
    ((PastaLean.pyIter [[(1 : Int), (2 : Int)], [(3 : Int), (4 : Int)]]).flatMap fun a =>
        (PastaLean.pyIter a).flatMap fun x => (PastaLean.pyIter a).map fun y => x *ₚ y :
      List Int)
  let lt := ((PastaLean.pyIter ll).flatMap fun x => (PastaLean.pyIter ll).map fun y => x *ₚ y : List Int)
  (ll, lt)

attribute [simp, taste_ingr] lc_multi_list

def lc_multi_list'rn :=
  let ll :=
    ((PastaLean.pyIter [[(1 : Int), (2 : Int)], [(3 : Int), (4 : Int)]]).flatMap fun a =>
        (PastaLean.pyIter a).flatMap fun x => (PastaLean.pyIter a).map fun y => x *ₚ y :
      List Int)
  let lt := ((PastaLean.pyIter ll).flatMap fun x => (PastaLean.pyIter ll).map fun y => x *ₚ y : List Int)
  (ll, lt)

def lc_multi_invoke :=
  let a :=
    ((PastaLean.pyRange (5 : Int)).flatMap fun x =>
        (PastaLean.pyRange (5 : Int)).flatMap fun y => (PastaLean.pyRange (5 : Int)).map fun z => x *ₚ y *ₚ z :
      List Int)
  let b :=
    ((PastaLean.pyRange (5 : Int)).flatMap fun x =>
        (PastaLean.pyRange (5 : Int)).flatMap fun y => (PastaLean.pyRange (5 : Int)).map fun z => (x, (y, z)) :
      List (Int × Int × Int))
  (a, b)

attribute [simp, taste_ingr] lc_multi_invoke

def lc_multi_invoke'rn :=
  let a :=
    ((PastaLean.pyRange (5 : Int)).flatMap fun x =>
        (PastaLean.pyRange (5 : Int)).flatMap fun y => (PastaLean.pyRange (5 : Int)).map fun z => x *ₚ y *ₚ z :
      List Int)
  let b :=
    ((PastaLean.pyRange (5 : Int)).flatMap fun x =>
        (PastaLean.pyRange (5 : Int)).flatMap fun y => (PastaLean.pyRange (5 : Int)).map fun z => (x, (y, z)) :
      List (Int × Int × Int))
  (a, b)
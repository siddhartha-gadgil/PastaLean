import PastaLean.PyAPI.PyPrint

open PastaLean

/-- info: "hello" -/
#guard_msgs in
#eval pyPrintStr "hello"

/-- info: "True" -/
#guard_msgs in
#eval pyPrintStr true

/-- info: "None" -/
#guard_msgs in
#eval pyPrintStr (none : Option Int)

/-- info: "[1, 2, 3]" -/
#guard_msgs in
#eval pyPrintStr ([1, 2, 3] : List Int)

/-- info: "(7, 'ok')" -/
#guard_msgs in
#eval pyPrintStr ((7 : Int), "ok")

/-- info: "{'a': 1, 'b': 2}" -/
#guard_msgs in
#eval pyPrintStr (Std.HashMap.ofList [("b", 2), ("a", 1)] : Std.HashMap String Int)

/-- info: "<function>" -/
#guard_msgs in
#eval pyPrintStr (fun x : Int => x + 1)

/-- info: "['a', 'b', 'c']" -/
#guard_msgs in
#eval pyPrintStr (['a', 'b', 'c'] : List Char)

/-! A container renders its elements with `repr`, so a string gains Python's quotes inside one while
`print("a")` stays bare. Quote choice and escaping follow CPython. -/

/-- info: "['a', 'b']" -/
#guard_msgs in
#eval pyPrintStr (["a", "b"] : List String)

/-- info: "[\"it's\", 'say \"hi\"']" -/
#guard_msgs in
#eval pyPrintStr (["it's", "say \"hi\""] : List String)

/-- info: "[None, 'x']" -/
#guard_msgs in
#eval pyPrintStr ([none, some "x"] : List (Option String))

/-- info: print me -/
#guard_msgs in
#eval pyPrintIO ["print me"]

/-- info: alpha 3 True -/
#guard_msgs in
#eval pyPrintIO ["alpha", (3 : Int), true]

/-- info: left|right! -/
#guard_msgs in
#eval pyPrintIO ["left", "right"] "|" "!"

/-- info: sum 3 4 -/
#guard_msgs in
#eval pyPrintIO ["sum", (3 : Int), (4 : Int)]

/--
info: [4, 5]
---
info: 9
-/
#guard_msgs in
#eval (pyPrintIO [[4, 5]] *> pure (9 : Int))

/-! Python-style `repr` for floats: shortest round-tripping decimal, `.0` on integers (not the
6-digit `%f` `3.000000` / truncated `0.285714`). -/

/-- info: "3.0" -/
#guard_msgs in
#eval pyFloatRepr (3.0 : Float)

/-- info: "1.0" -/
#guard_msgs in
#eval pyFloatRepr (1.0 : Float)

/-- info: "0.2857142857142857" -/
#guard_msgs in
#eval pyFloatRepr ((2 : Float) / 7)

/-- info: "3.141592653589793" -/
#guard_msgs in
#eval pyFloatRepr (3.141592653589793 : Float)

/-- info: "-1.5" -/
#guard_msgs in
#eval pyFloatRepr (-1.5 : Float)

/-- info: "100.0" -/
#guard_msgs in
#eval pyFloatRepr (100.0 : Float)

/-- info: "1e+20" -/
#guard_msgs in
#eval pyFloatRepr (1e20 : Float)

/-- info: "0.0" -/
#guard_msgs in
#eval pyFloatRepr (0.0 : Float)

-- Large-float `:.2f` must not overflow `UInt64` (regression: `bignum*0.5` printed `UInt64.max/100`).
/-- info: "6172839450617283584.00" -/
#guard_msgs in
#eval pyFormatSpec (6172839450617283584.0 : Float) ".2f"

/-- info: "49382716054938271744.00" -/
#guard_msgs in
#eval pyFormatSpec (49382716054938271744.0 : Float) ".2f"

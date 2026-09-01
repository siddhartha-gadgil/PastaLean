import Libraries.operator.OperatorDef

namespace Libraries.operator

/-- Map supported `operator` module members to their Lean runtime functions. The dunder aliases
(`__add__`, …) name the same functions, as in CPython. -/
def pythonOperatorMemberMap? (member : String) : Option Lean.Name :=
  match member with
  | "add" | "__add__" => some ``Libraries.operator.pyOperatorAdd
  | "sub" | "__sub__" => some ``Libraries.operator.pyOperatorSub
  | "mul" | "__mul__" => some ``Libraries.operator.pyOperatorMul
  | "truediv" | "__truediv__" => some ``Libraries.operator.pyOperatorTrueDiv
  | "floordiv" | "__floordiv__" => some ``Libraries.operator.pyOperatorFloorDiv
  | "mod" | "__mod__" => some ``Libraries.operator.pyOperatorMod
  | "pow" | "__pow__" => some ``Libraries.operator.pyOperatorPow
  | "and_" | "__and__" => some ``Libraries.operator.pyOperatorAnd
  | "or_" | "__or__" => some ``Libraries.operator.pyOperatorOr
  | "xor" | "__xor__" => some ``Libraries.operator.pyOperatorXor
  | "lshift" | "__lshift__" => some ``Libraries.operator.pyOperatorLShift
  | "rshift" | "__rshift__" => some ``Libraries.operator.pyOperatorRShift
  | "neg" | "__neg__" => some ``Libraries.operator.pyOperatorNeg
  | "pos" | "__pos__" => some ``Libraries.operator.pyOperatorPos
  | "abs" | "__abs__" => some ``Libraries.operator.pyOperatorAbs
  | "invert" | "inv" | "__invert__" => some ``Libraries.operator.pyOperatorInvert
  | "eq" | "__eq__" => some ``Libraries.operator.pyOperatorEq
  | "ne" | "__ne__" => some ``Libraries.operator.pyOperatorNe
  | "lt" | "__lt__" => some ``Libraries.operator.pyOperatorLt
  | "le" | "__le__" => some ``Libraries.operator.pyOperatorLe
  | "gt" | "__gt__" => some ``Libraries.operator.pyOperatorGt
  | "ge" | "__ge__" => some ``Libraries.operator.pyOperatorGe
  | "not_" => some ``Libraries.operator.pyOperatorNot
  | "truth" => some ``Libraries.operator.pyOperatorTruth
  | "concat" | "__concat__" => some ``Libraries.operator.pyOperatorConcat
  | "contains" | "__contains__" => some ``Libraries.operator.pyOperatorContains
  | _ => none

end Libraries.operator

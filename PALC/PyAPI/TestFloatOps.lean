import PastaLean.PyAPI.FloatOps
import PastaLean.PyAPI.Builtins

open PastaLean

/-! Python float semantics in the run twin, pinned to CPython's results (bit patterns from CPython). -/

-- `//` and `%` follow CPython's `fmod`-based `float_divmod`, not `floor(a / b)`.
#guard pyFloatFloorDivPy 1.0 0.1 == 9.0
#guard pyFloatFloorDivPy (-189.0) 0.3 == -631.0
#guard (pyFloatModPy (-800.0) 1.55).toBits == 4608758678669597185
#guard (pyFloatModPy 52.0 (-2.0)).toBits == (-0.0 : Float).toBits
#guard pyFloatModPy 5.0 (-1.0 / 0.0) == -1.0 / 0.0
#guard pyFloatFloorDivPy (-5.0) (1.0 / 0.0) == -1.0

-- Correctly rounded int → float and int / int.
#guard (pyIntTrueDiv (-6211380254616036683) 25).toBits == 14090520260105811038
#guard (pyIntToFloat (2 ^ 64 + 1)).toBits == 4895412794951729152
#guard (pyIntTrueDiv 0 (-31)).toBits == (-0.0 : Float).toBits

-- Exact conversions to int, any magnitude.
#guard pyFloatToInt 1.7976931348623157e308 % 1000 == 368
#guard pyFloatToInt (-0.9) == 0
#guard pyFloatFloorInt (-3.3e-295) == -1
#guard pyFloatRoundInt 2.5 == 2 && pyFloatRoundInt (-3.5) == -4

-- `round(x, n)`, `hypot`, `float(str)`, `abs`.
#guard (pyFloatRoundDigits 2.675 2).toBits == 4613194724302557020
#guard (pyFloatRoundDigits (-0.4) 0).toBits == (-0.0 : Float).toBits
#guard (pyFloatHypot (-90.3) (-5.13)).toBits == 4636064960357778067
#guard (pyFloatHypot 1e308 1e308).toBits == 9216947043162673653
#guard (pyParseFloat " 1_000.5e-3 ").toBits == 4607184670599831093
#guard (pyParseFloat "-InFiNiTy") == -1.0 / 0.0
#guard (pyAbs (-0.0 : Float)).toBits == (0.0 : Float).toBits

-- The exact twin's `int()` truncates toward zero, like Python.
#guard pyInt (-5/2 : ℚ) == -2 && pyInt (5/2 : ℚ) == 2

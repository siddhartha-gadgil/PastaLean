import PastaLean.PyAPI.PyPanic
import PastaLean.Imports

namespace PastaLean

/-!
This is for python's `chr()` builtin, which returns a string representing a character whose Unicode code point is the integer passed. For example, `chr(97)` returns the string `'a'`.
-/

def pyChr (n : Int) : String :=
  if n < 0 || n > 0x10FFFF then
    PastaLean.pyPanic "ValueError: chr() arg not in range(0x110000)"
  else
    String.singleton (Char.ofNat n.toNat)


/-!
This is for python's `ord()` builtin, which returns an integer representing the Unicode code point of a given character. For example, `ord('a')` returns `97`.
-/

-- Returns `Int` (not `Nat`): Python's `ord` yields an `int`, and code negates it (`-ord(c)`) or
-- subtracts code points (`ord(c) - ord('a')`, which can be negative) — both ill-typed on `Nat`.
def pyOrd (s : String) : Int :=
  if s.length != 1 then
    PastaLean.pyPanic s!"TypeError: ord() expected a character, but string of length {s.length} found"
  else
    (Char.toNat (String.Pos.Raw.get! s 0) : Int)

end PastaLean

import Libraries.re.Parser

/-!
# Strings a regular expression matches

For the literal pool: a pattern the program compiles (`re.compile(r"…", flags)`) is expanded into a
bounded set of strings it matches — each alternative, each quantifier at its minimum and one or two
more, each class by representative characters — plus the characters its classes name. Mutating those
strings (one inserted `.`, a dropped sign) is how the search reaches the inputs a regex almost accepts.
-/

namespace PastaLean.Refute

open Libraries.re

/-- Representative members of a class item. -/
def classItemChars : ClassItem → List Char
  | .single c => [c]
  | .range lo hi => if lo == hi then [lo] else [lo, hi]
  | .digit false => ['0', '5']
  | .digit true => ['a']
  | .space false => [' ']
  | .space true => ['a']
  | .word false => ['a', '0']
  | .word true => [' ']

def classMatches (items : List ClassItem) (c : Char) : Bool :=
  items.any fun
    | .single x => x == c
    | .range lo hi => lo ≤ c && c ≤ hi
    | .digit n => c.isDigit != n
    | .space n => isSpaceChar c != n
    | .word n => isWordChar c != n

/-- The lists' members taken round-robin, so every alternative is represented under a cap. -/
partial def interleave : List (List String) → List String
  | [] => []
  | ls => ls.filterMap List.head? ++ interleave ((ls.map List.tail).filter (!·.isEmpty))

/-- At most `cap` concatenations of a member of `xs` with a member of `ys`, round-robin over `xs`. -/
def productCap (cap : Nat) (xs ys : List String) : List String :=
  ((interleave (xs.map fun x => ys.map (x ++ ·))).eraseDups).take cap

mutual

/-- Strings matched by one node: at most `per` of them, so a sequence's product stays small. -/
partial def nodeLang (per : Nat) : Node → List String
  | .char c => [c.toString]
  | .any => ["a"]
  | .cls items false => ((items.flatMap classItemChars).eraseDups.map (·.toString)).take per
  | .cls items true =>
      (((" a0.-xZ_".toList).filter (!classMatches items ·)).take 2).map (·.toString)
  | .group _ alts => (altsLang per alts).take (2 * per)
  | .rep n lo hi _ =>
      let one := nodeLang per n
      let counts := [lo, lo + 1, lo + 2].filter fun k => hi.all (k ≤ ·)
      (interleave (counts.map fun k => (List.replicate k one).foldl (productCap per) [""])).eraseDups.take per
  | _ => [""]

partial def altsLang (per : Nat) (alts : List (List Node)) : List String :=
  (interleave (alts.map fun seq => seq.foldl (fun acc n => productCap (per * per) acc (nodeLang per n)) [""])).eraseDups

end

partial def nodeClassChars : Node → List Char
  | .cls items _ => items.flatMap classItemChars
  | .group _ alts | .look _ _ alts => alts.flatMap (·.flatMap nodeClassChars)
  | .rep n .. => nodeClassChars n
  | .char c => [c]
  | _ => []

/-- Members of `pattern` (compiled with `flags`) and the characters it names, for the literal pool. -/
def regexPoolStrings (pattern : String) (flags : Int) (per : Nat := 8) : List String :=
  let prog := (compile pattern flags).prog
  let chars := (prog.flatMap (·.flatMap nodeClassChars)).eraseDups.filter (!·.isWhitespace)
  (altsLang per prog).take 96 ++ chars.map (·.toString)

end PastaLean.Refute

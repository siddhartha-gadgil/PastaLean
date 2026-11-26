import Libraries.re.Api
import Libraries.Behaviour

namespace Libraries.re
open Libraries

/-- Map supported `re` members to their definitions in `Libraries/re/*.lean`. Methods of a compiled pattern or a
match (`p.fullmatch(s)`, `m.group(1)`) resolve by dot notation on `Pattern`/`Match`. -/
def pythonReMemberMap? (member : String) : Option Lean.Name :=
  match member with
  | "compile" => some ``Libraries.re.compile
  | "match" => some ``Libraries.re.match
  | "fullmatch" => some ``Libraries.re.fullmatch
  | "search" => some ``Libraries.re.search
  | "findall" => some ``Libraries.re.findall
  | "sub" => some ``Libraries.re.sub
  | "split" => some ``Libraries.re.split
  | "escape" => some ``Libraries.re.escape
  | "IGNORECASE" => some ``Libraries.re.IGNORECASE
  | "I" => some ``Libraries.re.I
  | "MULTILINE" => some ``Libraries.re.MULTILINE
  | "M" => some ``Libraries.re.M
  | "DOTALL" => some ``Libraries.re.DOTALL
  | "S" => some ``Libraries.re.S
  | "VERBOSE" => some ``Libraries.re.VERBOSE
  | "X" => some ``Libraries.re.X
  | "ASCII" => some ``Libraries.re.ASCII
  | "A" => some ``Libraries.re.A
  | _ => none

end Libraries.re

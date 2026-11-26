import Libraries.json.Decoder
import Libraries.json.Encoder
import Libraries.Behaviour

namespace Libraries.json
open Libraries

/-- Map supported `json` members to their definitions in `Decoder.lean`/`Encoder.lean`. -/
def pythonJsonMemberMap? (member : String) : Option Lean.Name :=
  match member with
  | "loads" => some ``Libraries.json.loads
  | "dumps" => some ``Libraries.json.dumps
  | _ => none

/-- Members that raise (`JSONDecodeError` is a `ValueError`, unserializable values a `TypeError`). -/
def jsonRaisingMembers : List String := ["loads", "dumps"]

end Libraries.json

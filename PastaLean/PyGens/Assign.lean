import PastaLean.PyGens.Core.Utils
import PastaLean.PyGens.Calls.CallEffects

open Lean Meta Elab Term Qq Std

namespace PastaLean

/-- Read a simple two-name tuple assignment target when present. -/
def tupleAssignTargetNames? (target : Json) : PygenM (Option (TSyntax `ident × TSyntax `ident)) := do
  unless jsonNodeType? target == some "Tuple" do
    return none
  let .ok elts := target.getObjValAs? (Array Json) "elts" | throwError
    s!"Tuple assignment target does not have an 'elts' field or it is not a JSON value: {target}"
  match elts[0]?, elts[1]? with
  | some leftJson, some rightJson =>
      if jsonNodeType? leftJson == some "Name" && jsonNodeType? rightJson == some "Name" then
        let leftIdent ← getCode leftJson `ident
        let rightIdent ← getCode rightJson `ident
        return some (leftIdent, rightIdent)
      else
        throwError "Only two-name tuple assignment targets are supported right now."
  | _, _ =>
      throwError "Only two-element tuple assignment targets are supported right now."

/-- Emit either a fresh `let mut` or a reassignment for one local binding. -/
def bindOrAssignLocal (nameIdent : TSyntax `ident) (rhs : TSyntax `term) : PygenM (TSyntax `doElem) := do
  if ← hasVar nameIdent.getId then
    `(doElem| $nameIdent:ident := $rhs)
  else
    let stx ← `(doElem| let mut $nameIdent:ident := $rhs)
    addVar nameIdent.getId
    pure stx

/-- Simple returned expressions can stay unparenthesized; more complex or effectful ones
keep parentheses so Lean parses multiline `return` expressions reliably. -/
def shouldParenthesizeReturnValue (value : Json) : Bool :=
  if jsonUsesMonadicEffect value then
    true
  else
    match jsonNodeType? value with
    | some "Name" => false
    | some "Constant" => false
    | some "Attribute" => false
    | _ => true

@[pygen "Assign"]
def assignSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
    | `command, json => do
        let .ok target := json.getObjVal? "target" | throwError
          s!"Assign node does not have a 'target' field or it is not a JSON value: {json}"
        let nameIdent ← getCode target `ident
        let .ok value := json.getObjVal? "value" | throwError
          s!"Assign node does not have a 'value' field or it is not a JSON value: {json}"
        let valueStx ← getCode value `term
        `(def $nameIdent := $valueStx)
    | `doElem, json => do
        let .ok target := json.getObjVal? "target" | throwError
          s!"Assign node does not have a 'target' field or it is not a JSON value: {json}"
        let .ok value := json.getObjVal? "value" | throwError
          s!"Assign node does not have a 'value' field or it is not a JSON value: {json}"
        match ← tupleAssignTargetNames? target with
        | some (leftIdent, rightIdent) => do
            let valueStx ← getCode value `term
            let leftFresh := !(← hasVar leftIdent.getId)
            let rightFresh := !(← hasVar rightIdent.getId)
            if leftFresh && rightFresh then
              addVar leftIdent.getId
              addVar rightIdent.getId
              if jsonUsesIOEffect value || jsonUsesMonadicEffect value then
                `(doElem| let ($leftIdent, $rightIdent) ← $valueStx:term)
              else
                `(doElem| let ($leftIdent, $rightIdent) := $valueStx)
            else
              let tmpIdent := mkIdent (← freshName `__unpack_tmp)
              let bindTmp ←
                if jsonUsesIOEffect value || jsonUsesMonadicEffect value then
                  `(doElem| let $tmpIdent:ident ← $valueStx:term)
                else
                  `(doElem| let $tmpIdent:ident := $valueStx)
              let leftBind ← bindOrAssignLocal leftIdent (← `(Prod.fst $tmpIdent))
              let rightBind ← bindOrAssignLocal rightIdent (← `(Prod.snd $tmpIdent))
              `(doElem| do
                $bindTmp:doElem
                $leftBind:doElem
                $rightBind:doElem)
        | none => do
            let nameIdent ← getCode target `ident
            let rhs ←
              if jsonUsesIOEffect value then
                inlineIOTerm value
              else
                let valueStx ← getCode value `term
                if jsonUsesMonadicEffect value then
                  `((← $valueStx:term))
                else
                  pure valueStx
            bindOrAssignLocal nameIdent rhs
    | _, _ => throwError s!"Unsupported syntax category for Assign node"

/--
`AnnAssign` represents Python's annotated assignment syntax (`x : T = v` or `x : T`).
The remaining declaration-only form is currently treated as a no-op in `do` blocks, and
rejected at top level until the backend grows explicit type-directed declarations.
-/
@[pygen "AnnAssign"]
def annAssignSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
    | `command, json => do
        let .ok value? := json.getObjVal? "value" | throwError
          s!"AnnAssign node does not have a 'value' field or it is not a JSON value: {json}"
        match value? with
        | .null =>
            throwError "Declaration-only annotated assignments are not yet supported at top level."
        | _ =>
            let targetJson := Json.mkObj [("node_type", Json.str "Assign")]
            let json := targetJson.mergeObj json
            assignSyntax `command json
    | `doElem, json => do
        let .ok value? := json.getObjVal? "value" | throwError
          s!"AnnAssign node does not have a 'value' field or it is not a JSON value: {json}"
        match value? with
        | .null =>
            `(doElem| let _ := ())
        | _ =>
            let targetJson := Json.mkObj [("node_type", Json.str "Assign")]
            let json := targetJson.mergeObj json
            assignSyntax `doElem json
    | _, _ => throwError s!"Unsupported syntax category for AnnAssign node"

@[pygen "Return"]
def returnSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
    | `doElem, json => do
        let .ok value := json.getObjVal? "value" | throwError
          s!"Return node does not have a 'value' field or it is not a JSON value: {json}"
        match value with
        | .null =>
            `(doElem| return (()))
        | _ =>
            if jsonUsesIOEffect value then
              let valueStx ← inlineIOTerm value
              if shouldParenthesizeReturnValue value then
                `(doElem| return ($valueStx))
              else
                `(doElem| return $valueStx)
            else
              let valueStx ← getCode value `term
              if jsonUsesMonadicEffect value then
                `(doElem| return (← $valueStx:term))
              else
                if shouldParenthesizeReturnValue value then
                  `(doElem| return ($valueStx))
                else
                  `(doElem| return $valueStx)
    | _, _ => throwError s!"Unsupported syntax category for Return node"

end PastaLean

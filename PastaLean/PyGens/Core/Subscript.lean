import PastaLean.PyAPI.Core
import PastaLean.PyAPI.Refinement
import PastaLean.PyGens.Basic
import PastaLean.PyGens.Core.Utils

namespace PastaLean

/-- Check if a JSON node represents a string constant. -/
def isStringConstant (json : Lean.Json) : Bool :=
    let nodeType := json.getObjValAs? (α := Lean.Json) (k := "node_type")
    let value := json.getObjValAs? (α := Lean.Json) (k := "value")
    match nodeType, value with
    | Except.ok "Constant", Except.ok (.str _) => true
    | _, _ => false

open Lean Elab Term Meta
open PastaLean

/-- Statically project the `k`-th element (0-based) out of an `n`-element right-nested product
`(e₀, e₁, …, eₙ₋₁)` = `e₀ × (e₁ × …)`. Descends with `Prod.snd` `k` times to reach the sub-tuple
starting at `k`, then takes `Prod.fst` unless `k` is the last element (which is the bare tail). This
gives the exact per-slot type, so it works for heterogeneous tuples where `pyGetItem` cannot. -/
def tupleProjection (valueCode : TSyntax `term) (k n : Nat) : PygenM (TSyntax `term) := do
    let mut t := valueCode
    for _ in [0:k] do
      t ← `(Prod.snd $t)
    if k + 1 < n then
      t ← `(Prod.fst $t)
    return t

/-- Build the Lean term for `value[slice]` from an *already-lowered* `valueCode`. Factoring this
out of the `@[pygen]` entry point lets IO inlining/hoisting rebuild a subscript over an awaited
container (`foo()[i]` where `foo()` is `IO _`) without re-lowering — and re-awaiting — the base. -/
def subscriptTermFromValue (valueJson sliceJson : Json) (valueCode : TSyntax `term) :
    PygenM (TSyntax `term) := do
    -- The arity of a tuple-typed value, when known: a literal `Tuple` node carries its `elts`, and a
    -- `Name` bound to a tuple is stamped by TypeInfer (`_PastaLean_tuple_arity`, or the legacy
    -- `_PastaLean_pair` for the arity-2 case). A constant index into such a value lowers to a static
    -- `Prod` projection rather than the generic `pyGetItem` notation, which has no `PyGetItem`
    -- instance for a heterogeneous product.
    let tupleArity : Option Nat :=
      match valueJson.getObjValAs? String "node_type" with
      | .ok "Tuple" => (valueJson.getObjValAs? (Array Json) "elts").toOption.map (·.size)
      | _ =>
        match valueJson.getObjValAs? Nat "_PastaLean_tuple_arity" with
        | .ok n => some n
        | _ =>
          match valueJson.getObjValAs? Bool "_PastaLean_pair" with
          | .ok true => some 2
          | _ => none
    let isTuple := tupleArity.isSome
    let isString := isStringConstant valueJson

    -- TypeInfer proved this index in range (`for h : i in range(len(xs))`, `_inbounds_h` on the slice):
    -- index through the proof, so no `Inhabited` default and no unreachable `panic!`. Not under
    -- `--heap`, where the container is a `Ref` the analysis does not model.
    if let some h := (sliceJson.getObjValAs? String "_inbounds_h").toOption then
      if !(← getHeapMode) then
        let sliceCode ← getCode sliceJson `term
        -- `rfl` proves the loop bound IS this container's length: either literally `pyRange (pyLen xs)`,
        -- or `pyRange n` for an `n` the analysis checked is a single `let n := pyLen xs`.
        return ← `($(mkIdent ``pyListGetProof) $valueCode $sliceCode
          ($(mkIdent ``pyRange_len_bound_of_eq) rfl $(mkIdent h.toName)))

    let sliceType := sliceJson.getObjValAs? String "node_type"
    if sliceType == .ok "Slice" then
        -- Lower each slice bound to an `Option Int` term. A missing or `None` bound is `none`;
        -- any other bound expression (constant, variable, arithmetic) is lowered through `getCode`
        -- and wrapped in `some`, so `a[i:j]`, `a[n-1::-1]`, etc. all carry the real bound rather
        -- than being silently dropped to a full slice.
        let boundStx (field : String) : PygenM (TSyntax `term) := do
            match (sliceJson.getObjVal? field).toOption with
            | none => `(none)
            | some j =>
                if j.getObjValAs? String "node_type" == .ok "Constant"
                    && (j.getObjVal? "value").toOption.any (· == Json.null) then
                  `(none)
                else
                  match j with
                  | .null => `(none)
                  | _ => `(some $(← getCode j `term))
        let startStx ← boundStx "lower"
        let stopStx ← boundStx "upper"
        let stepStx ← boundStx "step"
        -- Generic slice dispatch: a `String` slices to `String`, a `List` to `List`; the `step`
        -- bound makes `a[::-1]`/`a[::2]` correct. (A bare string literal uses the String slicer
        -- directly for predictable output.)
        let sliceIdent :=
          if isString then mkIdent `PastaLean.pyStringSliceStep
          else mkIdent `PastaLean.pySlice
        -- Slicing a homogeneous tuple (`(1, 2, 3)[1:]`) flattens it to a `List α` first: a
        -- variable-length slice can't be a fixed-arity Lean product, so a list is the honest result.
        let sliced ← if isTuple && !isString then `(PastaLean.pyIter $valueCode) else pure valueCode
        `($sliceIdent $sliced $startStx $stopStx $stepStx)
    else if sliceType == .ok "Tuple" then
        match sliceJson.getObjValAs? (Array Json) "elts" with
        | .ok elts =>
            if let some key ← dictTupleKeyTerm? sliceJson then
                -- `d[i, j]` on a dict is a single tuple-KEY access `d[(i, j)]` (TypeInfer saw a dict
                -- container), so index once by the tuple key.
                `($valueCode⦋$key⦌)
            else if elts.size == 2 then
                -- numpy-style 2-D indexing on a `List (List _)`: `a[i,j]`, `a[:,j]`, `a[i,:]`.
                let a := elts[0]!
                let b := elts[1]!
                let aSlice := a.getObjValAs? String "node_type" == .ok "Slice"
                let bSlice := b.getObjValAs? String "node_type" == .ok "Slice"
                if aSlice && !bSlice then
                    let jCode ← getCode b `term
                    `(List.map (fun row => row⦋$jCode⦌) $valueCode)
                else if !aSlice && bSlice then
                    `($valueCode⦋$(← getCode a `term)⦌)
                else if !aSlice && !bSlice then
                    `($valueCode⦋$(← getCode a `term)⦌⦋$(← getCode b `term)⦌)
                else
                    pure valueCode
            else
                throwError "Only 2-D tuple subscripts are supported."
        | .error _ => throwError "Tuple subscript is missing its 'elts' field."
    else if isTuple then
        -- A constant index static-projects to the exact slot (works for heterogeneous tuples); a
        -- variable index falls back to `pyGetItem`, which dispatches through the homogeneous
        -- `PyGetItem (α × β) Int α` runtime instance.
        match sliceJson.getObjValAs? String "node_type",
              (sliceJson.getObjVal? "value").toOption.bind (·.getNat?.toOption) with
        | .ok "Constant", some k =>
            match tupleArity with
            | some n => tupleProjection valueCode k n
            | none => tupleProjection valueCode k (k + 2)
        | _, _ =>
            let sliceCode ← getCode sliceJson `term
            `($valueCode⦋$sliceCode⦌)
    else if isString then
        -- Indexing a string literal yields a one-character string (Python has no char type),
        -- matching `pyGetItem`/`PyGetItem String Int String` on string variables.
        let getIdent := mkIdent `PastaLean.pyStringGetItemStr
        let sliceType := sliceJson.getObjValAs? String "node_type"
        match sliceType with
        | .ok "Constant" =>
            let idx := sliceJson.getObjValAs? Int "value"
            match idx with
            | .ok i =>
                let iStx ← intToStx i
                `($getIdent $valueCode $iStx)
            | _ =>
                let sliceCode ← getCode sliceJson `term
                `($getIdent $valueCode $sliceCode)
        | _ =>
            let sliceCode ← getCode sliceJson `term
            `($getIdent $valueCode $sliceCode)
    else
        -- General container indexing `c[i]`, emitted with the readable `c⦋i⦌` notation (which is
        -- definitionally `pyGetItem c i`, so it dispatches through any `PyGetItem` instance).
        let sliceType := sliceJson.getObjValAs? String "node_type"
        match sliceType with
        | .ok "Constant" =>
            let idx := sliceJson.getObjValAs? Int "value"
            match idx with
            | .ok i =>
                let iStx ← intToStx i
                `($valueCode⦋$iStx⦌)
            | _ =>
                let sliceCode ← getCode sliceJson `term
                `($valueCode⦋$sliceCode⦌)
        | .ok "UnaryOp" =>
            let op := sliceJson.getObjValAs? String "op"
            let operand := sliceJson.getObjValAs? Json "operand"
            if op == .ok "neg" then
                match operand with
                | .ok j =>
                    let val := j.getObjVal? "value"
                    match val with
                    | .ok jVal =>
                        match jVal.getNat? with
                        | .ok n =>
                            let iStx ← intToStx (-(n : Int))
                            `($valueCode⦋$iStx⦌)
                        | _ =>
                            let sliceCode ← getCode sliceJson `term
                            let getIdent := mkIdent `getElem!
                            `($getIdent $valueCode $sliceCode)
                    | _ =>
                        let sliceCode ← getCode sliceJson `term
                        `($valueCode⦋$sliceCode⦌)
                | _ =>
                    let sliceCode ← getCode sliceJson `term
                    `($valueCode⦋$sliceCode⦌)
            else
                let sliceCode ← getCode sliceJson `term
                `($valueCode⦋$sliceCode⦌)
        | _ =>
            let sliceCode ← getCode sliceJson `term
            `($valueCode⦋$sliceCode⦌)

@[pygen "Subscript"]
def subscriptSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
  | `term, json => do
    let .ok valueJson := json.getObjValAs? Json "value" | throwError
      s!"Subscript node does not have a 'value' field or it is not a JSON value: {json}"
    let .ok sliceJson := json.getObjValAs? Json "slice" | throwError
      s!"Subscript node does not have a 'slice' field or it is not a JSON value: {json}"
    -- Under `--heap`, a container held by reference is dereferenced before indexing (`a[i]` →
    -- `pyGetItem (← readRef a) i`).
    let valueCode ← match ← heapContainerDeref? valueJson with
      | some deref => pure deref
      | none => getCode valueJson `term
    subscriptTermFromValue valueJson sliceJson valueCode
  | _, _ => throwError s!"Unsupported syntax category for Subscript node"

end PastaLean

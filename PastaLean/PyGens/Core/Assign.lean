import PastaLean.PyGens.Core.Utils
import PastaLean.PyGens.Calls.CallEffects
import PastaLean.PyGens.Calls.CallShared

open Lean Meta Elab Term Qq Std

namespace PastaLean

-- Render a `PyType` to its HEAP Lean type (`--heap`): user objects and mutable containers become
-- `Ref`s (recursively), primitives stay inline, tuples stay inline products (immutable, never heap
-- cells), and un-pinnable container elements box to `PyAny`. This is what makes
-- `Node.next : Option (Ref Node)`, `items : Ref (List Int)`, and a generic `Ref (List PyAny)`.
-- (Lives here, upstream of both FuncDef and ClassDef, so closure cell params can reuse it.)
mutual
/-- The heap Lean type of a Python type. Object/container slots become `Ref`s; a scalar slot that
inference can't pin defaults to `Int` (kept concrete so arithmetic/ordering instances still resolve —
boxing a scalar to `PyAny` here would leave `+ₚ`/`≤` stuck). Container ELEMENTS go through
`heapElemTypeSyntax`, which boxes an un-pinnable element to `PyAny`. -/
partial def heapTypeSyntax (t : TypeInfer.PyType) : PygenM (TSyntax `term) := do
  match t with
  -- In a run-twin, an object type names the `'rn` class (`Counter'rn`), matching the twin's
  -- constructor/fields and its `Storable Val (Ref Counter'rn)`; exact mode leaves the name as-is.
  | .cls n => `(PastaLean.Ref $(mkIdent (← suffixIfUserName n).toName))
  | .list e => `(PastaLean.Ref (List $(← heapElemTypeSyntax e)))
  | .set e  => `(PastaLean.Ref (List $(← heapElemTypeSyntax e)))
  | .dict k v => `(PastaLean.Ref (Std.HashMap $(← heapTypeSyntax k) $(← heapElemTypeSyntax v)))
  | .opt inner => `(Option $(← heapTypeSyntax inner))
  | .tuple es =>
      match es with
      | []        => `(Unit)
      | e :: rest => do
          let mut acc ← heapTypeSyntax e
          for r in rest do
            acc ← `($acc × $(← heapTypeSyntax r))
          pure acc
  | _ => pure ((← pyTypeSyntax? t).getD (mkIdent ``Int))

/-- The Lean type of a container element/value position. An element that holds conflicting types
(`.any`, ⊤ — e.g. an explicit `list[object]`, or a list mixing `int` and `str`) boxes to `PyAny`, the
gradual-typing fallback: element ops (`append`/`[]`/`len`/`for`/print) all have `PyAny` instances and
pushed values auto-box, so a heap container "of any type" is `Ref (List PyAny)`. A merely un-pinned
element (`.unknown`, ⊥ — e.g. a bare `= []` whose items are all one type) keeps the concrete default,
so an all-`int` list stays `Ref (List Int)` and its element arithmetic still resolves. -/
partial def heapElemTypeSyntax (t : TypeInfer.PyType) : PygenM (TSyntax `term) := do
  match t with
  | .any => pure (mkIdent ``PastaLean.PyAny)
  | _ => heapTypeSyntax t
end

/-- Read all Name idents from a tuple assignment target (any arity ≥ 2). -/
def tupleAssignTargetNames? (target : Json) : PygenM (Option (Array (TSyntax `ident))) := do
  unless jsonNodeType? target == some "Tuple" do
    return none
  let .ok elts := target.getObjValAs? (Array Json) "elts" | throwError
    s!"Tuple assignment target does not have an 'elts' field or it is not a JSON value: {target}"
  if elts.size < 2 then
    throwError "Tuple assignment target must have at least two elements."
  let mut idents := #[]
  for elt in elts do
    unless jsonNodeType? elt == some "Name" do
      throwError "Only Name targets are supported in tuple assignment."
    idents := idents.push (← getCode elt `ident)
  return some idents

/-- The elements of a tuple-assignment target (arity ≥ 2), or `none` if it is not a `Tuple`.
Unlike `tupleAssignTargetNames?`, elements may be any target shape — e.g. the `Subscript`s in
`a[i], a[j] = a[j], a[i]`. -/
def tupleTargetElts? (target : Json) : PygenM (Option (Array Json)) := do
  unless jsonNodeType? target == some "Tuple" do
    return none
  let .ok elts := target.getObjValAs? (Array Json) "elts" | throwError
    s!"Tuple assignment target does not have an 'elts' field or it is not a JSON value: {target}"
  if elts.size < 2 then
    throwError "Tuple assignment target must have at least two elements."
  return some elts

/-- Build the accessor term to reach element `idx` of an N-element right-nested pair `pairIdent`.
`buildTuple` produces `(e0, (e1, (e2, e3)))`, so:
  - element 0 → `Prod.fst p`
  - element 1 → `Prod.fst (Prod.snd p)`
  - element N-2 → `Prod.fst (Prod.snd^(N-2) p)`
  - element N-1 → `Prod.snd^(N-1) p` -/
def tupleAccessTerm (pairIdent : TSyntax `ident) (idx n : Nat) : PygenM (TSyntax `term) := do
  let fstIdent := mkIdent ``Prod.fst
  let sndIdent := mkIdent ``Prod.snd
  let mut base : TSyntax `term := mkIdent pairIdent.getId
  for _ in List.range idx do
    base ← `($sndIdent $base)
  if idx == n - 1 then
    pure base
  else
    `($fstIdent $base)

/-- Build the accessor to reach element `idx` of an unpack source.

Python unpacking (`a, b, c = rhs`) iterates the RHS, but our two runtime shapes need different
accessors: a tuple *literal* RHS builds a right-nested `Prod` (so use `Prod.fst`/`Prod.snd`),
while anything else (a `list`, a `map(...)`/`split()` result, a variable) is a `List` (so index
with `pyListGetItem`). `isTuple` selects which. -/
def unpackAccessTerm (isTuple : Bool) (sourceIdent : TSyntax `ident) (idx n : Nat) :
    PygenM (TSyntax `term) := do
  if isTuple then
    tupleAccessTerm sourceIdent idx n
  else
    let getIdent := mkIdent ``PastaLean.pyListGetItem
    let idxStx ← intToStx (Int.ofNat idx)
    `($getIdent $sourceIdent $idxStx)

/-- Pure-term binding of one tuple-target element to `acc`, recursing into nested tuple targets
(`(a, b), c = …`). `isTuple` is the access mode for the *nested* levels: `Prod` for a threaded
call's all-`Prod` return, `List` for a `list[list[...]]`. -/
partial def pureUnpackBinding (isTuple : Bool) (elt : Json) (acc tail : TSyntax `term) :
    PygenM (TSyntax `term) := do
  match jsonNodeType? elt with
  | some "Tuple" | some "List" =>
    let subElts := (elt.getObjValAs? (Array Json) "elts").toOption.getD #[]
    let tmp := mkIdent (← freshName `__unpack_pair)
    let mut body := tail
    for i in (List.range subElts.size).reverse do
      body ← pureUnpackBinding isTuple subElts[i]! (← unpackAccessTerm isTuple tmp i subElts.size) body
    `(let $tmp := $acc
      $body)
  | _ =>
    `(let $(← getCode elt `ident) := $acc
      $tail)

/-- Emit either a fresh `let mut` or a reassignment for one local binding. On the first binding an
inferred type (`ty?`) is ascribed — `let mut x : T := …` — which stops Lean defaulting an
unconstrained element/index to `ℚ`. A reassignment never re-ascribes. -/
def bindOrAssignLocal (nameIdent : TSyntax `ident) (rhs : TSyntax `term)
    (ty? : Option (TSyntax `term) := none) (rebindShadow : Bool := false) : PygenM (TSyntax `doElem) := do
  -- Python may rebind a name to a DIFFERENT type (`for ch in s: ch = ord(ch)`). One `let mut` has a
  -- fixed type, so a fresh `let mut` shadows the plain `let` the loop bound — matching Python, where
  -- code before the rebind saw the old value and code after sees the new. Its type comes from the
  -- RHS, NOT from the `PyAny` stamp: a single binding never has to hold both types.
  if rebindShadow then
    setMutVar nameIdent.getId
    return ← `(doElem| let mut $nameIdent:ident := $rhs)
  if ← hasVar nameIdent.getId then
    `(doElem| $nameIdent:ident := $rhs)
  else
    let stx ← match ty? with
      | some ty => `(doElem| let mut $nameIdent:ident : $ty := $rhs)
      | none => `(doElem| let mut $nameIdent:ident := $rhs)
    addVar nameIdent.getId
    setMutVar nameIdent.getId
    pure stx

/-- Normalize Python-style two-target unpacking through the iterable protocol. -/
def unpack2Term (value : TSyntax `term) : PygenM (TSyntax `term) := do
  let pyUnpack2Ident := mkIdent ``PastaLean.pyUnpack2
  `($pyUnpack2Ident $value)

/-- Recognize a single-level subscript assignment target `name[index]`, returning the
container ident (the `mut` variable to rebuild) and the index term. Returns `none` for
non-subscript targets; throws a clear error for unsupported subscript shapes (nested
subscripts, non-Name containers, slice targets). -/
def subscriptTargetParts? (target : Json) : PygenM (Option (TSyntax `ident × TSyntax `term)) := do
  unless jsonNodeType? target == some "Subscript" do
    return none
  let .ok containerJson := target.getObjValAs? Json "value" | throwError
    s!"Subscript assignment target is missing a 'value' field: {target}"
  let .ok sliceJson := target.getObjValAs? Json "slice" | throwError
    s!"Subscript assignment target is missing a 'slice' field: {target}"
  -- Slice targets (`s[a:b] = ...`) are item-list replacement, handled by `sliceTargetParts?`.
  if jsonNodeType? sliceJson == some "Slice" then
    return none
  unless jsonNodeType? containerJson == some "Name" do
    throwError "Only `name[index] = ...` subscript assignment (single-level, Name container) \
      is supported."
  let containerIdent ← getCode containerJson `ident
  let indexTerm ← getCode sliceJson `term
  return some (containerIdent, indexTerm)

/-- Emit `container := pySetItem container index value` for a subscript item assignment. -/
def subscriptSetDoElem (containerIdent : TSyntax `ident) (indexTerm value : TSyntax `term) :
    PygenM (TSyntax `doElem) := do
  let setItemIdent := mkIdent ``PastaLean.pySetItem
  `(doElem| $containerIdent:ident := $setItemIdent $containerIdent $indexTerm $value)

/-- If `target` is `self.X` (an `Attribute` whose base is the `Name` `self`), return the attribute
name `X`. Used to lower attribute writes inside a class method to a `self` record update. -/
def selfAttrTarget? (target : Json) : Option String :=
  if jsonNodeType? target == some "Attribute" then
    match (target.getObjVal? "value").toOption, (target.getObjValAs? String "attr").toOption with
    | some v, some attr =>
        if jsonNodeType? v == some "Name" && v.getObjValAs? String "id" == .ok "self" then
          some attr
        else none
    | _, _ => none
  else none

/-- Emit `self := { self with X := rhs }` — the value-semantics lowering of `self.X = rhs` inside a
class method body (`self` is the method's `let mut` shadow). -/
def selfRecordUpdateDoElem (attr : String) (rhs : TSyntax `term) : PygenM (TSyntax `doElem) := do
  let selfId := mkIdent `self
  let attrId := mkIdent attr.toName
  -- Under `--heap` in a method body, `self` is a `Ref C`: write the field through it with the
  -- `self ~> attr <~ rhs` pointer notation (`rhs` may itself read fields — those `←`s lift). The
  -- `<~` doElem can't be produced by a quotation with an antiquote LHS, so build the node directly;
  -- the pretty-printed text re-parses and macro-expands to a `writeRef` when the file is compiled.
  if ← getHeapSelfRef then
    let lhs ← `($selfId ~> $attrId:ident)
    return ⟨mkNode ``PastaLean.ptrWrite #[lhs.raw, mkAtom "<~", rhs.raw]⟩
  let fields := #[← `(Lean.Parser.Term.structInstField| $attrId:ident := $rhs)]
  `(doElem| $selfId:ident := { $selfId:term with $fields:structInstField,* })

/-- `<recv>.attr = rhs` (or the base of `<recv>.attr op= rhs`) when `recv` is a heap OBJECT reference —
`self` as a `Ref C` param (`heapSelfRef`) or a variable/param registered to hold a heap object of a
known class (`heapVarClassOf?`). Emits the `recv ~> attr <~ rhs` pointer-write (built directly like
`selfRecordUpdateDoElem`, since the `<~` LHS can't be an antiquote). Returns `none` when not a heap
object ref, so callers fall back to the value-semantics record update. -/
def heapAttrWriteTargetDoElem? (target : Json) (rhs : TSyntax `term) :
    PygenM (Option (TSyntax `doElem)) := do
  unless ← getHeapMode do return none
  unless jsonNodeType? target == some "Attribute" do return none
  let .ok recv := target.getObjVal? "value" | return none
  let .ok attr := target.getObjValAs? String "attr" | return none
  unless jsonNodeType? recv == some "Name" do return none
  let .ok recvId := recv.getObjValAs? String "id" | return none
  let isHeapObj ←
    if recvId == "self" && (← getHeapSelfRef) then pure true
    else pure (← heapVarClassOf? recvId.toName).isSome
  unless isHeapObj do return none
  let lhs ← `($(mkIdent recvId.toName) ~> $(mkIdent attr.toName):ident)
  return some ⟨mkNode ``PastaLean.ptrWrite #[lhs.raw, mkAtom "<~", rhs.raw]⟩

/-- The class name of a value expression that produces a heap object, if statically known: a
constructor call (`_class_ctor` stamp) or a variable already known to hold one (`q = p`). -/
def heapClassOfValue? (value : Json) : PygenM (Option String) := do
  match (value.getObjValAs? String "_class_ctor").toOption with
  | some c => return some c
  | none =>
    if jsonNodeType? value == some "Name" then
      match value.getObjValAs? String "id" with
      | .ok vid => heapVarClassOf? vid.toName
      | _ => return none
    else return none

/-- `<recv>.attr = rhs` under value semantics, for ANY receiver (`node.children[i]=v` on a local,
`obj.field=v`): rebuild the receiver record `{recv with attr := rhs}` and store it back — a `Name`
receiver is reassigned, a nested attribute recurses. (Emitting `let mut obj.field := …` is invalid
Lean; this is the general form of the `self` record update.) -/
partial def attrRecordUpdateDoElem (recvJson : Json) (attr : String) (rhs : TSyntax `term)
    (recvIsOpt : Bool := false) : PygenM (TSyntax `doElem) := do
  let recvTerm ← getCode recvJson `term
  let attrId := mkIdent attr.toName
  -- An `Option`-typed receiver (`root.left = v` on a tree node) must be unwrapped for the record
  -- update and re-wrapped, since `{ opt with f := v }` is not a valid update.
  let updated ← if recvIsOpt then
      `(some { ($recvTerm).getD default with $attrId:ident := $rhs })
    else `({ $recvTerm with $attrId:ident := $rhs })
  match jsonNodeType? recvJson with
  | some "Name" =>
      let recvIdent ← getCode recvJson `ident
      `(doElem| $recvIdent:ident := $updated)
  | some "Attribute" =>
      let .ok inner := recvJson.getObjVal? "value" | throwError s!"Attribute missing 'value': {recvJson}"
      let .ok innerAttr := recvJson.getObjValAs? String "attr" | throwError s!"Attribute missing 'attr': {recvJson}"
      attrRecordUpdateDoElem inner innerAttr updated
        (recvJson.getObjValAs? Bool "_unwrap_opt" == .ok true)
  | some "Subscript" =>
      -- `arr[i].f = v` / `self.tr[u].l = v`: rebuild the element `{arr[i] with f := v}` and store it
      -- back into `arr[i]` via `pySetItem`, then reassign the container (a `Name`, or an `Attribute`
      -- like `self.tr` via the same record-update recursion).
      let .ok containerJson := recvJson.getObjVal? "value" | throwError s!"Subscript missing 'value': {recvJson}"
      let .ok sliceJson := recvJson.getObjVal? "slice" | throwError s!"Subscript missing 'slice': {recvJson}"
      if jsonNodeType? sliceJson == some "Slice" then
        throwError "attribute assignment on a sliced element is not supported."
      let containerCode ← getCode containerJson `term
      let indexTerm ← getCode sliceJson `term
      let newContainer ← `($(mkIdent ``PastaLean.pySetItem) $containerCode $indexTerm $updated)
      match jsonNodeType? containerJson with
      | some "Name" =>
          let containerIdent ← getCode containerJson `ident
          `(doElem| $containerIdent:ident := $newContainer)
      | some "Attribute" =>
          let .ok inner := containerJson.getObjVal? "value" | throwError s!"Attribute missing 'value': {containerJson}"
          let .ok innerAttr := containerJson.getObjValAs? String "attr" | throwError s!"Attribute missing 'attr': {containerJson}"
          attrRecordUpdateDoElem inner innerAttr newContainer
            (containerJson.getObjValAs? Bool "_unwrap_opt" == .ok true)
      | _ => throwError "attribute assignment `arr[i].f = v` needs a variable or attribute base container."
  | _ => throwError "attribute assignment `x.f = v` needs a variable or attribute receiver."

/-- Unwrap a nested subscript `root[i₁]…[iₖ]` into `(root, [slice₁, …, sliceₖ])` (outermost index
first). `none` if any level is a `Slice` (handled elsewhere) or the root isn't a `Name`/`Attribute`. -/
partial def subscriptChain? (target : Json) : Option (Json × Array Json) :=
  let rec go (node : Json) (acc : Array Json) : Option (Json × Array Json) :=
    match jsonNodeType? node with
    | some "Subscript" => do
        let c ← (node.getObjVal? "value").toOption
        let s ← (node.getObjVal? "slice").toOption
        guard (jsonNodeType? s != some "Slice")
        go c (acc.push s)
    | _ => some (node, acc)
  match go target #[] with
  | some (root, slicesInner) =>
      if slicesInner.isEmpty then none else some (root, slicesInner.reverse)
  | none => none

/-- Build the RHS of a nested subscript assignment `base[i₁]…[iₖ] = v`. The innermost level is a
`pySetItem`; every OUTER level is a `pyModifyItem base iₘ (fun row => …)` so an `Array` slot updates in
place (O(1)) instead of copying the whole row (the `pyGetItem`-then-`pySetItem` form is O(n)). -/
partial def buildSubscriptSetRhs (base : TSyntax `term) (idxs : List (TSyntax `term))
    (value : TSyntax `term) : PygenM (TSyntax `term) := do
  match idxs with
  | [] => pure value
  | [last] => `($(mkIdent ``PastaLean.pySetItem) $base $last $value)
  | i :: rest =>
      let row := mkIdent (← freshName `__row)
      let inner ← buildSubscriptSetRhs row rest value
      `($(mkIdent ``PastaLean.pyModifyItem) $base $i (fun $row => $inner))

partial def nestedSubscriptSetDoElem? (target : Json) (value : TSyntax `term) :
    PygenM (Option (TSyntax `doElem)) := do
  -- Under `--heap`, `a[i] = v` on a container held by reference mutates it in place through the ref.
  -- (Heap mode handles only the single-level subscript case; the multi-level chain below is the
  -- default value-semantics path.)
  if (← getHeapMode) && jsonNodeType? target == some "Subscript" then
    if let some containerJson := (target.getObjVal? "value").toOption then
      if let some sliceJson := (target.getObjVal? "slice").toOption then
        if jsonNodeType? sliceJson != some "Slice" then
          if let some refCode ← heapContainerRef? containerJson then
            let indexTerm ← getCode sliceJson `term
            let lVar := mkIdent `__hc_l
            let newVal ← `($(mkIdent ``PastaLean.pySetItem) $lVar $indexTerm $value)
            -- `a[i] = Node()` sets an awaited value (`pySetItem l i (← Node.new)`); the await can't sit
            -- in `modifyRefM`'s `fun l => …` lambda, so read-then-write to keep it in the enclosing `do`.
            if syntaxHasLift newVal then
              return some (← `(doElem| do
                let $lVar ← PastaLean.readRefM $refCode
                PastaLean.writeRefM $refCode $newVal))
            return some (← `(doElem| PastaLean.modifyRefM $refCode (fun $lVar => $newVal)))
  let some (root, slices) := subscriptChain? target | return none
  -- `d[i, j] = v` on a dict is a single tuple-KEY write; otherwise each level is a plain index.
  -- A level into a boxed `PyAny` container (`_box_index`) boxes its index, and the last one the value.
  let boxed := fun (s : Json) => s.getObjValAs? Bool "_box_index" == .ok true
  let idxTerms ← slices.mapM fun s => do
    let t := (← dictTupleKeyTerm? s).getD (← getCode s `term)
    if boxed s then `(($t : PastaLean.PyAny)) else pure t
  let value ← if slices.back?.any boxed then `(($value : PastaLean.PyAny)) else pure value
  match jsonNodeType? root with
  | some "Name" =>
      let rootIdent ← getCode root `ident
      -- Nested `g[i][j] = …` lowers to `pyModifyItem g i (fun row => …)`. Hoist the value into a prior
      -- `let` so a value that reads `g` (`f[i][j] = f[i-1][j] or …`) doesn't keep a second reference to
      -- `g` alive inside the modify closure — that would force an O(n) row copy instead of in-place.
      if idxTerms.size ≥ 2 then
        let vIdent := mkIdent (← freshName `__setval)
        let bindV ← `(doElem| let $vIdent:ident := $value)
        let rhs ← buildSubscriptSetRhs rootIdent idxTerms.toList vIdent
        let assign ← `(doElem| $rootIdent:ident := $rhs)
        return some ⟨mkNullNode #[bindV.raw, assign.raw]⟩
      let rhs ← buildSubscriptSetRhs rootIdent idxTerms.toList value
      return some (← `(doElem| $rootIdent:ident := $rhs))
  | some "Attribute" =>
      -- `recv.c[i]… = v` rebuilds the field: `recv := { recv with c := … }` (self or any local, e.g.
      -- a Trie walk-node `node.children[i] = Trie()`).
      let .ok recv := root.getObjVal? "value" | throwError
        s!"Attribute container is missing 'value': {root}"
      let .ok attr := root.getObjValAs? String "attr" | throwError
        s!"Attribute container is missing 'attr': {root}"
      let rootTerm ← getCode root `term
      let rhs ← buildSubscriptSetRhs rootTerm idxTerms.toList value
      return some (← attrRecordUpdateDoElem recv attr rhs
        (root.getObjValAs? Bool "_unwrap_opt" == .ok true))
  | _ =>
      throwError "Subscript assignment requires the base container to be a variable \
        (`a[i]…[k] = v`); got an unsupported container expression."

/-- Assign one element of a tuple target from `acc`, which reads it out of the already-evaluated
RHS temp. `Subscript` elements rebuild their container, so the swap `a[i], a[j] = a[j], a[i]`
works: the temp is evaluated before any write-back. -/
partial def tupleElementAssignDoElem (isTuple : Bool) (elt : Json) (acc : TSyntax `term) :
    PygenM (TSyntax `doElem) := do
  match ← nestedSubscriptSetDoElem? elt acc with
  | some setStx => pure setStx
  | none =>
    match jsonNodeType? elt with
    -- Ascribe the binder to the element's inferred type (`_ty`, stamped by TypeInfer) so a slot
    -- seeded by a polymorphic sentinel (`ans, mi = (0, inf)` → `mi : Int`, not the `ℚ` default) pins.
    | some "Name" =>
      -- A node mut-cursor target (`Option C`, from `tl, tr = (l, r)` then `tl = tl.next`) unpacked
      -- from a bare-`C` tuple element: coerce the projection (`↑`) so it elaborates at `C` then lifts.
      -- Without it the `Option C` ascription back-unifies the polymorphic `Prod.fst`, forcing the whole
      -- tuple to `Option C × …` which the `C × C` RHS can't match. `↑` is a no-op if the element is
      -- already `Option C`.
      -- Also coerce a numeric-WIDENED element (`_ty = float`/ℚ from `left,right = (0, 1e8)` then
      -- `left = mid : ℚ`): the same back-unification would otherwise force the tuple to `ℚ × …`. The
      -- int-sentinel case (`ans, mi = (0, inf)` → `mi : Int`) keeps the pinning ascription (not float).
      let coerceElem := match (jsonFieldOption elt "_ty").map TypeInfer.ofAnnotation with
        | some (.opt (.cls _)) | some (.float) => true | _ => false
      let acc ← if coerceElem then `(↑$acc) else pure acc
      bindOrAssignLocal (← getCode elt `ident) acc (ty? := ← stampedTypeSyntax? elt)
    | some "Attribute" =>
      -- `a.val, b.val = b.val, a.val` (a value swap on tree nodes): rebuild each receiver record.
      let .ok recv := elt.getObjVal? "value" | throwError s!"Attribute target missing 'value': {elt}"
      let .ok attr := elt.getObjValAs? String "attr" | throwError s!"Attribute target missing 'attr': {elt}"
      attrRecordUpdateDoElem recv attr acc (elt.getObjValAs? Bool "_unwrap_opt" == .ok true)
    | some "Tuple" | some "List" =>
      let subElts := (elt.getObjValAs? (Array Json) "elts").toOption.getD #[]
      let tmp := mkIdent (← freshName `__unpack_nested)
      let mut binds := #[← `(doElem| let $tmp:ident := $acc)]
      for i in [0:subElts.size] do
        binds := binds.push (← tupleElementAssignDoElem isTuple subElts[i]! (← unpackAccessTerm isTuple tmp i subElts.size))
      pure ⟨mkNullNode (binds.map TSyntax.raw)⟩
    | _ =>
      throwError s!"Unsupported tuple-assignment target element (only `Name`, attribute `a.f`, \
        nested tuple, and subscript `a[i]` targets are supported): {elt}"

/-- Index of a `Starred` element in a tuple target (`a, *b = …`), if any. -/
def starredTargetIndex? (elts : Array Json) : Option Nat :=
  (List.range elts.size).find? (fun i => jsonNodeType? elts[i]! == some "Starred")

/-- Lower a starred tuple-assignment `a, *b, c = src` over a list `src`. The starred element (at
`k`) collects the middle slice `src[k : -(after)]`; elements before it index from the front, and
elements after it index from the end (negative indices), so `c` always reads the last element
regardless of how many `src` holds. `src` must be list-accessed (a `*` target collects a list). -/
def starredUnpackDoElems (elts : Array Json) (k : Nat) (srcIdent : TSyntax `ident) :
    PygenM (Array (TSyntax `doElem)) := do
  let n := elts.size
  let after := n - 1 - k
  let getItem := mkIdent ``PastaLean.pyListGetItem
  let mut binds : Array (TSyntax `doElem) := #[]
  for i in List.range n do
    let elt := elts[i]!
    let bind ←
      if i < k then
        tupleElementAssignDoElem false elt (← `($getItem $srcIdent $(← intToStx (Int.ofNat i))))
      else if i == k then
        let .ok inner := elt.getObjVal? "value" | throwError
          s!"Starred assignment target is missing a 'value' field: {elt}"
        let startStx ← `(some $(← intToStx (Int.ofNat k)))
        let stopStx ← if after == 0 then `((none : Option Int))
                      else `(some $(← intToStx (-(Int.ofNat after))))
        tupleElementAssignDoElem false inner (← `($(mkIdent ``PastaLean.pyListSlice) $srcIdent $startStx $stopStx))
      else
        tupleElementAssignDoElem false elt (← `($getItem $srcIdent $(← intToStx (-(Int.ofNat (n - i))))))
    binds := binds.push bind
  pure binds

/-- Lower an optional slice bound expression to a `some _`/`none` `Option Int` term. -/
def sliceBoundOptTerm (boundJson? : Option Json) : PygenM (TSyntax `term) := do
  match boundJson? with
  | none => `(none)
  | some boundJson => `(some $(← getCode boundJson `term))

/-- Recognize a slice assignment target `name[lower:upper]`, returning the container ident
and the two optional bound terms. Returns `none` for non-slice subscript targets. A step
(`name[a:b:c]`) is rejected. -/
def sliceTargetParts? (target : Json) :
    PygenM (Option (TSyntax `ident × TSyntax `term × TSyntax `term × Option (TSyntax `term))) := do
  unless jsonNodeType? target == some "Subscript" do
    return none
  let .ok sliceJson := target.getObjValAs? Json "slice" | throwError
    s!"Subscript assignment target is missing a 'slice' field: {target}"
  unless jsonNodeType? sliceJson == some "Slice" do
    return none
  let .ok containerJson := target.getObjValAs? Json "value" | throwError
    s!"Slice assignment target is missing a 'value' field: {target}"
  unless jsonNodeType? containerJson == some "Name" do
    throwError "Only `name[a:b] = ...` slice assignment (Name container) is supported."
  let containerIdent ← getCode containerJson `ident
  let lowerTerm ← sliceBoundOptTerm (jsonFieldOption sliceJson "lower")
  let upperTerm ← sliceBoundOptTerm (jsonFieldOption sliceJson "upper")
  -- An extended slice `s[a:b:c] = repl` writes every `c`-th element via `pySliceSetStep`.
  let stepTerm? ← match jsonFieldOption sliceJson "step" with
    | some s => if s.isNull then pure none else pure (some (← getCode s `term))
    | none => pure none
  return some (containerIdent, lowerTerm, upperTerm, stepTerm?)

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

/-- The library module owning the object this expression constructs (`hashlib.md5()` → `"hashlib"`),
or the module already recorded for a `Name` being copied. Lets `m = hashlib.md5()` then
`n = m` both tag their target, so the method dispatch follows the value. -/
def jsonLibObjectModule? (value : Json) : PygenM (Option String) := do
  match jsonNodeType? value with
  | some "Call" =>
      let some func := (value.getObjVal? "func").toOption | return none
      let .ok m := func.getObjValAs? String "library_module" | return none
      let .ok member := func.getObjValAs? String "library_member" | return none
      return if Libraries.libraryObjectConstructor? m member then some m else none
  | some "Name" =>
      let .ok id := value.getObjValAs? String "id" | return none
      libObjVarModule? id.toName
  | _ => return none

/-- `match v with | (x₀, …, xₙ) => (box x₀, …)`, boxing the components typed `Any`. -/
partial def boxTupleParts (v : TSyntax `term) (ts : List TypeInfer.PyType) : PygenM (TSyntax `term) := do
  if ts.length < 2 then return v
  let xs ← ts.mapM fun _ => do return mkIdent (← freshName `p'_part)
  let parts ← (xs.zip ts).mapM fun (x, t) => match t with
    | .any => `(($x : PastaLean.PyAny))
    | .tuple us => boxTupleParts x us
    | _ => pure x
  let pat ← xs.dropLast.foldrM (fun x acc => `(($x, $acc))) (xs.getLast! : TSyntax `term)
  let body ← parts.dropLast.foldrM (fun p acc => `(($p, $acc))) parts.getLast!
  `(match $v:term with | $pat => $body)

/-- Lower `value` against its declared type `ty`, boxing the parts typed `Any` (a tuple literal is
matched componentwise), so `return None, i` in a `-> tuple[Any, int]` function yields `(PyAny.none, i)`. -/
partial def lowerAgainstType (lower : Json → PygenM (TSyntax `term)) (value : Json) :
    TypeInfer.PyType → PygenM (TSyntax `term)
  | .any => do
      match jsonNodeType? value with
      -- A literal in an `Any` slot is a boxed, insertion-ordered container, not a `Std.HashMap`/`List`.
      | some "Dict" =>
          let ks := (value.getObjValAs? (Array Json) "keys").toOption.getD #[]
          let vs := (value.getObjValAs? (Array Json) "values").toOption.getD #[]
          if ks.any (·.isNull) then return ← lower value
          let kvs ← (ks.zip vs).mapM fun (k, v) => do
            `(($(← lowerAgainstType lower k .any), $(← lowerAgainstType lower v .any)))
          `(PastaLean.PyAny.dict [$kvs,*])
      | some "List" =>
          let es := (value.getObjValAs? (Array Json) "elts").toOption.getD #[]
          let xs ← es.mapM fun e => lowerAgainstType lower e .any
          `(PastaLean.PyAny.list [$xs,*])
      | _ =>
          let v ← withBoxReturnContext true (lower value)
          `(($v : PastaLean.PyAny))
  | .tuple ts => do
      let elts := (value.getObjValAs? (Array Json) "elts").toOption.getD #[]
      if jsonNodeType? value != some "Tuple" || elts.size != ts.length || elts.size < 2
          || !ts.any TypeInfer.PyType.boxesAny then
        if ts.any TypeInfer.PyType.boxesAny then
          -- A non-literal tuple (`return scanstring(s, i)`) is destructured and its `Any` parts boxed.
          return ← boxTupleParts (← lower value) ts
        return ← lower value
      let parts ← (elts.toList.zip ts).mapM fun (e, t) => lowerAgainstType lower e t
      let init := parts.getLast!
      parts.dropLast.foldrM (fun p acc => `(($p, $acc))) init
  | .list .any => do
      if jsonNodeType? value != some "List" then return ← lower value
      let es := (value.getObjValAs? (Array Json) "elts").toOption.getD #[]
      let xs ← es.mapM fun e => lowerAgainstType lower e .any
      `(([$xs,*] : List PastaLean.PyAny))
  | _ => lower value

@[pygen "Assign"]
def assignSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
    | `command, json => withRealIfMarked json do
        let .ok target := json.getObjVal? "target" | throwError
          s!"Assign node does not have a 'target' field or it is not a JSON value: {json}"
        let .ok value := json.getObjVal? "value" | throwError
          s!"Assign node does not have a 'value' field or it is not a JSON value: {json}"
        match ← tupleAssignTargetNames? target with
        | some idents => do
            let n := idents.size
            let valueStx ← getCode value `term
            let unpackTmpIdent := mkIdent (Name.mkSimple s!"p'_unpack_{idents.toList.map (·.getId.toString) |> String.intercalate "_"}")
            -- The unpack temporary is always private (an implementation detail).
            let cmd0 ← makeCommandPrivate (← `(command| def $unpackTmpIdent := $valueStx))
            -- A literal `Tuple` RHS builds a `Prod` (use `Prod.fst`/`Prod.snd`); so does a
            -- function call returning a `tuple[...]` (the Python pre-pass only leaves such
            -- tuple-returning calls as native unpacking — list-returning RHSs are pre-split
            -- into subscripts and never reach here, so a `Call` here means a `Prod` result).
            -- `_list_unpack` (stamped when the RHS is list-typed, e.g. `np.shape(x)` returns a list)
            -- forces list-index access even for a `Call` RHS that would otherwise be read as a `Prod`.
            -- Unpack shape is decided by the INFERRED RHS type (authoritative): `_list_unpack` (RHS a
            -- `list` — `sorted`/`map`/a `list[...]` value) → index access; `_tuple_unpack` (RHS a
            -- `tuple[...]`) → `Prod`. The syntactic checks are ONLY the fallback when inference stamped
            -- neither (an inference gap, or best-effort inference disabled): a literal `Tuple` is
            -- exactly a `Prod`; a residual `Call` defaults to `Prod` (an un-inferred call is usually a
            -- user function returning a tuple — a list-returning builtin carries a return-shape
            -- `Behaviour` so it is stamped `_list_unpack` instead). To fix a mis-shaped case, extend
            -- inference, not this fallback.
            let isTuple :=
              if target.getObjValAs? Bool "_list_unpack" == .ok true then false
              else if target.getObjValAs? Bool "_tuple_unpack" == .ok true then true
              else jsonNodeType? value == some "Tuple" || jsonNodeType? value == some "Call"
            let mut cmds : Array (TSyntax `command) := #[cmd0]
            for i in List.range n do
              let acc ← unpackAccessTerm isTuple unpackTmpIdent i n
              let cmd ← applyPrivacy idents[i]!.getId.toString (← `(command| def $(idents[i]!) := $acc))
              cmds := cmds.push cmd
            pure ⟨mkNullNode (cmds.map TSyntax.raw)⟩
        | none => do
            if jsonNodeType? target == some "Subscript" then
              throwError "Top-level subscript assignment (`s[i] = ...`) is not supported; \
                it mutates a global, which has no top-level form. Move it into a function \
                or an `if __name__ == \"__main__\"` block."
            let nameIdent ← getCode target `ident
            let valueStx ← getCode value `term
            -- `inf = float('inf')` must stay polymorphic in its numeric type: a monomorphic `def`
            -- would pin it to `ℚ` and then `-inf` inside an `int`-returning DP would not typecheck.
            if (← nonFiniteFloatTerm? ((value.getObjVal? "func").toOption.getD Json.null)
                  ((value.getObjValAs? (Array Json) "args").toOption.getD #[])).isSome then
              let α := mkIdent `α
              return ← applyPrivacy nameIdent.getId.toString
                (← `(def $nameIdent {$α : Type} [$(mkIdent ``PastaLean.PyNonFinite) $α] : $α := $valueStx))
            applyPrivacy nameIdent.getId.toString (← `(def $nameIdent := $valueStx))
    | `doElem, json => withRealIfMarked json do
        let .ok target := json.getObjVal? "target" | throwError
          s!"Assign node does not have a 'target' field or it is not a JSON value: {json}"
        let .ok value := json.getObjVal? "value" | throwError
          s!"Assign node does not have a 'value' field or it is not a JSON value: {json}"
        match ← tupleTargetElts? target with
        | some elts => do
            let n := elts.size
            let nestedIsTuple := target.getObjValAs? Bool "_thread_unpack" == .ok true
            -- RHS both yields a value (a tuple) and mutates its receiver (`d, node = heappop(h)`):
            -- bind the value first (reads the original receiver), apply the mutation, then unpack.
            if let some (valueTerm, update) ← mutatingCallRhsLowering? value then
              let valueTmpIdent := mkIdent (← freshName `__unpack_value)
              let bindValueTmp ← `(doElem| let $valueTmpIdent:ident := $valueTerm)
              -- The popped value may be a tuple (`d, node = heappop(h)`) OR a list element
              -- (`_, i, j = heappop(q)` on a list-of-lists) — a `_list_unpack` stamp forces list access;
              -- otherwise default to a `Prod` (the popped element is usually a tuple).
              let isTuple := target.getObjValAs? Bool "_list_unpack" != .ok true
              let mut binds : Array (TSyntax `doElem) := #[bindValueTmp, update]
              for i in List.range n do
                let acc ← unpackAccessTerm isTuple valueTmpIdent i n
                binds := binds.push (← tupleElementAssignDoElem nestedIsTuple elts[i]! acc)
              return ⟨mkNullNode (binds.map TSyntax.raw)⟩
            let valueStx ← getCode value `term
            let valueTmpIdent := mkIdent (← freshName `__unpack_value)
            let unpackTmpIdent := mkIdent (← freshName `__unpack_pair)
            let bindValueTmp ←
              if jsonUsesIOEffect value || jsonUsesMonadicEffect value then
                `(doElem| let $valueTmpIdent:ident ← $valueStx:term)
              else
                `(doElem| let $valueTmpIdent:ident := $valueStx)
            let bindUnpackTmp ← `(doElem| let $unpackTmpIdent:ident := $valueTmpIdent)
            -- `a, *b, c = src`: the `*` target collects a list slice, so `src` is list-accessed
            -- (never a `Prod`), and elements after the star index from the end.
            if let some k := starredTargetIndex? elts then
              let starBinds ← starredUnpackDoElems elts k unpackTmpIdent
              return ⟨mkNullNode ((#[bindValueTmp, bindUnpackTmp] ++ starBinds).map TSyntax.raw)⟩
            -- A literal `Tuple` RHS builds a `Prod` (use `Prod.fst`/`Prod.snd`); so does a
            -- function call returning a `tuple[...]` (the Python pre-pass only leaves such
            -- tuple-returning calls as native unpacking — list-returning RHSs are pre-split
            -- into subscripts and never reach here, so a `Call` here means a `Prod` result).
            -- `_list_unpack` (stamped when the RHS is list-typed, e.g. `np.shape(x)` returns a list)
            -- forces list-index access even for a `Call` RHS that would otherwise be read as a `Prod`.
            -- Unpack shape is decided by the INFERRED RHS type (authoritative): `_list_unpack` (RHS a
            -- `list` — `sorted`/`map`/a `list[...]` value) → index access; `_tuple_unpack` (RHS a
            -- `tuple[...]`) → `Prod`. The syntactic checks are ONLY the fallback when inference stamped
            -- neither (an inference gap, or best-effort inference disabled): a literal `Tuple` is
            -- exactly a `Prod`; a residual `Call` defaults to `Prod` (an un-inferred call is usually a
            -- user function returning a tuple — a list-returning builtin carries a return-shape
            -- `Behaviour` so it is stamped `_list_unpack` instead). To fix a mis-shaped case, extend
            -- inference, not this fallback.
            let isTuple :=
              if target.getObjValAs? Bool "_list_unpack" == .ok true then false
              else if target.getObjValAs? Bool "_tuple_unpack" == .ok true then true
              else jsonNodeType? value == some "Tuple" || jsonNodeType? value == some "Call"
            -- Under `--heap`, a tuple-unpack of a function returning a tuple-of-containers binds each
            -- container element to its object-ref (`Ref (List …)`); TypeInfer marks which slots are
            -- containers, so register those `Name` targets — later `len`/subscript/iterate deref them,
            -- exactly as a directly-bound container does (§ single-target path below).
            let containerMask? : Option (Array Bool) :=
              (target.getObjValAs? (Array Bool) "_unpack_container_mask").toOption
            let mut binds : Array (TSyntax `doElem) := #[bindValueTmp, bindUnpackTmp]
            -- A threaded combined-assign `(userTarget, ...threadedNames) = helper(...)` (ClosureConvert)
            -- puts the user target at index 0 and the threaded-state restores after it. When the user
            -- target is `p[x]` on a threaded container `p`, the restore `p := snd` must land BEFORE the
            -- subscript write `p[x] := fst` — else it clobbers the compression (`p[x]=find(p[x])` in a
            -- union-find `find`). Both read the already-bound tmp, so restoring first is safe. Emit the
            -- threaded restores (indices ≥ 1) ahead of the user target (index 0).
            let order : List Nat :=
              if target.getObjValAs? Bool "_thread_unpack" == .ok true && n ≥ 2
              then (List.range n).drop 1 ++ [0] else List.range n
            for i in order do
              let acc ← unpackAccessTerm isTuple unpackTmpIdent i n
              let mut elt := elts[i]!
              if ← getHeapMode then
                if (containerMask?.bind (·[i]?)).getD false && jsonNodeType? elt == some "Name" then
                  registerHeapVarContainer (← getCode elt `ident).getId
                  -- The slot binds a `Ref (List …)`, not the plain container the `_ty` stamp records;
                  -- drop the ascription so Lean infers the ref type from the `Prod.fst`/`.snd` projection.
                  elt := elt.setObjVal! "_ty" Json.null
              binds := binds.push (← tupleElementAssignDoElem nestedIsTuple elt acc)
            -- Return the bindings as siblings (a flattened null-node), NOT wrapped in a
            -- nested `do` — wrapping would scope the unpacked names away from following
            -- statements. Consumers flatten via `appendDoElems`.
            pure ⟨mkNullNode (binds.map TSyntax.raw)⟩
        | none => do
            -- Some RHS calls both mutate their receiver and yield a value (e.g. `x.pop()`), which a
            -- pure term cannot express. The Calls layer lowers these to a value term plus a
            -- container-update statement, both reading the original container; assignment binds the
            -- target to the value first, then applies the update.
            if jsonNodeType? target == some "Name" then
              if let some (valueTerm, update) ← mutatingCallRhsLowering? value then
                let bindTarget ← bindOrAssignLocal (← getCode target `ident) valueTerm
                return ⟨mkNullNode #[bindTarget.raw, update.raw]⟩
            -- `mat[i][j] = g[k].pop()`: the RHS both mutates and yields, and the target is a subscript.
            -- Hoist the value to a temp, run the receiver update, then rebuild the target container.
            if jsonNodeType? target == some "Subscript" then
              if let some (valueTerm, update) ← mutatingCallRhsLowering? value then
                let tmpIdent := mkIdent (← freshRenameName `_popval)
                let bindTmp ← `(doElem| let $tmpIdent:ident := $valueTerm)
                if let some setStx ← nestedSubscriptSetDoElem? target tmpIdent then
                  return ⟨mkNullNode #[bindTmp.raw, update.raw, setStx.raw]⟩
            let lowerRhs (value : Json) : PygenM (TSyntax `term) := do
              -- `x = a or b` binds the deciding *value*, not a `Bool` (`x = s or '0'` → the string).
              if jsonNodeType? value == some "BoolOp" then boolOpValueTerm value
              else if jsonUsesIOEffect value || jsonNestedMonadicEffect value then
                inlineEffectfulTerm value
              else
                let valueStx ← getCode value `term
                if jsonUsesMonadicEffect value then
                  `((← $valueStx))
                else
                  pure valueStx
            let annTy := (((jsonFieldOption json "annotation").orElse fun _ => jsonFieldOption json "_decl_ty").map
              (TypeInfer.ofAnnotation · (anyDynamic := true))).getD .unknown
            let rhs ← if TypeInfer.PyType.boxesAny annTy then lowerAgainstType lowerRhs value annTy else lowerRhs value
            -- `node = node.children[idx]`: TypeInfer marked the `Option[Node]` value `_narrow` (the
            -- cursor var is a bare node, and the value is guarded non-`None`). Unwrap it (`.get!`).
            let rhs ← if value.getObjValAs? Bool "_narrow" == .ok true then `(($rhs).get!) else pure rhs
            -- Ascribe to the value's inferred type when the inference pass stamped one (a `c[i] = v`
            -- into a float container: put an `Int` value into the container's `ℚ`/`Float` element).
            let rhs ← match ← stampedTypeSyntax? value with
              | some tyStx =>
                  -- A bare int literal must be re-emitted as an `OfNat` in the target type (`(0 : Float)`);
                  -- an ascribed `((0 : Int) : Float)` fails — there is no `Int → Float` coercion.
                  match jsonNodeType? value, value.getObjValAs? Int "value" with
                  | some "Constant", .ok i =>
                      let n := Syntax.mkNumLit (toString i.natAbs)
                      let lit : TSyntax `term ← if i < 0 then `(- $n:num) else pure ⟨n⟩
                      `(($lit : $tyStx))
                  | _, _ => `(($rhs : $tyStx))
              | none => pure rhs
            -- `self.X = v` inside a class method (where `self` is the `let mut` shadow) rebuilds
            -- `self` via record update. The `hasVar self` guard keeps top-level `obj.x = v`
            -- (no mutable `self` in scope) on its normal path.
            if let some attr := selfAttrTarget? target then
              -- Value mode: `self` is the `let mut` shadow (`hasVar`). Heap mode: `self` is a `Ref C`
              -- parameter (not a var), so also fire when `heapSelfRef` is set → `writeRef` update.
              if (← hasVar `self) || (← getHeapSelfRef) then
                return ← selfRecordUpdateDoElem attr rhs
            -- `obj.field = v` for a non-`self` receiver (a local record/node): record-update + reassign,
            -- rather than the invalid `let mut obj.field := v`.
            if jsonNodeType? target == some "Attribute" then
              -- A heap object-ref receiver (`c.n = v` where `c : Ref C`) writes through the pointer;
              -- a plain local record does the value-semantics rebuild-and-reassign.
              if let some w ← heapAttrWriteTargetDoElem? target rhs then return w
              let .ok recv := target.getObjVal? "value" | throwError s!"Attribute missing 'value': {target}"
              let .ok attr := target.getObjValAs? String "attr" | throwError s!"Attribute missing 'attr': {target}"
              return ← attrRecordUpdateDoElem recv attr rhs
                (target.getObjValAs? Bool "_unwrap_opt" == .ok true)
            match ← sliceTargetParts? target with
            | some (containerIdent, lowerTerm, upperTerm, stepTerm?) =>
                match stepTerm? with
                | none =>
                    -- `s[a:b] = repl` replaces the slice and reassigns the variable.
                    let sliceSetIdent := mkIdent ``PastaLean.pySliceSet
                    `(doElem| $containerIdent:ident := $sliceSetIdent $containerIdent $lowerTerm $upperTerm $rhs)
                | some stepTerm =>
                    -- `s[a:b:c] = repl` overwrites every `c`-th element in order.
                    let sliceSetStepIdent := mkIdent ``PastaLean.pySliceSetStep
                    `(doElem| $containerIdent:ident := $sliceSetStepIdent $containerIdent $lowerTerm $upperTerm (some $stepTerm) $rhs)
            | none =>
            match ← nestedSubscriptSetDoElem? target rhs with
            | some setStx =>
                -- `s[i] = v` (and nested `g[i][j] = v`) rebuild the container(s) and reassign.
                pure setStx
            | none =>
                let nameIdent ← getCode target `ident
                -- Closure-promoted variable CELLS (`--heap`): a `_heap_cell_def` assignment allocates
                -- the cell (one extra `allocM` over the ordinary heap RHS — `Ref τ` scalar,
                -- `Ref (Ref T)` container/object); a plain assignment to an already-promoted cell
                -- rebinds it in place with `writeRefM`.
                if ← getHeapMode then
                  if (json.getObjValAs? Bool "_heap_cell_def").toOption.getD false then
                    let cls? ← heapClassOfValue? value
                    let isContainerRhs :=
                      (match jsonNodeType? value with
                        | some "List" | some "Dict" | some "Set" => true | _ => false)
                      || (← heapContainerRef? value).isSome || cls?.isSome
                    if isContainerRhs then registerHeapContainerCell nameIdent.getId
                    else registerHeapScalarCell nameIdent.getId
                    if let some cls := cls? then registerHeapVarClass nameIdent.getId cls
                    return ← bindOrAssignLocal nameIdent (← `((← PastaLean.allocM $rhs))) none
                  if ← isHeapCellVar nameIdent.getId then
                    return ← `(doElem| PastaLean.writeRefM $nameIdent $rhs)
                -- Under `--heap`, remember that this local now holds a heap object of a known class
                -- (`p = Point(..)`, or `q = p`), so later `p.x` reads dereference it.
                if ← getHeapMode then
                  let cls? ← heapClassOfValue? value
                  match cls? with
                  | some cls => registerHeapVarClass nameIdent.getId cls
                  | none => pure ()
                  -- A constructor result or a container literal is a `Ref`; suppress the
                  -- value-semantics `_ty` ascription and let Lean infer the ref type from the RHS.
                  let isContainerLit := match jsonNodeType? value with
                    | some "List" | some "Dict" | some "Set" => true | _ => false
                  -- The RHS is a container ref if it's a literal, aliases another container
                  -- (`ys = xs`, `xs = self.items`), or is a call returning a container (`ys = f()`,
                  -- handing back the object-ref); track it so reads/mutations of the target deref.
                  let isContainerRhs ←
                    if isContainerLit
                        || (value.getObjValAs? Bool "_returns_container").toOption.getD false then
                      pure true
                    else pure (← heapContainerRef? value).isSome
                  if isContainerRhs then registerHeapVarContainer nameIdent.getId
                  if cls?.isSome || isContainerRhs then
                    -- A heap container of closures is the one case the RHS can't self-infer: an empty
                    -- `allocM []` leaves the element's function-domain universe stuck, and a later
                    -- `fun () ↦ …` append does not pin it. Re-apply the stamped heap type there.
                    let fnAsc? ← match jsonFieldOption target "_ty" with
                      | some ann =>
                          let t := TypeInfer.ofAnnotation ann
                          if t.containsFn then pure (some (← heapTypeSyntax t)) else pure none
                      | none => pure none
                    return ← bindOrAssignLocal nameIdent rhs fnAsc?
                -- A cross-type rebind (`_ty` = `PyAny`) of an immutable `let` (a loop var, `for ch in
                -- s: ch = ord(ch)`) is shadowed with a fresh `let mut`. But a `let mut` slot — incl. a
                -- `let mut x : PyAny` from a first binding — is just reassigned (a `let mut` cannot be
                -- shadowed, and a `PyAny` slot coerces the new value in).
                let conflicting := (jsonFieldOption target "_ty").any
                  (fun t => t.getObjValAs? String "id" == .ok "PyAny")
                -- A type-changing rebind (`s = list(s)`: str → List) of a name that is already a
                -- `let mut` can't re-`let mut` it (Lean forbids shadowing a mut var) nor plain-reassign
                -- (the types differ). Bind a fresh `let mut s'rbN` and SSA-rename every later `s`
                -- reference, keeping concrete types (vs. widening the slot to PyAny).
                if conflicting && (← hasVar nameIdent.getId) && (← isMutVar nameIdent.getId)
                    && !(← isPyAnySlot nameIdent.getId) then
                  let fresh ← freshRenameName nameIdent.getId
                  addRename nameIdent.getId fresh
                  addVar fresh
                  setMutVar fresh
                  setSetVar fresh (← jsonIsSetExpr value)
                  setSortedVar fresh (← jsonIsSortedListExpr value)
                  setDictVar fresh (← jsonIsDictExpr value)
                  setLibObjVar fresh (← jsonLibObjectModule? value)
                  return ← `(doElem| let mut $(mkIdent fresh):ident := $rhs)
                let shadow := conflicting && (← hasVar nameIdent.getId) && !(← isMutVar nameIdent.getId)
                -- Under `--heap`, `t = (xs, ys)` where the elements are container object-refs builds a
                -- `Ref × Ref`; the value-semantics `_ty` stamp (`List × List`) would mismatch, so drop it
                -- and let Lean infer the ref product from the RHS.
                let mut heapTupleOfRefs := false
                if (← getHeapMode) && jsonNodeType? value == some "Tuple" then
                  for e in (value.getObjValAs? (Array Json) "elts").toOption.getD #[] do
                    if (← heapContainerRef? e).isSome then heapTupleOfRefs := true
                let ty? ← if shadow || heapTupleOfRefs then pure none else stampedTypeSyntax? target
                let bound ← bindOrAssignLocal nameIdent rhs ty? shadow
                -- A `PyAny`-slotted mut var absorbs later cross-type reassignments by coercion (no rebind).
                if conflicting then setPyAnySlot nameIdent.getId true
                -- Track whether this name now holds a set, so later `==`/`<=` on it use set semantics
                -- (order-independent) rather than the list-backed ones.
                setSetVar nameIdent.getId (← jsonIsSetExpr value)
                setSortedVar nameIdent.getId (← jsonIsSortedListExpr value)
                setDictVar nameIdent.getId (← jsonIsDictExpr value)
                setLibObjVar nameIdent.getId (← jsonLibObjectModule? value)
                -- An `Option T` slot (`ans = None` then `ans = t`): remember it so an ordered `<`/`>`
                -- comparison or the `X if ans is None else ans` return unwraps the `Option` (never
                -- unmarked — a plain reassign keeps the slot, coercing the value to `some`).
                if (jsonFieldOption target "_ty").any (fun t => match TypeInfer.ofAnnotation t with
                    | .opt _ => true | _ => false) then
                  setOptionVar nameIdent.getId
                pure bound
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
    | `doElem, json => withRealIfMarked json do
        let .ok value := json.getObjVal? "value" | throwError
          s!"Return node does not have a 'value' field or it is not a JSON value: {json}"
        match value with
        -- A bare `return` (Python `return`, i.e. `None`) → `return default`, which is `()` for a
        -- `Unit`/void function but also matches a (mis-)annotated non-`Unit` return type.
        | .null =>
            if (← getValueMutatorContext) then `(doElem| return (default, $(mkIdent `self)))
            else `(doElem| return default)
        | _ =>
            let lowerValue (value : Json) : PygenM (TSyntax `term) := do
              -- `return a or b` returns the deciding *value* (`x or '0'` → the string), not a `Bool`.
              if jsonNodeType? value == some "BoolOp" then boolOpValueTerm value
              -- A call that both yields a value and mutates its receiver (`return heappop(h)`):
              -- the mutation is unobservable after a `return`, so return the value component.
              else if let some (valueTerm, _) ← mutatingCallRhsLowering? value then
                pure valueTerm
              else if jsonUsesIOEffect value || jsonNestedMonadicEffect value then
                inlineEffectfulTerm value
              else
                let s ← getCode value `term
                if jsonUsesMonadicEffect value then `((← $s:term)) else pure s
            let retTy := ((← getReturnAnnotation).map (TypeInfer.ofAnnotation · (anyDynamic := true))).getD .unknown
            let valueStx ← lowerAgainstType lowerValue value retTy
            -- In a boxed-return function, ascribe each value to `PyAny` so `try/catch` branches
            -- coerce individually (Lean would otherwise unify the branch types from the first return).
            let valueStx ← if (← getBoxReturnContext)
              then `(($valueStx : PastaLean.PyAny)) else pure valueStx
            -- In a float-reconciled function (`_ret_float`), a *branching* return `return -1 if …
            -- else v` must have BOTH branches elaborated at `ℚ`/`Float` so the `int` branch coerces
            -- up (via `Coe Int Rat`/`Coe Int Float`) instead of the first branch pinning the temp to
            -- `ℤ`. Only ascribe the branching forms — a plain `return a/b` of untyped operands would
            -- become an ambiguous `a /ₚ b : ℚ`; those are handled by the whole-body ascription.
            let valueStx ← if (← getRetFloatContext) && jsonNodeType? value == some "IfExp"
              then let t := if (← getNumericMode) == .exact then mkIdent ``Rat else mkIdent ``Float
                   `(($valueStx : $t)) else pure valueStx
            -- In a VALUE+MUTATE method, return BOTH the value and the (mutated) receiver so the caller
            -- can reassign it — `return v` becomes `return (v, self)`.
            let valueStx ← if (← getValueMutatorContext)
              then `(($valueStx, $(mkIdent `self))) else pure valueStx
            -- A simple atom (`return x` / `return 42`) is always narrow, so return it directly.
            -- A wide expression placed directly after `return`, however, can be split onto the
            -- next line by the pretty-printer, which re-parses as `return` (Unit) followed by a
            -- stray term ("must be last element in a `do` sequence"). For those we bind the value
            -- to a temporary first and `return <ident>`, which always stays on one line.
            match jsonNodeType? value with
            | some "Name" | some "Constant" =>
                `(doElem| return $valueStx)
            | _ =>
                let retIdent := mkIdent (← freshName `__py_ret)
                let bind ← `(doElem| let $retIdent:ident := $valueStx)
                let ret ← `(doElem| return $retIdent)
                pure ⟨mkNullNode #[bind.raw, ret.raw]⟩
    | _, _ => throwError s!"Unsupported syntax category for Return node"

end PastaLean

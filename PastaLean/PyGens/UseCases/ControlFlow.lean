import PastaLean.PyGens.Core.Assign

open Lean Meta Elab Term Qq Std

namespace PastaLean

/-- Lower a standalone Python expression statement inside `do` notation. -/
def exprStmtDoElemSyntax (valueJson : Json) : PygenM (TSyntax `doElem) := do
  try
    getCode valueJson `doElem
  catch e =>
    -- Only fall back when the node has no `doElem` form at all. A `doElem` generator that ran and
    -- *failed* must propagate: swallowing it silently discards statements such as `g[i].append(v)`.
    let msg ← e.toMessageData.toString
    -- `getCode` wraps the generator's message, so the marker lands at the *end*; keying it to this
    -- node's own type keeps a nested generator's failure from being mistaken for a missing form.
    let key := (valueJson.getObjValAs? String "node_type").toOption.getD ""
    unless msg.endsWith s!"Unsupported syntax category for {key} node" do throw e
    let valueStx ← getCode valueJson `term
    -- If the expression carries an effect (e.g. a statement-position ternary
    -- `print(a) if c else print(b)`, whose branches are `IO`), it must be *run*, not merely
    -- bound — `let _ := ioAction` discards the action unexecuted. Await it so the effect happens.
    if jsonUsesMonadicEffect valueJson then
      `(doElem| let _ ← $valueStx:term)
    else
      `(doElem| let _ := $valueStx)

/-- Stable helper name for top-level expression statements lowered as commands. The hash is
truncated to keep the generated name short while staying unique across the handful of top-level
expression statements in a module. -/
def topLevelExprCommandIdent (json : Json) : TSyntax `ident :=
  let h := (hash json).toNat % 1000000
  mkIdent <| Name.mkSimple s!"pyStmt_{h}"

@[pygen "Expr"]
def exprSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
    | `doElem, json => do
        let .ok valueJson := json.getObjValAs? Json "value" | throwError
          s!"Expr node does not have a 'value' field or it is not a JSON value: {json}"
        exprStmtDoElemSyntax valueJson
    | `command, json => do
        let .ok valueJson := json.getObjValAs? Json "value" | throwError
          s!"Expr node does not have a 'value' field or it is not a JSON value: {json}"
        if jsonUsesExceptionEffect valueJson then
          let bodyElem ← exprStmtDoElemSyntax valueJson
          let exprIdent := topLevelExprCommandIdent json
          let exceptIdent := mkIdent ``PastaLean.PyExcept
          `(command| def $exprIdent : $exceptIdent Unit := do
              $bodyElem:doElem
              pure ())
        else if jsonUsesIOEffect valueJson then
          let bodyElem ← exprStmtDoElemSyntax valueJson
          let exprIdent := topLevelExprCommandIdent json
          let ioIdent := mkIdent ``IO
          `(command| def $exprIdent : $ioIdent Unit := do
              $bodyElem:doElem
              pure ())
        else
          pure ⟨mkNullNode #[]⟩
    | _, _ => throwError s!"Unsupported syntax category for Expr node"

/-- `Pass` is a statement-level no-op in Python, so we lower it to an empty command
or a trivial `do` element. -/
@[pygen "Pass"]
def passSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
    | `command, _ => do
        return ⟨mkNullNode #[]⟩
    | `doElem, _ => do
        `(doElem| let _ := ())
    | _, _ => throwError s!"Unsupported syntax category for Pass node"

@[pygen "Continue"]
def continueSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
    | `command, _ => do
        return ⟨mkNullNode #[]⟩
    | `doElem, _ => do
        `(doElem| continue)
    | _, _ => throwError s!"Unsupported syntax category for Continue node"

@[pygen "Break"]
def breakSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
    | `command, _ => do
        return ⟨mkNullNode #[]⟩
    | `doElem, _ => do
        -- Inside a loop carrying a Python `else`, record that we broke so the `else` is skipped.
        match ← getBreakFlag with
        | some flag =>
            let flagIdent := mkIdent flag
            let setFlag ← `(doElem| $flagIdent:ident := true)
            let brk ← `(doElem| break)
            pure ⟨mkNullNode #[setFlag.raw, brk.raw]⟩
        | none => `(doElem| break)
    | _, _ => throwError s!"Unsupported syntax category for Break node"

@[pygen "AugAssign"]
def augAssignSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
    | `doElem, json => withRealIfMarked json do
        let .ok targetJson := json.getObjValAs? Json "target" | throwError
          s!"AugAssign node does not have a 'target' field or it is not a JSON value: {json}"
        let .ok op := json.getObjValAs? String "op" | throwError
          s!"AugAssign node does not have an 'op' field or it is not a string: {json}"
        let .ok valueJson := json.getObjValAs? Json "value" | throwError
          s!"AugAssign node does not have a 'value' field or it is not a JSON value: {json}"
        -- A RHS that both yields a value and mutates its receiver (`s += heappop(pq)`): use the
        -- value component here (it reads the original receiver) and apply the mutation afterwards.
        let mutating? ← mutatingCallRhsLowering? valueJson
        let valueCode ← match mutating? with
          | some (valueTerm, _) => pure valueTerm
          | none => getCode valueJson `term
        -- The current value: for a Name target this is the variable; for a subscript target
        -- `s[i]` it is the element read, so `s[i] += v` works on both.
        let curTerm ← getCode targetJson `term
        let updated ← match op with
          | "add" => `($curTerm +ₚ $valueCode)
          | "sub" => `($curTerm -ₚ $valueCode)
          | "mul" => `($curTerm *ₚ $valueCode)
          | "div" => `($curTerm /ₚ $valueCode)
          | "mod" => `($curTerm %ₚ $valueCode)
          | "pow" => `($curTerm ^ₚ $valueCode)
          | "floordiv" =>
              let floorDivIdent := mkIdent ``PastaLean.pyFloorDiv
              `($floorDivIdent $curTerm $valueCode)
          -- AUGASSIGN_MAP spells bitwise ops `and`/`or`/`xor` (vs BINOP's `bitand`/...).
          | "and" => `($(mkIdent ``PastaLean.pyBitAnd) $curTerm $valueCode)
          | "or" => `($(mkIdent ``PastaLean.pyBitOr) $curTerm $valueCode)
          | "xor" => `($(mkIdent ``PastaLean.pyBitXor) $curTerm $valueCode)
          | "lshift" => `($(mkIdent ``PastaLean.pyShiftLeft) $curTerm $valueCode)
          | "rshift" => `($(mkIdent ``PastaLean.pyShiftRight) $curTerm $valueCode)
          | _ => throwError s!"Unsupported augmented assignment operator: {op}"
        -- Build the base assignment, then (if the RHS was a mutating value+rest call) append its
        -- receiver-mutation as a sibling statement.
        let baseStx : TSyntax `doElem ←
          -- `self.X += v` inside a class method: `curTerm` already reads `self.X`, so rebuild
          -- `self` with the updated field (value semantics). Guarded on a mutable `self` in scope.
          if (selfAttrTarget? targetJson).isSome && (← hasVar `self) then
            selfRecordUpdateDoElem (selfAttrTarget? targetJson).get! updated
          -- `c.n += k` where `c : Ref C` (heap object ref: `self` under `--heap`, or an object
          -- ref param/var): `curTerm` already read the field via `~>`, so write the sum back through
          -- the pointer. Value-mode / non-heap-object targets fall through to the paths below.
          else if let some w ← heapAttrWriteTargetDoElem? targetJson updated then
            pure w
          else match ← nestedSubscriptSetDoElem? targetJson updated with
            | some setStx =>
                -- `s[i] += v` (and nested `g[i][j] += v`) rebuild the container with the new element.
                pure setStx
            | none =>
                let targetIdent ← getCode targetJson `ident
                -- A closure-promoted SCALAR cell (`--heap`): `n += k` rebinds the shared cell in
                -- place (`curTerm` already read it via `(← readRefM n)`). Container cells mutate
                -- their object, not the binding, so they stay on the ordinary reassignment path.
                if (← getHeapMode) && (← isHeapCellVar targetIdent.getId)
                    && !(← isHeapCellContainer targetIdent.getId) then
                  `(doElem| PastaLean.writeRefM $targetIdent $updated)
                else
                  `(doElem| $targetIdent:ident := $updated)
        match mutating? with
        | some (_, update) => pure ⟨mkNullNode #[baseStx.raw, update.raw]⟩
        | none => pure baseStx
    | _, _ => throwError s!"Unsupported syntax category for AugAssign node"

/-- In-place mutating methods that codegen lowers to a reassignment `x := f x`. -/
def mutatingMethods : List String :=
  ["sort", "append", "appendleft", "extend", "reverse", "insert", "remove", "clear",
   "pop", "popleft", "add", "discard", "update"]

/-- Does the assignment target `t` write `target` — the bare `Name`, or a subscript `target[i] = v`? -/
private def targetHitsName (target : String) (t : Json) : Bool :=
  (jsonNodeType? t == some "Name" && t.getObjValAs? String "id" == .ok target)
  || (jsonNodeType? t == some "Subscript" && (t.getObjVal? "value").toOption.any
        (fun v => jsonNodeType? v == some "Name" && v.getObjValAs? String "id" == .ok target))

/-- Does any statement in `json` reassign `target` — an `Assign`/`AugAssign`/`AnnAssign` to the name
or to `target[i]`, or an in-place mutating method `target.sort()` / `.append(…)` (which lowers to a
reassignment)? Searches nested `if`/`for`/`while`/`try` bodies but not nested `def`s. -/
partial def bodyReassignsName (target : String) (json : Json) : Bool :=
  match jsonNodeType? json with
  | some "FunctionDef" => false
  | some "Assign" | some "AugAssign" | some "AnnAssign" =>
      (match json.getObjVal? "target" with
       | .ok t => targetHitsName target t
       | _ => false)
      || (json.getObjVal? "value" |>.toOption |>.any (bodyReassignsName target))
  | some "Call" =>
      (match json.getObjVal? "func" with
       | .ok f => jsonNodeType? f == some "Attribute"
           && (f.getObjVal? "value").toOption.any
                (fun v => jsonNodeType? v == some "Name" && v.getObjValAs? String "id" == .ok target)
           && (f.getObjValAs? String "attr").toOption.any mutatingMethods.contains
       | _ => false)
      || (match json with
          | .obj fields => fields.toList.any (fun (_, v) => bodyReassignsName target v)
          | _ => false)
  | _ => match json with
    | .arr elems => elems.any (bodyReassignsName target)
    | .obj fields => fields.toList.any (fun (_, v) => bodyReassignsName target v)
    | _ => false

/-- Lower a for-loop target into a binder and optional destructuring prelude. A target name the
`bodyElems` reassign gets a mutable shadow (`let mut`) instead of an immutable binder, so the
reassignment sticks and the `if` lowering doesn't pre-declare a `let mut … := default` shadowing it. -/
def forTargetBinder (targetJson : Json) (bodyElems : Array Json := #[]) :
    PygenM (TSyntax `ident × Array (TSyntax `doElem)) := do
  match jsonNodeType? targetJson with
  | some "Name" =>
      let targetIdent ← getCode targetJson `ident
      let mutated := bodyElems.any (bodyReassignsName targetIdent.getId.toString)
      -- Lean forbids a `for` binder from shadowing an enclosing `let mut`. When Python reuses
      -- a name that is already a mutable variable in scope (`p = 2; ...; for p in ...:`), bind
      -- a fresh loop variable and assign it into the existing mutable, matching Python's rebind.
      if ← hasVar targetIdent.getId then
        let loopIdent := mkIdent (← freshName `__py_loop)
        let assign ← `(doElem| $targetIdent:ident := $loopIdent)
        pure (loopIdent, #[assign])
      else if mutated then
        let loopIdent := mkIdent (← freshName `__py_loop)
        -- A `_ty` of `PyAny` means the body rebinds this name to a CONFLICTING type
        -- (`for ch in s: ch = ord(ch)`). A `let mut` has one fixed type and cannot be shadowed, so
        -- bind it plainly and leave it unregistered — the rebind then emits its own `let mut`,
        -- which shadows this one. That matches Python: code after the rebind sees the new value.
        let conflicting := (jsonFieldOption targetJson "_ty").any
          (fun t => t.getObjValAs? String "id" == .ok "PyAny")
        if conflicting then
          addVar targetIdent.getId
          pure (loopIdent, #[← `(doElem| let $targetIdent:ident := $loopIdent)])
        else
          let decl ← `(doElem| let mut $targetIdent:ident := $loopIdent)
          addVar targetIdent.getId
          pure (loopIdent, #[decl])
      else
        pure (targetIdent, #[])
  | some "Tuple" =>
      let .ok elts := targetJson.getObjValAs? (Array Json) "elts" | throwError
        s!"For-loop tuple target does not have an 'elts' field: {targetJson}"
      if elts.size < 2 then
        throwError "For-loop tuple target must have at least two elements."
      let mut idents := #[]
      for elt in elts do
        unless jsonNodeType? elt == some "Name" do
          throwError "Only Name targets are supported in for-loop tuple unpacking."
        idents := idents.push (← getCode elt `ident)
      let n := idents.size
      let pairIdent := mkIdent (← freshName `_pair)
      -- When the inference pass marked the iterable's element a *list* (`for a,b in edges` with
      -- `edges : list[list[int]]`), unpack by list index; otherwise it is a tuple, unpacked via `Prod`.
      let listUnpack := targetJson.getObjValAs? Bool "_list_unpack" == .ok true
      let mut prelude : Array (TSyntax `doElem) := #[]
      for i in List.range n do
        let acc ←
          if listUnpack then
            let iStx ← intToStx (i : Int)
            `($(mkIdent ``PastaLean.pyListGetItem) $pairIdent $iStx)
          else tupleAccessTerm pairIdent i n
        -- An unpacked element the body reassigns (`for i, word in …: word = …`) must be `let mut` —
        -- UNLESS the rebind changes its type (`_ty` = `PyAny`, e.g. `for i, c in …: c = ord(c)`).
        -- A `let mut` has one fixed type and cannot be shadowed, so bind that one plainly and let
        -- the rebind introduce its own `let mut` over it.
        let eltConflicts := (jsonFieldOption elts[i]! "_ty").any
          (fun t => t.getObjValAs? String "id" == .ok "PyAny")
        if bodyElems.any (bodyReassignsName idents[i]!.getId.toString) then
          if eltConflicts then
            prelude := prelude.push (← `(doElem| let $(idents[i]!) := $acc))
          else
            prelude := prelude.push (← `(doElem| let mut $(idents[i]!) := $acc))
          addVar idents[i]!.getId
        else
          prelude := prelude.push (← `(doElem| let $(idents[i]!) := $acc))
      pure (pairIdent, prelude)
  | _ =>
      throwError s!"Unsupported for-loop target: {targetJson}"

/-!
  Top-level state threading.

  Lean has no top-level statement execution, so a bare `for` at module scope cannot
  mutate a module global. The Python pre-pass annotates such a block with
  `mutated_names` (the names it reassigns) and `state_init` (the versioned
  initializer to read for each name's pre-block value). We lower the block to a
  fold that returns the updated names as a tuple, then re-export each name as a
  fresh top-level `def` — keeping translated top-level names reusable declarations
  rather than hiding them inside `main`.
-/

/-- Read the `mutated_names` annotation (sorted name list) from a top-level block. -/
def blockMutatedNames? (json : Json) : Option (Array String) :=
  match json.getObjValAs? (Array String) "mutated_names" with
  | .ok names => if names.isEmpty then none else some names
  | .error _ => none

/-- Read the `state_init` map entry: the versioned initializer identifier for `name`. -/
def blockStateInit (json : Json) (name : String) : PygenM (TSyntax `ident) := do
  let .ok initObj := json.getObjVal? "state_init" | throwError
    s!"Top-level block is missing a 'state_init' field: {json}"
  let .ok initName := initObj.getObjValAs? String name | throwError
    s!"state_init has no entry for mutated name '{name}': {initObj}"
  pure (mkIdent initName.toName)

/-- Name the generated result `def` after the block's `block_id` (a short, position-based,
name-independent hash) so distinct top-level blocks never collide — even two identical ones.
`kindPrefix` distinguishes the construct (`__py_for`, `__py_if`, ...). -/
def blockResultIdent (json : Json) (kindPrefix : String) : PygenM (TSyntax `ident) := do
  let .ok blockId := json.getObjValAs? String "block_id" | throwError
    s!"Top-level block is missing a 'block_id' field: {json}"
  pure (mkIdent (Name.mkSimple s!"{kindPrefix}_{blockId}"))

/-- Build the right-nested tuple term `(n0, (n1, n2))` from a list of idents. -/
partial def buildNameTuple (idents : Array (TSyntax `ident)) : PygenM (TSyntax `term) := do
  match idents.toList with
  | [] => `(())
  | [single] => `($single)
  | first :: rest => do
      let restTuple ← buildNameTuple rest.toArray
      `(($first, $restTuple))

/-- Read the re-export identifier for a mutated `name`: the clean `name` when this block
holds its final value, or a versioned (dead) name when a later assignment shadows it. -/
def blockReexportName (json : Json) (name : String) : String :=
  match json.getObjVal? "reexport_names" with
  | .ok obj =>
      match obj.getObjValAs? String name with
      | .ok reexport => reexport
      | .error _ => name
  | .error _ => name

/-- Re-export each mutated name as a fresh top-level `def` reading from the block's
result. A single name needs no projection; multiple names project the result tuple.
The re-export identifier comes from the block's `reexport_names` annotation so a shadowed
result (re-initialized later) gets a versioned name instead of colliding on the clean one. -/
def reexportCommands (json : Json) (resultIdent : TSyntax `ident) (names : Array String) :
    PygenM (Array (TSyntax `command)) := do
  let n := names.size
  if n == 1 then
    let nameIdent := mkIdent (blockReexportName json names[0]!).toName
    -- Privacy keys on the original Python name, not the (possibly versioned) re-export id.
    pure #[← applyPrivacy names[0]! (← `(command| def $nameIdent := $resultIdent))]
  else
    let mut cmds := #[]
    for i in List.range n do
      let nameIdent := mkIdent (blockReexportName json names[i]!).toName
      let acc ← tupleAccessTerm resultIdent i n
      cmds := cmds.push (← applyPrivacy names[i]! (← `(command| def $nameIdent := $acc)))
    pure cmds

/-- Build `mut` prelude bindings that bind each mutated `name` to its projection of
the accumulator identifier `sourceIdent` (the whole value for a single name). -/
def stateMutPrelude (sourceIdent : TSyntax `ident) (names : Array String) :
    PygenM (Array (TSyntax `doElem)) := do
  let n := names.size
  let mut elems : Array (TSyntax `doElem) := #[]
  if n == 1 then
    let nameIdent := mkIdent names[0]!.toName
    elems := elems.push (← `(doElem| let mut $nameIdent := $sourceIdent))
  else
    for i in List.range n do
      let nameIdent := mkIdent names[i]!.toName
      let acc ← tupleAccessTerm sourceIdent i n
      elems := elems.push (← `(doElem| let mut $nameIdent := $acc))
  pure elems

/-- Build `Id.run do <prelude>; <body>; return (names...)` for a state-threading block.
The body statements run through the existing `doElem` generators, so `Assign`/`AugAssign`
on the mutated names lower to reassignment of the `mut` locals. -/
def stateRunBlock (prelude : Array (TSyntax `doElem)) (bodyElems : Array Json)
    (names : Array String) : PygenM (TSyntax `term) := do
  let mut doElems := prelude
  for elem in bodyElems do
    doElems := appendDoElems doElems (← getCode elem `doElem)
  let returnTuple ← buildNameTuple (names.map (mkIdent ·.toName))
  doElems := doElems.push (← `(doElem| return $returnTuple))
  let idRunIdent := mkIdent ``Id.run
  `($idRunIdent do
      $[$doElems:doElem]*)

/-- Reject top-level state-threading blocks that carry I/O or exception effects.

These would need the block (and every re-exported name, transitively) to be lowered in
`IO`/`PyExcept` rather than the pure `Id.run`, which is not implemented yet. Lowering them
as pure would silently drop the effect, so we fail loudly instead. -/
def ensureTopLevelBlockIsPure (bodyElems : Array Json) (what : String) : PygenM Unit := do
  if bodyElems.any jsonUsesIOEffect then
    throwError "Top-level {what} that performs I/O (e.g. `print`/`input`) is not supported \
      yet; move it into a function or an `if __name__ == \"__main__\"` block."
  if bodyElems.any jsonUsesExceptionEffect then
    throwError "Top-level {what} that can raise (e.g. `raise`/`try`) is not supported yet; \
      move it into a function or an `if __name__ == \"__main__\"` block."

/-- Lower a top-level `for` block with state threading: emit `def __py_for := List.foldl
(fun state i => Id.run do ...) init iter`, then re-export the mutated names. -/
def topLevelForCommands (json : Json) (names : Array String) : PygenM (Array (TSyntax `command)) := do
  let .ok targetJson := json.getObjValAs? Json "target" | throwError
    s!"Top-level For is missing a 'target' field: {json}"
  let .ok iterJson := json.getObjValAs? Json "iter" | throwError
    s!"Top-level For is missing an 'iter' field: {json}"
  let .ok bodyElems := json.getObjValAs? (Array Json) "body" | throwError
    s!"Top-level For is missing a 'body' field: {json}"
  let .ok orelseElems := json.getObjValAs? (Array Json) "orelse" | throwError
    s!"Top-level For is missing an 'orelse' field: {json}"
  unless orelseElems.isEmpty do
    throwError "Top-level for-else blocks are not supported."
  ensureTopLevelBlockIsPure bodyElems "for-loop"
  let loopVarIdent ← match jsonNodeType? targetJson with
    | some "Name" => getCode targetJson `ident
    | _ => throwError "Only a simple Name loop target is supported in top-level for state threading."
  -- Initial accumulator: tuple of the versioned initializers.
  let initIdents ← names.mapM (blockStateInit json)
  let initTuple ← buildNameTuple initIdents
  -- Register the mutated names so body `Assign`/`AugAssign` lower to reassignment.
  for name in names do
    addVar name.toName
  -- Fold step: bind state names as `mut` from the accumulator, run the body, return tuple.
  let stateIdent := mkIdent (← freshName `_state)
  let prelude ← stateMutPrelude stateIdent names
  let foldBody ← stateRunBlock prelude bodyElems names
  let iterCode ← rangeIterSyntax iterJson
  let resultIdent ← blockResultIdent json "__py_for"
  let foldlIdent := mkIdent ``List.foldl
  let foldDef ← `(command|
    def $resultIdent := $foldlIdent (fun $stateIdent $loopVarIdent => $foldBody) $initTuple $iterCode)
  let reexports ← reexportCommands json resultIdent names
  pure (#[foldDef] ++ reexports)

/-- Lower a top-level single-statement block (`if`/`match`/`while`) with state threading.

Unlike `for`, there is no iterable to fold over: the block runs once. We emit
`def __py_block := Id.run do let mut n := n₀; ...; <stmt>; return (n...)` then re-export.
The block's own statement (the `if`/`match`/`while`) lowers through its existing `doElem`
generator, so branches, `orelse`, and nested mutation all work, and names absent from a
branch keep their initial value. -/
def topLevelStmtCommands (json : Json) (names : Array String) (kindPrefix : String)
    (label : String) : PygenM (Array (TSyntax `command)) := do
  ensureTopLevelBlockIsPure #[json] label
  -- Bind each mutated name as `mut` from its versioned initializer, then run the
  -- whole block statement and return the updated tuple.
  for name in names do
    addVar name.toName
  let mut prelude : Array (TSyntax `doElem) := #[]
  let n := names.size
  if n == 1 then
    let nameIdent := mkIdent names[0]!.toName
    let initIdent ← blockStateInit json names[0]!
    prelude := prelude.push (← `(doElem| let mut $nameIdent := $initIdent))
  else
    for name in names do
      let nameIdent := mkIdent name.toName
      let initIdent ← blockStateInit json name
      prelude := prelude.push (← `(doElem| let mut $nameIdent := $initIdent))
  -- The single block statement (this `json`) lowers through its `doElem` generator.
  let blockBody ← stateRunBlock prelude #[json] names
  let resultIdent ← blockResultIdent json kindPrefix
  let blockDef ← `(command| def $resultIdent := $blockBody)
  let reexports ← reexportCommands json resultIdent names
  pure (#[blockDef] ++ reexports)

/-- Wrap a lowered loop (`coreElems`) with Python `else`-clause handling. With no `else`
(`breakFlag?` is `none`) the loop's statements are emitted unchanged. Otherwise the break flag is
declared `let mut f := false` before the loop and the `else` body runs afterward guarded by
`if !f`, so it executes only when the loop completed without `break`. -/
def loopWithElseDoElem (breakFlag? : Option Name) (coreElems : Array (TSyntax `doElem))
    (orelseElems : Array Json) : PygenM (TSyntax `doElem) := do
  match breakFlag? with
  | none => pure ⟨mkNullNode (coreElems.map TSyntax.raw)⟩
  | some flag =>
      let flagIdent := mkIdent flag
      let initFlag ← `(doElem| let mut $flagIdent:ident := false)
      let elseStxArray ← withFixedVariables do
        let mut arr : Array (TSyntax `doElem) := #[]
        for elem in orelseElems do
          arr := appendDoElems arr (← getCode elem `doElem)
        pure arr
      let noop ← noopDoElemSyntax
      let elseCheck ← `(doElem| if (!$flagIdent) then
          $[$elseStxArray:doElem]*
        else
          $noop:doElem)
      pure ⟨mkNullNode (#[initFlag.raw] ++ coreElems.map TSyntax.raw ++ #[elseCheck.raw])⟩

/-- Pre-declare `let mut x : T := default` for each name a block leaks out (listed under `namesKey`,
typed via `typesKey`) that is not already bound in the enclosing scope. Python is function-scoped;
Lean blocks are not, so a name first bound inside an `if`/`try`/`for`/`while` and used outside it must
be hoisted. Each is registered as a mut var so a later branch/body assignment REASSIGNS it (boxing a
`PyAny`) rather than shadowing. For nested loops the outer block's list already carries an inner-bound
name (the annotate pass collects recursively), so hoisting there lands it at the right outer scope. -/
def hoistEscapingDecls (json : Json) (namesKey typesKey : String) :
    PygenM (Array (TSyntax `doElem)) := do
  let names := (json.getObjValAs? (Array String) namesKey).toOption.getD #[]
  let mut decls : Array (TSyntax `doElem) := #[]
  for nm in names do
    let nmName := nm.toName
    unless (← hasVar nmName) do
      let nmIdent := mkIdent nmName
      let tyStx? ← match (jsonFieldOption json typesKey).bind (·.getObjVal? nm |>.toOption) with
        | some ann => stampedTypeSyntax? (Json.mkObj [("_ty", ann)])
        | none => pure none
      let decl ← match tyStx? with
        | some tyStx => `(doElem| let mut $nmIdent:ident : $tyStx := default)
        | none => `(doElem| let mut $nmIdent:ident := default)
      decls := decls.push decl
      addVar nmName
      setMutVar nmName
  return decls

@[pygen "While"]
def whileSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
    | `doElem, json => do
        let .ok test := json.getObjVal? "test" | throwError
          s!"While node does not have a 'test' field or it is not a JSON value: {json}"
        let testStx ← truthyConditionTerm test (← withPropCondition true (getCode test `term))
        let .ok bodyElems := json.getObjValAs? (Array Json) "body" | throwError
          s!"While node does not have a 'body' field or it is not a JSON array: {json}"
        let .ok orelseElems := json.getObjValAs? (Array Json) "orelse" | throwError
          s!"While node does not have an 'orelse' field or it is not a JSON array: {json}"
        -- Python `while … else`: the `else` runs iff the loop exited normally (test became false),
        -- not via `break`. Tracked with a flag set inside `break` (scoped via `withBreakFlag`).
        let breakFlag? ← if orelseElems.isEmpty then pure none
          else pure (some (← freshName `__py_broke))
        -- Hoist body-bound names that escape the loop (used after it) BEFORE lowering the body, so the
        -- body's assignments become reassignments of one enclosing `let mut`, matching Python scoping.
        let hoistDecls ← hoistEscapingDecls json "while_assigned_names" "while_assigned_types"
        -- Scope the body's variable declarations to the loop (see the `for` case): names
        -- first bound in the body do not leak to the enclosing scope.
        let bodyStxArray ← withFixedVariables do withBreakFlag breakFlag? do
          let mut bodyStxArray := #[]
          for elem in bodyElems do
              let elemStx ← getCode elem `doElem
              bodyStxArray := appendDoElems bodyStxArray elemStx
          pure bodyStxArray
        -- Parenthesize the test so its last token never glues to the `do` keyword.
        let whileLoop ← `(doElem| while ($testStx) do
            $[$bodyStxArray:doElem]*)
        let loopStx ← loopWithElseDoElem breakFlag? #[whileLoop] orelseElems
        if hoistDecls.isEmpty then pure loopStx
        -- `loopStx` is itself a null-node (from `loopWithElseDoElem`); splice its children flat rather
        -- than nesting another null-node, which would leave an inner `null` the consumer can't flatten.
        else pure ⟨mkNullNode (hoistDecls.map TSyntax.raw ++ loopStx.raw.getArgs)⟩
    | `command, json => do
        -- A top-level `while` that mutates module globals is a state transformer.
        -- It lowers like `if`/`match`: `Id.run do let mut n := n₀; while ...; return (n...)`.
        match blockMutatedNames? json with
        | some names =>
            let cmds ← topLevelStmtCommands json names "__py_while" "while-loop"
            return ⟨mkNullNode (cmds.map TSyntax.raw)⟩
        | none =>
            throwError "Top-level `while` is only supported when it mutates a module global \
              (state threading)."
    | _, _ => throwError s!"Unsupported syntax category for While node"

@[pygen "For"]
def forSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
    | `doElem, json => do
        let .ok targetJson := json.getObjValAs? Json "target" | throwError
          s!"For node does not have a 'target' field or it is not a JSON value: {json}"
        let .ok iterJson := json.getObjValAs? Json "iter" | throwError
          s!"For node does not have an 'iter' field or it is not a JSON value: {json}"
        let .ok bodyElems := json.getObjValAs? (Array Json) "body" | throwError
          s!"For node does not have a 'body' field or it is not a JSON array: {json}"
        let .ok orelseElems := json.getObjValAs? (Array Json) "orelse" | throwError
          s!"For node does not have an 'orelse' field or it is not a JSON array: {json}"
        -- Python `for … else`: the `else` runs iff the loop completed without `break`. Track that
        -- with a `let mut` flag set inside `break` (scoped to this loop via `withBreakFlag`).
        let breakFlag? ← if orelseElems.isEmpty then pure none
          else pure (some (← freshName `__py_broke))
        -- Hoist body-bound names that escape the loop (used after it) to one enclosing `let mut`,
        -- matching Python's function scoping (Lean's loop body is its own scope). For nested loops the
        -- OUTER loop's list already carries an inner-bound name, so it lands at the outermost scope.
        let hoistDecls ← hoistEscapingDecls json "for_assigned_names" "for_assigned_types"
        -- Scope the loop's target and remaining body declarations to the loop: names used only inside
        -- the body keep their per-iteration scope (only escaping names were hoisted above).
        let (targetIdent, bodyStxArray) ← withFixedVariables do withBreakFlag breakFlag? do
          let (targetIdent, preludeElems) ← forTargetBinder targetJson bodyElems
          let mut bodyStxArray := preludeElems
          for elem in bodyElems do
            let elemStx ← getCode elem `doElem
            bodyStxArray := appendDoElems bodyStxArray elemStx
          pure (targetIdent, bodyStxArray)
        -- Parenthesize the iterable so its last token never glues to the `do` keyword
        -- (e.g. an iterable ending in `none` would otherwise pretty-print as `nonedo`).
        let coreElems : Array (TSyntax `doElem) ←
          if jsonUsesIOEffect iterJson then
            -- The iterable is IO-derived (e.g. `range(int(input()))` → `IO (List Int)`, or
            -- `input()` → `IO String`). Await it once into a local, then iterate over the pure
            -- value — otherwise a raw `IO X` would flow into a pure position. The awaited value is
            -- normalized through `pyIter` (unless it is a `range`, already a `List Int`) so a
            -- string iterable binds one-character strings, matching the pure path.
            let rawIter ← getCode iterJson `term
            let itIdent := mkIdent (← freshName `__py_iter)
            let bindIt ← `(doElem| let $itIdent:ident ← $rawIter:term)
            let iterTerm ←
              if isRangeIter iterJson then pure (itIdent : TSyntax `term)
              else `($(mkIdent ``pyIter) $itIdent)
            let forLoop ← `(doElem| for $targetIdent:ident in ($iterTerm) do
                $[$bodyStxArray:doElem]*)
            pure #[bindIt, forLoop]
          else
            -- Under `--heap`, a container held by reference is dereferenced before iterating.
            let iterCode ← match ← heapContainerDeref? iterJson with
              | some deref => `($(mkIdent ``pyIter) $deref)
              | none => rangeIterSyntax iterJson
            let forLoop ← `(doElem| for $targetIdent:ident in ($iterCode) do
                $[$bodyStxArray:doElem]*)
            pure #[forLoop]
        let loopStx ← loopWithElseDoElem breakFlag? coreElems orelseElems
        if hoistDecls.isEmpty then pure loopStx
        -- `loopStx` is itself a null-node (from `loopWithElseDoElem`); splice its children flat rather
        -- than nesting another null-node, which would leave an inner `null` the consumer can't flatten.
        else pure ⟨mkNullNode (hoistDecls.map TSyntax.raw ++ loopStx.raw.getArgs)⟩
    | `command, json => do
        match blockMutatedNames? json with
        | some names =>
            let cmds ← topLevelForCommands json names
            return ⟨mkNullNode (cmds.map TSyntax.raw)⟩
        | none =>
            throwError "Top-level `for` without state threading is not supported; \
              a top-level loop must mutate at least one module global."
    | _, _ => throwError s!"Unsupported syntax category for For node"

@[pygen "If"]
def ifSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
    | `doElem, json => do
        let .ok testJson := json.getObjValAs? Json "test" | throwError
          s!"If node does not have a 'test' field or it is not a JSON value: {json}"
        let .ok bodyElems := json.getObjValAs? (Array Json) "body" | throwError
          s!"If node does not have a 'body' field or it is not a JSON array: {json}"
        let .ok orelseElems := json.getObjValAs? (Array Json) "orelse" | throwError
          s!"If node does not have an 'orelse' field or it is not a JSON array: {json}"
        -- Lower the test in condition position so a direct comparison may be a provable `Prop`
        -- (paired with the `if h : …` hypothesis below); `and`/`or`/`not` reset this to `Bool`.
        let testStx ← truthyConditionTerm testJson (← withPropCondition true (getCode testJson `term))
        -- Hoist names first bound inside a branch but escaping the `if` (read after it, or in the
        -- other branch). Each branch lowers to its own `do` block, so a `let mut` there is invisible
        -- outside it; pre-declaring one enclosing `let mut name : T := default` turns the branch
        -- assignments into reassignments, matching Python's cross-branch binding.
        let hoistDecls ← hoistEscapingDecls json "if_assigned_names" "if_assigned_types"
        -- Bind the branch condition as a hypothesis (`if h : cond then …`), so proofs about the
        -- generated code have the test available: `h` in the then-branch, `¬h` in the else.
        -- Reserve the name *before* lowering the branch bodies: `freshName` registers it, so a
        -- nested `if` inside the body gets `h_1` (not another `h`) and the outer hypothesis stays
        -- visible inside the nested branch instead of being shadowed. (`withFixedVariables` below
        -- restores per-branch scope, which is why the reservation must happen out here first.)
        let hName := mkIdent (← freshName `h)
        -- Scope each branch's variable declarations to that branch: a name first bound in the
        -- `then` branch must not leak into the `else` branch's scope (which would make the `else`
        -- assignment a reassignment of a `let mut` it cannot see). Names that escape the whole
        -- `if` are handled by the hoist above; everything else stays branch-local.
        let bodyStxArray ← withFixedVariables do
          let mut arr : Array (TSyntax `doElem) := #[]
          for elem in bodyElems do
            arr := appendDoElems arr (← getCode elem `doElem)
          pure arr
        let orelseStxArray ← withFixedVariables do
          let mut arr : Array (TSyntax `doElem) := #[]
          for elem in orelseElems do
            arr := appendDoElems arr (← getCode elem `doElem)
          pure arr
        let ifStx ←
          if orelseStxArray.isEmpty then
            let noop ← noopDoElemSyntax
            `(doElem| if $hName : $testStx then
                $[$bodyStxArray:doElem]*
              else
                $noop:doElem
            )
          else
            `(doElem| if $hName : $testStx then
                $[$bodyStxArray:doElem]*
              else
                $[$orelseStxArray:doElem]*)
        if hoistDecls.isEmpty then
          pure ifStx
        else
          pure ⟨mkNullNode ((hoistDecls.push ifStx).map TSyntax.raw)⟩
    | `command, json => do
        -- A top-level `if` that mutates module globals is a state transformer.
        match blockMutatedNames? json with
        | some names =>
            let cmds ← topLevelStmtCommands json names "__py_if" "if-block"
            return ⟨mkNullNode (cmds.map TSyntax.raw)⟩
        | none => pure ()
        -- Otherwise, the only supported top-level `if` is the `__main__` guard, which
        -- becomes Lean's `main` entry point.
        let isGuard := json.getObjValAs? Bool "is_main_guard" |>.toOption.getD false
        unless isGuard do
          throwError "A top-level `if` must either mutate a module global \
            (state threading) or be an `if __name__ == \"__main__\"` guard."
        let .ok bodyElems := json.getObjValAs? (Array Json) "body" | throwError
          s!"If node does not have a 'body' field or it is not a JSON array: {json}"
        let mut bodyStxArray := #[]
        for elem in bodyElems do
          let elemStx ← getCode elem `doElem
          bodyStxArray := appendDoElems bodyStxArray elemStx
        -- Run-twin (`--mode both`): the entry wrapper is emitted as `main'rn` (and its body call to
        -- `main'` is suffixed to `main''rn` by the Name pygen), leaving the prove `main` as the file's
        -- single Lean entry point.
        let mainIdent := mkIdent (← withRunSuffix "main").toName
        -- A guard that calls into a real-valued (`ℝ`, exact mode) function makes the `main`
        -- wrapper depend on a `noncomputable` def, so it must itself be `noncomputable` (it
        -- still elaborates / compile-checks; it just can't be run — use `--mode run` to run).
        let isReal := (← getNumericMode) == .exact && json.getObjValAs? Bool "_real_fn" == .ok true
        let usesExceptions := bodyNeedsExceptionMonad bodyElems
        let usesIO := bodyNeedsIOMonad bodyElems
        let useProofMonad ← shouldUseProofMonad
        -- Determine monad type based on mode
        let usesProofMode := useProofMonad && (usesExceptions || usesIO)
        let usesPureExceptions := !useProofMonad && (← getNumericMode) == .exact && usesExceptions && !usesIO
        if ← needsHeapMonad bodyElems then
          -- Heap `main`: run the body from the empty heap, then surface output + any exception. Run
          -- mode uses `PyHeapIO` (real IO); prove mode uses `PyHeapProofM` (IO modeled as state).
          let valId := mkIdent `Val
          let outputLinesName := mkIdent `outputLines
          let lineName := mkIdent `line
          let mainBody ← if useProofMonad then
            `(do
              let inputText ← IO.getStdin >>= fun h => h.readToEnd
              let inputLines := String.splitOn inputText "\n"
              let inputStream : PastaLean.ProofMode.IOStream :=
                ⟨0, fun i => PastaLean.ProofMode.IOResult.success (List.getD inputLines i "")⟩
              let initState : PastaLean.HeapIOState $valId := ⟨PastaLean.emptyHeap, ⟨inputStream, []⟩⟩
              let (result, finalState) := PastaLean.PyHeapProofM.runProgram (V := $valId) (do
                  $[$bodyStxArray:doElem]*
                  pure ()) initState
              -- Splice `mkIdent` identifiers (as the non-heap proof path does): a literal identifier
              -- written inline in the quasiquote glues to the following `do` keyword when formatted
              -- (`outputLinesdo`); an antiquoted identifier renders with correct spacing.
              let $outputLinesName := finalState.io.output
              for $lineName in $outputLinesName do
                IO.print $lineName
              match result with
              | .ok _ => pure ()
              | .error err => throw (IO.userError (toString err)))
          else
            `(do
              let (result, _heap) ← PastaLean.PyHeapIO.runProgram (V := $valId) (do
                  $[$bodyStxArray:doElem]*
                  pure ())
              match result with
              | .ok _ => pure ()
              | .error err => throw (IO.userError (toString err)))
          if isReal then `(command| noncomputable def $mainIdent : IO Unit := $mainBody)
          else `(command| def $mainIdent : IO Unit := $mainBody)
        else if usesProofMode then
          -- Proof mode: Run PyProofM with input from stdin, then print output to stdout
          -- PyProofM α = ExceptT PyException (StateM IOState) α
          -- Running it: IOState → (Except PyException α × IOState)
          let proofMonadIdent := mkIdent ``PastaLean.ProofMode.PyProofM
          let ioStreamIdent := mkIdent ``PastaLean.ProofMode.IOStream
          let ioStateIdent := mkIdent ``PastaLean.ProofMode.IOState
          let ioResultSuccessIdent := mkIdent ``PastaLean.ProofMode.IOResult.success
          let ioUserErrorIdent := mkIdent ``IO.userError
          let outputLinesName := mkIdent `outputLines
          let lineName := mkIdent `line
          let mainBody ← `(do
            -- Read all input from stdin and convert to stream
            -- Note: The stream produces IOResult values (success/error), not plain strings.
            -- This infinite-success pattern is suitable for competitive programming where
            -- input() should never fail. For finite input with EOF:
            --   let inputStream := ⟨0, fun i => if i < inputLines.length
            --                                    then IOResult.success (inputLines.get! i)
            --                                    else IOResult.error IOError.EndOfFile⟩
            let inputText ← IO.getStdin >>= fun h => h.readToEnd
            let inputLines := String.splitOn inputText "\n"
            let inputStream : $ioStreamIdent := ⟨0, fun i => $ioResultSuccessIdent (List.getD inputLines i "")⟩
            let initState : $ioStateIdent := ⟨inputStream, []⟩
            -- Run the PyProofM computation
            let (result, finalState) := (((do
                $[$bodyStxArray:doElem]*
                pure ()
              ) : $proofMonadIdent Unit)) initState
            -- Print accumulated output to stdout
            let $outputLinesName := finalState.output
            for $lineName in $outputLinesName do
              IO.print $lineName
            -- Convert result to IO
            match result with
            | .ok _ => pure ()
            | .error err => throw ($ioUserErrorIdent (toString err)))
          if isReal then `(command| noncomputable def $mainIdent : IO Unit := $mainBody)
          else `(command| def $mainIdent : IO Unit := $mainBody)
        else if usesExceptions then
          -- Exception handling path - convert PyExcept/PyExceptId result to IO
          let exceptIdent := mkIdent (if usesPureExceptions then ``PastaLean.PyExceptId else ``PastaLean.PyExcept)
          let ioUserErrorIdent := mkIdent ``IO.userError
          let mainBody ← if usesPureExceptions then
            -- For PyExceptId, we need to lift it to IO - run it in Id then convert to IO
            `(do
              let result := (((do
                  $[$bodyStxArray:doElem]*
                  pure ()
                ) : $exceptIdent Unit)).run
              match result with
              | .ok _ => pure ()
              | .error err => throw ($ioUserErrorIdent (toString err)))
          else
            -- For PyExcept (IO-backed), unwrap normally
            `(do
              let result ← (((do
                  $[$bodyStxArray:doElem]*
                  pure ()
                ) : $exceptIdent Unit)).run
              match result with
              | .ok _ => pure ()
              | .error err => throw ($ioUserErrorIdent (toString err)))
          if isReal then `(command| noncomputable def $mainIdent : IO Unit := $mainBody)
          else `(command| def $mainIdent : IO Unit := $mainBody)
        else if usesIO then
          let mainBody ← `(do
              $[$bodyStxArray:doElem]*
              pure ())
          if isReal then `(command| noncomputable def $mainIdent : IO Unit := $mainBody)
          else `(command| def $mainIdent : IO Unit := $mainBody)
        else
          -- Pure body - no IO, no exceptions
          -- For mode=both, bodyStxArray contains a call to main' (the renamed Python main function).
          -- Since main' returns Id Unit (via Id.run), we can't use monadic bind (←) in IO context.
          -- Solution: evaluate the call directly with := (pure binding).
          -- This works because Id.run evaluates to a pure value.
          let mainBody ← `(do
              $[$bodyStxArray:doElem]*
              pure ())
          if isReal then `(command| noncomputable def $mainIdent : IO Unit := $mainBody)
          else `(command| def $mainIdent : IO Unit := $mainBody)
    | _, _ => throwError s!"Unsupported syntax category for If node"


end PastaLean

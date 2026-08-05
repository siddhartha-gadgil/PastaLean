import PastaLean.PyGens.Core.Utils
import PastaLean.PyGens.Calls.CallShared

open Lean Meta Elab Term Qq Std

namespace PastaLean

/-- Project the `.kind` field from a caught `PyException`. -/
def exceptionKindTerm (caughtIdent : TSyntax `ident) : PygenM (TSyntax `term) := do
  let caughtTerm : TSyntax `term := mkIdent caughtIdent.getId
  `(($(caughtTerm):term).OfKind)

/-- Raise a structured `PyException` value in generated `Except` code. -/
def throwExceptionDoElemSyntax (value : TSyntax `term) : PygenM (TSyntax `doElem) := do
  `(doElem| throw $value)

/-- Recover the exception constructor name from the JSON term used in `raise` / `except`. -/
def exceptionNameFromTermJson (json : Json) : PygenM String := do
  let .ok nodeType := json.getObjValAs? String "node_type" | throwError
    s!"Exception term is missing a 'node_type' field: {json}"
  match nodeType with
  | "Name" =>
      let .ok id := json.getObjValAs? String "id" | throwError
        s!"Exception name node is missing an 'id': {json}"
      return id
  | "Attribute" =>
      let .ok attr := json.getObjValAs? String "attr" | throwError
        s!"Exception attribute node is missing an 'attr': {json}"
      return attr
  | _ =>
      throwError s!"Unsupported exception type node: {nodeType}"

/-- Lower a Python `raise` payload into a `PyException` runtime value. -/
def exceptionValueTerm (excJson? : Option Json) : PygenM (TSyntax `term) := do
  let mkExcIdent := mkIdent ``PastaLean.PyException.Raise
  match excJson? with
  | none => `($mkExcIdent "Exception" "Python raise")
  | some excJson =>
      let .ok nodeType := excJson.getObjValAs? String "node_type" | throwError
        s!"Raise node exception term is missing a 'node_type' field: {excJson}"
      match nodeType with
      | "Name" =>
          let excName ← exceptionNameFromTermJson excJson
          `($mkExcIdent $(Syntax.mkStrLit excName) "")
      | "Attribute" =>
          let excName ← exceptionNameFromTermJson excJson
          `($mkExcIdent $(Syntax.mkStrLit excName) "")
      | "Call" =>
          let .ok funcJson := excJson.getObjValAs? Json "func" | throwError
            s!"Raise call is missing a 'func' field: {excJson}"
          let excName ← exceptionNameFromTermJson funcJson
          let .ok argsJson := excJson.getObjValAs? (Array Json) "args" | throwError
            s!"Raise call is missing an 'args' field: {excJson}"
          match argsJson[0]? with
          | some firstArg =>
              let argTerm ← getCode firstArg `term
              let toStringIdent := mkIdent ``toString
              `($mkExcIdent $(Syntax.mkStrLit excName) ($toStringIdent $argTerm))
          | none =>
              `($mkExcIdent $(Syntax.mkStrLit excName) "")
      | _ =>
          let msgTerm ← getCode excJson `term
          `($mkExcIdent "Exception" (toString $msgTerm))

/-- Whether a statement may `return` a value on some path, scanning the statement and the
control-flow branches it owns (`If`/`For`/`While`/`With`/nested `Try`) but **not** descending into
nested `FunctionDef`/`Lambda` bodies (whose `return`s belong to the inner scope). Used to decide
whether a `try` body produces a non-`Unit` value that must be propagated out of the `try`. -/
partial def statementMayYieldValue (stmt : Json) : Bool :=
  match jsonNodeType? stmt with
  | some "Return" =>
      -- A bare `return` (no value) yields `Unit`; a `return <expr>` yields a value.
      match jsonFieldOption stmt "value" with
      | some _ => true
      | none => false
  | some "FunctionDef" => false
  | some "Lambda" => false
  | some _ =>
      match stmt with
      | .obj fields =>
          fields.toList.any fun (key, value) =>
            -- Only recurse into fields that hold owned sub-statements.
            if key == "body" || key == "orelse" || key == "finalbody"
                || key == "handlers" then
              match value with
              | .arr elems => elems.toList.any statementMayYieldValue
              | _ => statementMayYieldValue value
            else
              false
      | _ => false
  | none => false

/-- Whether any statement in `bodyElems` may `return` a value (see `statementMayYieldValue`). -/
def statementListMayYieldValue (bodyElems : Array Json) : Bool :=
  bodyElems.toList.any statementMayYieldValue

/-- Whether any `except` handler's body may `return` a value. If a handler returns a value, the
whole `try` expression has a non-`Unit` result type, so the `try` branch must also produce that
type (even when the try-body itself only raises). -/
def handlersListMayYieldValue (handlersElems : Array Json) : Bool :=
  handlersElems.toList.any fun handlerJson =>
    match handlerJson.getObjValAs? (Array Json) "body" with
    | .ok bodyElems => statementListMayYieldValue bodyElems
    | .error _ => false

/-- Build the guard deciding whether a caught exception should enter a given handler. -/
def handlerConditionTerm (caughtIdent : TSyntax `ident) (handlerType? : Option Json) : PygenM (TSyntax `term) := do
  match handlerType? with
  | none => pure trueTerm
  | some handlerTypeJson =>
      let caughtKind ← exceptionKindTerm caughtIdent
      let .ok nodeType := handlerTypeJson.getObjValAs? String "node_type" | throwError
        s!"ExceptHandler type is missing a 'node_type' field: {handlerTypeJson}"
      match nodeType with
      | "Tuple" =>
          let .ok eltsJson := handlerTypeJson.getObjValAs? (Array Json) "elts" | throwError
            s!"Tuple handler type is missing an 'elts' field: {handlerTypeJson}"
          let mut cond? : Option (TSyntax `term) := none
          for elt in eltsJson do
            let excName := (← exceptionNameFromTermJson elt)
            let altCond ←
              if excName == "Exception" then
                pure trueTerm
              else
                `($caughtKind == $(Syntax.mkStrLit excName))
            cond? ← match cond? with
              | none => pure (some altCond)
              | some prev => pure (some (← orTerm prev altCond))
          pure <| cond?.getD falseTerm
      | _ =>
          let excName ← exceptionNameFromTermJson handlerTypeJson
          if excName == "Exception" then
            pure trueTerm
          else
            `($caughtKind == $(Syntax.mkStrLit excName))

/-- Wrap every `(← e)` await in a run-mode try body with `PyExcept.captureIOErrors`, turning an IO
error (e.g. `EOFError` from `input()`) into a catchable `PyException`. Unlike wrapping the whole body
in `captureIOErrors (do …)`, this keeps each statement in the enclosing `do`, so a hoisted `let mut`
stays mutable (Lean forbids mutating an outer `let mut` from inside a nested `do`). -/
partial def wrapIOAwaitsWithCapture (stx : Syntax) : PygenM Syntax := do
  -- Heap run-mode awaits live in `PyHeapIO` (heap-call awaits raise `PyException`, `input()` awaits
  -- raise `IO.Error`), so use the `PyHeapIO`-typed capture there; plain run mode uses `PyExcept`.
  let captureName ←
    if (← getHeapMode) then pure ``PastaLean.PyHeapIO.captureIOErrors
    else pure ``PastaLean.PyExcept.captureIOErrors
  match stx with
  | .node _ ``Lean.Parser.Term.nestedAction args =>
      if args.size ≥ 1 then
        -- The awaited operand is a `doExpr` wrapping the term (post-#…: `← doElem`, not `← term`);
        -- unwrap to the term, recurse, wrap with `captureIOErrors`, then rebuild the `(← …)`.
        let operand := args[args.size - 1]!
        let termRaw :=
          if operand.getKind == ``Lean.Parser.Term.doExpr && operand.getArgs.size ≥ 1 then
            operand.getArgs[0]!
          else operand
        let inner ← wrapIOAwaitsWithCapture termRaw
        let innerT : TSyntax `term := ⟨inner⟩
        let captured ← `($(mkIdent captureName) $innerT)
        return (← `(← $captured:term)).raw
      else return stx
  | .node info k args => return .node info k (← args.mapM wrapIOAwaitsWithCapture)
  | _ => return stx

mutual

/-- Compile the `except` chain into nested handler tests over the caught exception value. -/
partial def exceptHandlersDoElemSyntax (caughtIdent : TSyntax `ident) (handlers : List Json) :
    PygenM (TSyntax `doElem) := do
  match handlers with
  | [] => throwExceptionDoElemSyntax caughtIdent
  | handlerJson :: restHandlers => do
      let handlerType? := jsonFieldOption handlerJson "type"
      let handlerName? := handlerJson.getObjValAs? String "name" |>.toOption
      let .ok bodyElemsJson := handlerJson.getObjValAs? (Array Json) "body" | throwError
        s!"ExceptHandler node is missing a 'body' field: {handlerJson}"
      let cond ← handlerConditionTerm caughtIdent handlerType?
      let mut bodyElems := #[]
      if let some handlerName := handlerName? then
        bodyElems := bodyElems.push (← `(doElem| let $(mkIdent handlerName.toName) := $caughtIdent))
      bodyElems := bodyElems ++ (← tryBranchBodySyntax bodyElemsJson)
      let nextHandler ← exceptHandlersDoElemSyntax caughtIdent restHandlers
      if bodyElems.isEmpty then
        let noop ← noopDoElemSyntax
        `(doElem| if $cond then
            $noop:doElem
          else
            $nextHandler:doElem)
      else
        -- Splice the handler statements straight into the `then` branch (a `doSeq`), no `do` wrapper.
        `(doElem| if $cond then
            $[$bodyElems:doElem]*
          else
            $nextHandler:doElem)

/-- Compile a try-body / catch-body sequence, lowering nested `Try` nodes to inner
`PyExcept` terms so only genuinely nested tries introduce nested exception wrappers. -/
partial def tryBranchBodySyntax (bodyElems : Array Json) : PygenM (Array (TSyntax `doElem)) := do
  let mut bodyStxArray := #[]
  for elem in bodyElems do
    let elemStx ←
      -- A value-returning nested `try` becomes an inner PyExcept term (it yields a value); a
      -- non-returning one is spliced inline via its `doElem` form, so a `let mut` assigned inside it
      -- and used later in the enclosing body stays mutable (a nested `do` term would freeze it).
      if jsonNodeType? elem == some "Try" && statementDefinitelyReturns elem then
        let nestedTry ← tryExceptTerm elem
        `(doElem| $nestedTry:term)
      else
        withoutCheck do
          getCode elem `doElem
    bodyStxArray := appendDoElems bodyStxArray elemStx
    if statementDefinitelyReturns elem then
      break
  return bodyStxArray

/-- Lower a Python `try` block to an inner `PyExcept` term so it can be reused in both
statement position and nested-expression-like contexts. -/
partial def tryExceptTerm (json : Json) : PygenM (TSyntax `term) := do
  let .ok bodyElems := json.getObjValAs? (Array Json) "body" | throwError
    s!"Try node does not have a 'body' field or it is not a JSON array: {json}"
  let .ok handlersElems := json.getObjValAs? (Array Json) "handlers" | throwError
    s!"Try node does not have a 'handlers' field or it is not a JSON array: {json}"
  let .ok orelseElems := json.getObjValAs? (Array Json) "orelse" | throwError
    s!"Try node does not have an 'orelse' field or it is not a JSON array: {json}"
  let .ok finalbodyElems := json.getObjValAs? (Array Json) "finalbody" | throwError
    s!"Try node does not have a 'finalbody' field or it is not a JSON array: {json}"
  let bodyAndElse ← tryBranchBodySyntax (bodyElems ++ orelseElems)
  let noopElem ← noopDoElemSyntax
  let innerBodyElems := if bodyAndElse.isEmpty then #[noopElem] else bodyAndElse
  let catchIdent := mkIdent `caught
  let catchBody ← exceptHandlersDoElemSyntax catchIdent handlersElems.toList
  -- The try-branch statements. By default we splice them straight into `try` so a `let mut` in the
  -- body mutates the *enclosing* scope (wrapping them in a nested `do`, as `captureIOErrors (do …)`
  -- does, makes those vars read-only and breaks the mutation). The wrapper is only needed when the
  -- body performs IO — there an IO error (e.g. `EOFError` from `input()` at end of input) must be
  -- turned into a catchable `PyException`; that case keeps the wrapper (and binds/returns the value).
  let needsIO := bodyNeedsIOMonad (bodyElems ++ orelseElems)
  -- Pin the exception monad based on mode and effects.
  -- Proof mode (exact + IO/exceptions) uses PyProofM (state monad with Python exceptions).
  -- Exact mode without proof uses PyExceptId (pure exceptions, no IO).
  -- Run mode uses PyExcept (IO + exceptions).
  let useProofMonad ← shouldUseProofMonad
  let usePureExcept := !useProofMonad && (← getNumericMode) == .exact && !needsIO
  let exceptIdent ←
    if useProofMonad then
      pure (mkIdent ``PastaLean.ProofMode.PyProofM)
    else if usePureExcept then
      pure (mkIdent ``PastaLean.PyExceptId)
    else
      pure (mkIdent ``PastaLean.PyExcept)
  let bodyYieldsValue :=
    statementListMayYieldValue (bodyElems ++ orelseElems)
      || handlersListMayYieldValue handlersElems
  let _ := bodyYieldsValue
  let tryBranchElems : Array (TSyntax `doElem) ←
    if needsIO && !useProofMonad then do
      -- Run mode with IO: wrap each `(← io)` await with captureIOErrors and splice the body
      -- directly, so IO errors are catchable AND a hoisted `let mut` stays mutable.
      innerBodyElems.mapM (fun e => do return ⟨← wrapIOAwaitsWithCapture e.raw⟩)
    else
      -- Proof mode (pyInputProof self-converts IO errors) or no IO: splice directly.
      pure innerBodyElems
  if finalbodyElems.isEmpty then
    `(((do
          try
            $[$tryBranchElems:doElem]*
          catch $catchIdent =>
            $catchBody:doElem) : $exceptIdent _))
  else
    let finalElems ← tryBranchBodySyntax finalbodyElems
    let finalBlock ← sequenceDoElems finalElems (← noopDoElemSyntax)
    `(((do
          try
            $[$tryBranchElems:doElem]*
          catch $catchIdent =>
            $catchBody:doElem
          finally
            $finalBlock:doElem) : $exceptIdent _))

end

@[pygen "Raise"]
def raiseSyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
    | `doElem, json => do
        let excJson? := jsonFieldOption json "exc"
        let excTerm ← exceptionValueTerm excJson?
        throwExceptionDoElemSyntax excTerm
    | _, _ => throwError s!"Unsupported syntax category for Raise node"

@[pygen "Try"]
def trySyntax : (kind : SyntaxNodeKind) → Json →
    PygenM (TSyntax kind)
    | `term, json => do
        tryExceptTerm json
    | `doElem, json => do
        let .ok bodyElems := json.getObjValAs? (Array Json) "body" | throwError
          s!"Try node does not have a 'body' field or it is not a JSON array: {json}"
        let .ok handlersElems := json.getObjValAs? (Array Json) "handlers" | throwError
          s!"Try node does not have a 'handlers' field or it is not a JSON array: {json}"
        let .ok orelseElems := json.getObjValAs? (Array Json) "orelse" | throwError
          s!"Try node does not have an 'orelse' field or it is not a JSON array: {json}"
        let .ok finalbodyElems := json.getObjValAs? (Array Json) "finalbody" | throwError
          s!"Try node does not have a 'finalbody' field or it is not a JSON array: {json}"
        -- Hoist names assigned across `try`/`except`/`finally` that are used after the block into
        -- one enclosing `let mut … := default` (mirrors the `if` hoist in `ControlFlow.lean`), so a
        -- variable set in the body and reassigned in a handler binds a single outer mutable.
        let assignedNames := (json.getObjValAs? (Array String) "try_assigned_names").toOption.getD #[]
        let mut hoistDecls : Array (TSyntax `doElem) := #[]
        for nm in assignedNames do
          unless (← hasVar nm.toName) do
            let tyStx? ← match (jsonFieldOption json "try_assigned_types").bind
                (·.getObjVal? nm |>.toOption) with
              | some ann => stampedTypeSyntax? (Json.mkObj [("_ty", ann)])
              | none => pure none
            let decl ← match tyStx? with
              | some tyStx => `(doElem| let mut $(mkIdent nm.toName):ident : $tyStx := default)
              | none => `(doElem| let mut $(mkIdent nm.toName):ident := default)
            hoistDecls := hoistDecls.push decl
            addVar nm.toName
            setMutVar nm.toName
        let bodyAndElse ← tryBranchBodySyntax (bodyElems ++ orelseElems)
        -- Splice body statements straight into `captureIOErrors (do …)` (no nested `do (do …)`).
        let noopElem ← noopDoElemSyntax
        let innerBodyElems := if bodyAndElse.isEmpty then #[noopElem] else bodyAndElse
        let catchIdent := mkIdent `caught
        let catchBody ← exceptHandlersDoElemSyntax catchIdent handlersElems.toList
        -- Splice the body straight into `try` so a `let mut` in it mutates the enclosing scope.
        -- In proof mode, no captureIOErrors wrapper is needed (pyInputProof already converts IOError).
        -- In run mode with IO, wrap with captureIOErrors to convert IO.Error to PyException.
        let needsIO := bodyNeedsIOMonad (bodyElems ++ orelseElems)
        let useProofMonad ← shouldUseProofMonad
        let bodyYieldsValue :=
          statementListMayYieldValue (bodyElems ++ orelseElems)
            || handlersListMayYieldValue handlersElems
        let _ := bodyYieldsValue
        let tryBranchElems : Array (TSyntax `doElem) ←
          if needsIO && !useProofMonad then do
            -- Run mode with IO: wrap each `(← io)` await with captureIOErrors and splice directly,
            -- so IO errors are catchable AND a hoisted `let mut` stays mutable.
            innerBodyElems.mapM (fun e => do return ⟨← wrapIOAwaitsWithCapture e.raw⟩)
          else
            -- Proof mode (pyInputProof self-converts IO errors) or no IO: splice directly.
            pure innerBodyElems
        let tryStx ←
          if finalbodyElems.isEmpty then
            `(doElem| try
                $[$tryBranchElems:doElem]*
              catch $catchIdent =>
                $catchBody:doElem)
          else
            let finalElems ← tryBranchBodySyntax finalbodyElems
            let finalBlock ← sequenceDoElems finalElems (← noopDoElemSyntax)
            `(doElem| try
                $[$tryBranchElems:doElem]*
              catch $catchIdent =>
                $catchBody:doElem
              finally
                $finalBlock:doElem)
        if hoistDecls.isEmpty then
          pure tryStx
        else
          pure ⟨mkNullNode ((hoistDecls.push tryStx).map TSyntax.raw)⟩
    | `command, _ => do
        return ⟨mkNullNode #[]⟩
    | _, _ => throwError s!"Unsupported syntax category for Try node"

end PastaLean

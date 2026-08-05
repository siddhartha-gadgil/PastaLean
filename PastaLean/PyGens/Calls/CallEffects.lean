import Mathlib
import PastaLean.Codegen
import PastaLean.PyGens.Basic
import PastaLean.PyGens.Attributes
import PastaLean.PyGens.Core.Subscript
import PastaLean.PyGens.Core.Utils

open Lean Meta Elab Term Qq Std

namespace PastaLean

/-- Build the `List PyPrintArg` term for a `print(...)` call's arguments.

Each ordinary argument becomes `pyPrintArg arg`; the common case (no `*iterable` spread) is a
single list literal `[pyPrintArg a, pyPrintArg b, …]`, which reads far better than a chain of
`++`-joined singletons. A `*iterable` (`Starred`) argument is spread with `List.map pyPrintArg`,
and only then are the pieces concatenated.

`pyPrintArg` applies `pyStringify` eagerly rather than relying on the `CoeOut` into a `List PyPrintArg`
literal: the coercion would push the expected element type `PyPrintArg` into each argument, which
breaks polymorphic argument terms such as `pyListGetItem a i` (the element type unifies with
`PyPrintArg`, then demands `Inhabited PyPrintArg`). Letting each argument elaborate at its natural
type first gives identical results for fixed-type arguments. -/
def buildPrintArgsList (argsArray : Array Json) (resolvedArgs : Array (TSyntax `term)) :
    PygenM (TSyntax `term) := do
  -- Emit the print helpers as bare names; every generated file `open`s `PastaLean`, so
  -- `pyPrintArg`/`pyPrintIO` resolve without the noisy `PastaLean.` prefix.
  let argIdent := mkIdent `pyPrintArg
  let isStarred (i : Nat) : Bool :=
    match argsArray[i]? with
    | some argJson => argJson.getObjValAs? String "node_type" == .ok "Starred"
    | none => false
  -- Under `--heap`, a printed container is held by reference; dereference it (recursively through
  -- tuple/list literals) so `print(xs)`/`print((xs, ys))` show contents, not `Ref` addresses. A
  -- `*iterable` spread keeps its resolved term. `none` in value mode → `resolvedArgs` unchanged.
  let mut resolvedArgs := resolvedArgs
  for i in [0:resolvedArgs.size] do
    unless isStarred i do
      if let some argJson := argsArray[i]? then
        if let some deref ← heapValueDeref? argJson then
          resolvedArgs := resolvedArgs.set! i deref
  -- Common case: no spread → one clean `[pyArg a, pyArg b, …]` literal.
  if (List.range resolvedArgs.size).all (fun i => !isStarred i) then
    match resolvedArgs.toList with
    | [] => `(([] : List PastaLean.PyPrintArg))
    | _ =>
        let elems ← resolvedArgs.mapM (fun code => `($argIdent $code))
        `([$elems,*])
  else
    -- A `*iterable` is present: build each part as a `List PyPrintArg` and concatenate.
    let mut parts : Array (TSyntax `term) := #[]
    for i in [0:resolvedArgs.size] do
      let code := resolvedArgs[i]!
      if isStarred i then
        parts := parts.push (← `(List.map $argIdent $code))
      else
        parts := parts.push (← `([$argIdent $code]))
    match parts.toList with
    | [] => `(([] : List PastaLean.PyPrintArg))
    | first :: rest =>
        let mut acc := first
        for p in rest do
          acc ← `($acc ++ $p)
        pure acc

/-- Local copy of the exception-effect probe so call lowering can avoid cyclic imports. -/
partial def basicJsonUsesExceptionEffect (json : Json) : Bool :=
  let directMatches :=
    match json.getObjValAs? String "effect_mode" with
    | .ok "except" => true
    | _ =>
        match json.getObjValAs? String "node_type" with
        | .ok nodeType => nodeType == "Try" || nodeType == "Raise"
        | .error _ => false
  if directMatches then
    true
  else
    match json with
    | .arr elems => elems.toList.any basicJsonUsesExceptionEffect
    | .obj fields => fields.toList.any (fun (_, value) => basicJsonUsesExceptionEffect value)
    | _ => false

/-- Local copy of the IO-effect probe so calls can lift nested `input(...)` / `print(...)`. -/
partial def basicJsonUsesIOEffect (json : Json) : Bool :=
  let directMatches :=
    match json.getObjValAs? String "effect_mode" with
    | .ok "io" => true
    | _ => false
  if directMatches then
    true
  else
    match json with
    | .arr elems => elems.toList.any basicJsonUsesIOEffect
    | .obj fields => fields.toList.any (fun (_, value) => basicJsonUsesIOEffect value)
    | _ => false

/-- Detect whether a JSON subtree contains any translated monadic effect. -/
def basicJsonUsesMonadicEffect (json : Json) : Bool :=
  basicJsonUsesExceptionEffect json || basicJsonUsesIOEffect json

/--
Inline simple translated `IO` expressions directly as terms that contain local `←` binds.

This is used in surrounding `do` notation so code like `b = int(input())` can become
`let mut b := PastaLean.pyInt (← PastaLean.pyInputIO "")` instead of an extra nested
`do ... : IO _` wrapper.
-/
partial def inlineIOTerm (json : Json) : PygenM (TSyntax `term) := do
  if !basicJsonUsesIOEffect json then
    return ← getCode json `term
  let some nodeType := json.getObjValAs? String "node_type" |>.toOption
    | return ← getCode json `term
  match nodeType with
  | "Call" =>
      let .ok funcJson := json.getObjValAs? Json "func" | throwError
        s!"Call node does not have a 'func' field or it is not a JSON value: {json}"
      let .ok argsJson := json.getObjValAs? Json "args" | throwError
        s!"Call node does not have an 'args' field or it is not a JSON value: {json}"
      let argsArray ← match argsJson with
        | .arr arr => pure arr
        | _ => throwError s!"Call node 'args' field is not an array: {argsJson}"
      let .ok keyWordsJson := json.getObjVal? "keywords" | throwError
        s!"Call node does not have a 'keywords' field or it is not json pairs: {json}"
      let .ok keyWordsMap := keyWordsJson.getObj? | throwError
        s!"Call node 'keywords' field is not a JSON object: {keyWordsJson}"
      match funcJson.getObjValAs? String "node_type", funcJson.getObjValAs? String "id" with
      | .ok "Name", .ok "input" => do
          unless keyWordsMap.isEmpty do
            throwError "input() keyword arguments are not supported yet."
          unless argsArray.size ≤ 1 do
            throwError "input() expects zero or one positional argument."
          -- Choose between proof mode (PyProofM) and run mode (IO) input
          let inputIdent ← if (← shouldUseProofMonad) then
              pure (mkIdent ``PastaLean.ProofMode.pyInputProof)
            else
              pure (mkIdent ``pyInputIO)
          match argsArray.size with
          | 0 => `((← ($inputIdent "")))
          | 1 =>
              let arg0 ← inlineIOTerm argsArray[0]!
              `((← ($inputIdent $arg0)))
          | _ => throwError "input() expects zero or one positional argument."
      | .ok "Name", .ok "int" => do
          unless keyWordsMap.isEmpty do
            throwError "int() keyword arguments are not supported yet."
          unless argsArray.size == 1 || argsArray.size == 2 do
            throwError "int() expects one or two positional arguments."
          let arg0 ← inlineIOTerm argsArray[0]!
          if argsArray.size == 2 then
            `($(mkIdent ``pyIntBase) $arg0 $(← inlineIOTerm argsArray[1]!))
          else
            `($(mkIdent ``pyInt) $arg0)
      | _, _ =>
          let mut inlineArgs : Array (TSyntax `term) := #[]
          for argJson in argsArray do
            if basicJsonUsesIOEffect argJson then
              inlineArgs := inlineArgs.push (← inlineIOTerm argJson)
            else
              match argJson.getObjValAs? String "node_type", argJson.getObjValAs? String "id" with
              | .ok "Name", .ok funcName =>
                  match ← builtinMappedName? funcName with
                  | some mappedName =>
                      inlineArgs := inlineArgs.push ((mkIdent mappedName : TSyntax `term))
                  | none =>
                      let mappedName ← leanName funcName.toName
                      inlineArgs := inlineArgs.push ((mkIdent mappedName : TSyntax `term))
              | _, _ =>
                  inlineArgs := inlineArgs.push (← getCode argJson `term)
          let heap ← getHeapMode
          let mut funcTerm : TSyntax `term ← `("")
          -- Under `--heap`, a ctor/method/heap-fn call must keep its heap dispatch (`C.new` /
          -- `C.m recv` / awaited) even though an argument carries IO — otherwise the generic lowering
          -- below would emit the raw class/function name (`Box (…)` instead of `(← Box.new …)`).
          let mut heapAwait := false
          if funcJson.getObjValAs? String "node_type" == .ok "Attribute" then
            let .ok valueJson := funcJson.getObjValAs? Json "value" | throwError
              s!"Attribute node missing 'value' field: {funcJson}"
            let .ok attr := funcJson.getObjValAs? String "attr" | throwError
              s!"Attribute node missing 'attr' field: {funcJson}"
            let receiverTerm ←
              if basicJsonUsesIOEffect valueJson then
                inlineIOTerm valueJson
              else
                getCode valueJson `term
            match (if heap then (json.getObjValAs? String "_receiver_class").toOption else none) with
            | some cls =>
                -- Heap method call `recv.m(args)` → `(← C.m recv args)`.
                funcTerm := mkIdent (Name.mkStr (← suffixIfUserName cls).toName attr)
                inlineArgs := #[receiverTerm] ++ inlineArgs
                heapAwait := true
            | none =>
              match pythonMethodMap attr with
              | some funcName =>
                  -- Apply the mapped runtime function to the receiver as its *first* argument,
                  -- flat with the call arguments, rather than pre-building `(f receiver)`. The
                  -- latter is a complete sub-application, so a runtime method with a default
                  -- argument (e.g. `pyStringSplit`'s `sep`) would fill the default and then the
                  -- explicit argument (`s.split(" ")`) would be applied to the *result*.
                  funcTerm := (mkIdent funcName : TSyntax `term)
                  inlineArgs := #[receiverTerm] ++ inlineArgs
              | none =>
                  let attrId := mkIdent attr.toName
                  funcTerm ← `($receiverTerm.$attrId)
          else
            match funcJson.getObjValAs? String "node_type", funcJson.getObjValAs? String "id" with
            | .ok "Name", .ok funcName =>
                match (if heap then (json.getObjValAs? String "_class_ctor").toOption else none) with
                | some cls =>
                    -- Heap constructor `C(args)` → `(← C.new args)`.
                    funcTerm := mkIdent (Name.mkStr (← suffixIfUserName cls).toName "new")
                    heapAwait := true
                | none =>
                    match ← builtinMappedName? funcName with
                    | some mappedName => funcTerm := (mkIdent mappedName : TSyntax `term)
                    | none =>
                        let mappedName ← leanName funcName.toName
                        funcTerm := (mkIdent mappedName : TSyntax `term)
                    -- A heap-effectful user free function returns a `HeapM` action; await it inline.
                    if heap && json.getObjValAs? Bool "_heap_call" == .ok true then
                      heapAwait := true
            | _, _ =>
                funcTerm ← getCode funcJson `term
          let mut t ← `($funcTerm $inlineArgs*)
          for (kwName, kwValueJson) in keyWordsMap.toList do
            let kwValueCode ←
              if basicJsonUsesIOEffect kwValueJson then
                inlineIOTerm kwValueJson
              else
                getCode kwValueJson `term
            let kwId := mkIdent kwName.toName
            t ← `($t ($kwId:ident := $kwValueCode))
          if heapAwait then return ← `((← $t:term)) else return t
  | "FormattedValue" => do
      let .ok valueJson := json.getObjValAs? Json "value" | throwError
        s!"FormattedValue node does not have a 'value' field or it is not a JSON value: {json}"
      let valueCode ← inlineIOTerm valueJson
      let toStringIdent := mkIdent ``toString
      `($toStringIdent $valueCode)
  | "JoinedStr" => do
      let .ok valuesJson := json.getObjValAs? Json "values" | throwError
        s!"JoinedStr node does not have a 'values' field or it is not a JSON value: {json}"
      let valuesArray ← match valuesJson with
        | .arr arr => pure arr
        | _ => throwError s!"JoinedStr node 'values' field is not an array: {valuesJson}"
      let appendIdent := mkIdent ``String.append
      let mut res : TSyntax `term ← `("")
      for valueJson in valuesArray do
        let valueCode ← inlineIOTerm valueJson
        res ← `($appendIdent $res $valueCode)
      pure res
  | "BinOp" => do
      -- Recurse into both operands so an IO subexpression (e.g. `int(input()) + 5`) becomes an
      -- inline `(← …)` await in a pure arithmetic position rather than an un-awaited `IO _`.
      let .ok op := json.getObjValAs? String "op" | throwError s!"BinOp node missing 'op': {json}"
      let .ok leftJson := json.getObjValAs? Json "left" | throwError s!"BinOp node missing 'left': {json}"
      let .ok rightJson := json.getObjValAs? Json "right" | throwError s!"BinOp node missing 'right': {json}"
      let leftCode ← inlineIOTerm leftJson
      let rightCode ← inlineIOTerm rightJson
      binOpApplyTerm op leftCode rightCode
  | "UnaryOp" => do
      let .ok op := json.getObjValAs? String "op" | throwError s!"UnaryOp node missing 'op': {json}"
      let .ok operandJson := json.getObjValAs? Json "operand" | throwError s!"UnaryOp node missing 'operand': {json}"
      let operandCode ← inlineIOTerm operandJson
      unaryOpApplyTerm op operandCode
  | "Compare" => do
      let .ok op := json.getObjValAs? String "op" | throwError s!"Compare node missing 'op': {json}"
      let .ok leftJson := json.getObjValAs? Json "left" | throwError s!"Compare node missing 'left': {json}"
      let .ok rightJson := json.getObjValAs? Json "right" | throwError s!"Compare node missing 'right': {json}"
      let leftCode ← inlineIOTerm leftJson
      let rightCode ← inlineIOTerm rightJson
      compareApplyTerm op leftJson leftCode rightCode (rightJson := some rightJson)
  | "BoolOp" => do
      let .ok op := json.getObjValAs? String "op" | throwError s!"BoolOp node missing 'op': {json}"
      let .ok valuesJson := json.getObjValAs? Json "values" | throwError s!"BoolOp node missing 'values': {json}"
      let valuesArray ← match valuesJson with
        | .arr arr => arr.mapM inlineIOTerm
        | _ => throwError s!"BoolOp node 'values' field is not an array: {valuesJson}"
      if valuesArray.isEmpty then throwError s!"BoolOp node 'values' array is empty: {valuesJson}"
      match op with
      | "and" => valuesArray.foldlM (fun a b => `($a && $b)) valuesArray[0]! (start := 1)
      | "or" => valuesArray.foldlM (fun a b => `($a || $b)) valuesArray[0]! (start := 1)
      | _ => throwError s!"Unsupported boolean operator: {op}"
  | "ListComp" => do
      -- A comprehension whose element is itself effectful (e.g. `[int(input()) for _ in …]`)
      -- lowers to `List.mapM …`, an `IO (List _)` action. Await it inline so the surrounding
      -- pure position sees the resulting `List _`. When only the *iterable* is IO the element
      -- stays pure (`List.map`), so the comprehension is already a `List _` — do not await.
      let compTerm ← getCode json `term
      match json.getObjValAs? Json "elt" with
      | .ok eltJson =>
          if basicJsonUsesIOEffect eltJson then `((← $compTerm:term)) else pure compTerm
      | _ => pure compTerm
  | "Subscript" => do
      -- `foo()[i]` where `foo()` is `IO _`: inline the awaited container into the index
      -- position so the subscript runs on the value, not on a raw `IO _`.
      let .ok valueJson := json.getObjValAs? Json "value" | throwError
        s!"Subscript node does not have a 'value' field: {json}"
      let .ok sliceJson := json.getObjValAs? Json "slice" | throwError
        s!"Subscript node does not have a 'slice' field: {json}"
      let valueCode ← inlineIOTerm valueJson
      subscriptTermFromValue valueJson sliceJson valueCode
  | _ =>
      return ← getCode json `term

/--
Hoist translated `IO` subexpressions into surrounding `do` blocks and return a pure term
that refers to the bound result.
-/
partial def hoistIOTerm (json : Json) : PygenM (Array (TSyntax `doElem) × TSyntax `term) := do
  if !basicJsonUsesIOEffect json then
    return (#[], ← getCode json `term)
  let some nodeType := json.getObjValAs? String "node_type" |>.toOption
    | return (#[], ← getCode json `term)
  match nodeType with
  | "Call" =>
      let .ok funcJson := json.getObjValAs? Json "func" | throwError
        s!"Call node does not have a 'func' field or it is not a JSON value: {json}"
      let .ok argsJson := json.getObjValAs? Json "args" | throwError
        s!"Call node does not have an 'args' field or it is not a JSON value: {json}"
      let argsArray ← match argsJson with
        | .arr arr => pure arr
        | _ => throwError s!"Call node 'args' field is not an array: {argsJson}"
      let .ok keyWordsJson := json.getObjVal? "keywords" | throwError
        s!"Call node does not have a 'keywords' field or it is not json pairs: {json}"
      let .ok keyWordsMap := keyWordsJson.getObj? | throwError
        s!"Call node 'keywords' field is not a JSON object: {keyWordsJson}"
      match funcJson.getObjValAs? String "node_type", funcJson.getObjValAs? String "id" with
      | .ok "Name", .ok "input" => do
          unless keyWordsMap.isEmpty do
            throwError "input() keyword arguments are not supported yet."
          let mut bindings : Array (TSyntax `doElem) := #[]
          let mut resolvedArgs : Array (TSyntax `term) := #[]
          for argJson in argsArray do
            if basicJsonUsesIOEffect argJson then
              let (argBindings, argTerm) ← hoistIOTerm argJson
              bindings := bindings ++ argBindings
              resolvedArgs := resolvedArgs.push argTerm
            else
              resolvedArgs := resolvedArgs.push (← getCode argJson `term)
          -- Choose between proof mode (PyProofM) and run mode (IO) input
          let inputIdent ← if (← shouldUseProofMonad) then
              pure (mkIdent ``PastaLean.ProofMode.pyInputProof)
            else
              pure (mkIdent ``pyInputIO)
          let action ← match resolvedArgs.size with
            | 0 => `($inputIdent "")
            | 1 =>
                let arg0 := resolvedArgs[0]!
                `($inputIdent $arg0)
            | _ => throwError "input() expects zero or one positional argument."
          let binder := mkIdent (s!"__py_input{bindings.size}").toName
          let finalBindings := bindings.push (← `(doElem| let $binder:ident ← $action:term))
          return (finalBindings, binder)
      | .ok "Name", .ok "int" => do
          unless keyWordsMap.isEmpty do
            throwError "int() keyword arguments are not supported yet."
          unless argsArray.size == 1 || argsArray.size == 2 do
            throwError "int() expects one or two positional arguments."
          let mut bindings : Array (TSyntax `doElem) := #[]
          let mut resolvedArgs : Array (TSyntax `term) := #[]
          for argJson in argsArray do
            if basicJsonUsesIOEffect argJson then
              let (argBindings, argTerm) ← hoistIOTerm argJson
              bindings := bindings ++ argBindings
              resolvedArgs := resolvedArgs.push argTerm
            else
              resolvedArgs := resolvedArgs.push (← getCode argJson `term)
          if resolvedArgs.size == 2 then
            return (bindings, ← `($(mkIdent ``pyIntBase) $(resolvedArgs[0]!) $(resolvedArgs[1]!)))
          else
            return (bindings, ← `($(mkIdent ``pyInt) $(resolvedArgs[0]!)))
      | .ok "Name", .ok "print" => do
          -- In `prove` (exact) mode `print` is a no-op (the prove version is for theorems, not
          -- output), but we keep the full rendered line — `pyPrintNoop` takes the same args as
          -- `pyPrintIO` and discards them. Only the function name differs by mode; IO-effect args
          -- (`input()`) are hoisted and run in both.
          let supportedKeywords := ["sep", "end"]
          for (kwName, _) in keyWordsMap.toList do
            unless supportedKeywords.contains kwName do
              throwError s!"print() keyword argument '{kwName}' is not supported yet."
          let mut bindings : Array (TSyntax `doElem) := #[]
          let mut resolvedArgs : Array (TSyntax `term) := #[]
          for argJson in argsArray do
            if basicJsonUsesIOEffect argJson then
              let (argBindings, argTerm) ← hoistIOTerm argJson
              bindings := bindings ++ argBindings
              resolvedArgs := resolvedArgs.push argTerm
            else
              resolvedArgs := resolvedArgs.push (← getCode argJson `term)
          let pyPrintIOIdent := mkIdent (if (← getNumericMode) == .exact then `pyPrintNoop else `pyPrintIO)
          let printArgs ← buildPrintArgsList argsArray resolvedArgs
          let action ← match keyWordsMap.get? "sep", keyWordsMap.get? "end" with
            | none, none =>
                `($pyPrintIOIdent $printArgs)
            | _, _ =>
                let sepCode ← match keyWordsMap.get? "sep" with
                  | some sepJson => getCode sepJson `term
                  | none => `(" ")
                let endCode ← match keyWordsMap.get? "end" with
                  | some endJson => getCode endJson `term
                  | none => `("\n")
                `($pyPrintIOIdent $printArgs $sepCode $endCode)
          let binder := mkIdent (s!"__py_print{bindings.size}").toName
          let finalBindings := bindings.push (← `(doElem| let $binder:ident ← $action:term))
          return (finalBindings, binder)
      | _, _ =>
          return (#[], ← getCode json `term)
  | "FormattedValue" => do
      let .ok valueJson := json.getObjValAs? Json "value" | throwError
        s!"FormattedValue node does not have a 'value' field or it is not a JSON value: {json}"
      let (bindings, valueTerm) ← hoistIOTerm valueJson
      let toStringIdent := mkIdent ``toString
      return (bindings, ← `($toStringIdent $valueTerm))
  | "JoinedStr" => do
      let .ok valuesJson := json.getObjValAs? Json "values" | throwError
        s!"JoinedStr node does not have a 'values' field or it is not a JSON value: {json}"
      let valuesArray ← match valuesJson with
        | .arr arr => pure arr
        | _ => throwError s!"JoinedStr node 'values' field is not an array: {valuesJson}"
      let appendIdent := mkIdent ``String.append
      let mut bindings : Array (TSyntax `doElem) := #[]
      let mut res : TSyntax `term ← `("")
      for valueJson in valuesArray do
        let (pieceBindings, pieceTerm) ← hoistIOTerm valueJson
        bindings := bindings ++ pieceBindings
        res ← `($appendIdent $res $pieceTerm)
      return (bindings, res)
  | "Subscript" => do
      -- `foo()[i]` in an argument position: hoist the IO container to a binding, then index the
      -- bound value (`int(input()[0])` → `let s ← input; pyInt (pyGetItem s 0)`).
      let .ok valueJson := json.getObjValAs? Json "value" | throwError
        s!"Subscript node does not have a 'value' field: {json}"
      let .ok sliceJson := json.getObjValAs? Json "slice" | throwError
        s!"Subscript node does not have a 'slice' field: {json}"
      let (valueBindings, valueTerm) ← hoistIOTerm valueJson
      let term ← subscriptTermFromValue valueJson sliceJson valueTerm
      return (valueBindings, term)
  | _ =>
      return (#[], ← getCode json `term)

/-- Lift a pure function application into `IO` when any argument is already monadic. -/
def buildIOPureApplicationFromArgs (argJsons : Array Json) (argCodes : Array (TSyntax `term))
    (mkResult : Array (TSyntax `term) → PygenM (TSyntax `term)) : PygenM (TSyntax `term) := do
  let mut bindings : Array (TSyntax `doElem) := #[]
  let mut resolvedArgs : Array (TSyntax `term) := #[]
  for idx in [0:argCodes.size] do
    let argJson := argJsons[idx]!
    let argCode := argCodes[idx]!
    if basicJsonUsesIOEffect argJson then
      let (argBindings, argTerm) ← hoistIOTerm argJson
      if argBindings.isEmpty then
        let binder := mkIdent (s!"__py_arg{idx}").toName
        bindings := bindings.push (← `(doElem| let $binder:ident ← $argTerm:term))
        resolvedArgs := resolvedArgs.push (binder : TSyntax `term)
      else
        bindings := bindings ++ argBindings
        resolvedArgs := resolvedArgs.push argTerm
    else if basicJsonUsesMonadicEffect argJson then
      let binder := mkIdent (s!"__py_arg{idx}").toName
      bindings := bindings.push (← `(doElem| let $binder:ident ← $argCode:term))
      resolvedArgs := resolvedArgs.push (binder : TSyntax `term)
    else
      resolvedArgs := resolvedArgs.push argCode
  let resultTerm ← mkResult resolvedArgs
  if bindings.isEmpty then
    return resultTerm
  -- Choose monad type: PyProofM in proof mode, IO in run mode
  let monadType ← if (← shouldUseProofMonad) then
      `(PastaLean.ProofMode.PyProofM)
    else
      `(IO)
  `(((do
        $[$bindings:doElem]*
        return $resultTerm:term) : $monadType _))

/-- Lift an `IO`-returning application when some arguments are already monadic. -/
def buildIOActionApplicationFromArgs (argJsons : Array Json) (argCodes : Array (TSyntax `term))
    (mkAction : Array (TSyntax `term) → PygenM (TSyntax `term)) : PygenM (TSyntax `term) := do
  let mut bindings : Array (TSyntax `doElem) := #[]
  let mut resolvedArgs : Array (TSyntax `term) := #[]
  for idx in [0:argCodes.size] do
    let argJson := argJsons[idx]!
    let argCode := argCodes[idx]!
    if basicJsonUsesIOEffect argJson then
      let (argBindings, argTerm) ← hoistIOTerm argJson
      if argBindings.isEmpty then
        let binder := mkIdent (s!"__py_arg{idx}").toName
        bindings := bindings.push (← `(doElem| let $binder:ident ← $argTerm:term))
        resolvedArgs := resolvedArgs.push (binder : TSyntax `term)
      else
        bindings := bindings ++ argBindings
        resolvedArgs := resolvedArgs.push argTerm
    else if basicJsonUsesMonadicEffect argJson then
      let binder := mkIdent (s!"__py_arg{idx}").toName
      bindings := bindings.push (← `(doElem| let $binder:ident ← $argCode:term))
      resolvedArgs := resolvedArgs.push (binder : TSyntax `term)
    else
      resolvedArgs := resolvedArgs.push argCode
  let actionTerm ← mkAction resolvedArgs
  if bindings.isEmpty then
    return actionTerm
  -- Choose monad type: PyProofM in proof mode, IO in run mode
  let monadType ← if (← shouldUseProofMonad) then
      `(PastaLean.ProofMode.PyProofM)
    else
      `(IO)
  `(((do
        $[$bindings:doElem]*
        let __py_result ← $actionTerm:term
        return __py_result) : $monadType _))

end PastaLean

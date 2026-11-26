import PastaLean.PyGens.Core.Utils
import PastaLean.PyVerify.AssertTactic
import Std.Tactic.Do

set_option linter.unusedVariables false

/-!
# PASSTA contract codege

Detection and theorem-building for the `Libraries.passta` contract markers (`Requires`/`Ensures`/ `Assert`/`Assume`/`Invariant`/`Decreases`).
-/

open Lean Meta Elab Term Qq Std
open Lean.Parser.Term
open Std.Do

namespace PastaLean

/-- `contractArg?` extracts contract metadata from a Python AST node. Verifies the function is from the "passta" library. Extracts the contract type (library member:
"Requires" /"Ensures" /"Assert" /"Assume" /"Invariant"/"Decreases") and Returns the contract type paired with its argument, or none if it's not a contract statement -/
def contractArg? (stmt : Json) : Option (String × Json) :=
  match jsonNodeType? stmt with
  | some "Expr" =>
    match (stmt.getObjVal? "value").toOption with
    | some value =>
      match jsonNodeType? value, (value.getObjVal? "func").toOption with
      | some "Call", some func =>
        match func.getObjValAs? String "library_module", func.getObjValAs? String "library_member",
              (value.getObjValAs? (Array Json) "args").toOption with
        | .ok "passta", .ok member, some args =>
          match args[0]? with
          | some arg => some (member, arg)
          | none => none
        | _, _, _ => none
      | _, _ => none
    | none => none
  | _ => none

/-- A JSON `Name` node with the given identifier. -/
def nameJson (id : String) : Json := Json.mkObj [("node_type", Json.str "Name"), ("id", Json.str id)]

/-- If `j` is a call to the `passta` result marker `Result()` / `ResultT(v)`, the member name; else
`none`. `Result()` denotes the function's return value, only meaningful in a postcondition. -/
def resultCallMember? (j : Json) : Option String :=
  if jsonNodeType? j == some "Call" then
    match (j.getObjVal? "func").toOption with
    | some func =>
      match func.getObjValAs? String "library_module", func.getObjValAs? String "library_member" with
      | .ok "passta", .ok m => if m == "Result" || m == "ResultT" then some m else none
      | _, _ => none
    | none => none
  else none

/-- Does `j` (recursively) reference `Result()`/`ResultT(...)`? Such an `Ensures`/`Assert` is a
statement about the return value, so it must become the spec's *postcondition* rather than an in-body
checkpoint (where the return value does not yet exist). -/
partial def jsonMentionsResult (j : Json) : Bool :=
  match resultCallMember? j with
  | some _ => true
  | none =>
    match j with
    | .arr a => a.any jsonMentionsResult
    | .obj kvs => kvs.toList.any (fun (_, v) => jsonMentionsResult v)
    | _ => false

/-- Does this IR subtree *read* the variable `name` (a `Name` node with that `id`)? -/
partial def jsonRefsName (j : Json) (name : String) : Bool :=
  (j.getObjValAs? String "node_type" == .ok "Name" && j.getObjValAs? String "id" == .ok name) ||
    (match j with
     | .arr a => a.any (jsonRefsName · name)
     | .obj kvs => kvs.toList.any (fun (_, v) => jsonRefsName v name)
     | _ => false)

/-- Replace every `Result()`/`ResultT(...)` call in `j` with `repl`. The replacement is a `Name` node
(the postcondition's return binder, monadic path) or the returned expression itself (pure path). -/
partial def substResultWith (repl : Json) (j : Json) : Json :=
  match resultCallMember? j with
  | some _ => repl
  | none =>
    match j with
    | .arr a => Json.arr (a.map (substResultWith repl))
    | .obj kvs => Json.mkObj (kvs.toList.map (fun (k, v) => (k, substResultWith repl v)))
    | other => other

/-- Replace `Result()`/`ResultT(...)` with a `Name` referencing `retId`, so an `Ensures(Result() >= 1)`
lowers as `retId >= 1`. -/
def substResult (retId : String) (j : Json) : Json := substResultWith (nameJson retId) j

/-- Replace every `Name` node with id `name` by `repl` in `j`. -/
partial def substNameWith (name : String) (repl : Json) (j : Json) : Json :=
  if j.getObjValAs? String "node_type" == .ok "Name" && j.getObjValAs? String "id" == .ok name then repl
  else match j with
    | .arr a => Json.arr (a.map (substNameWith name repl))
    | .obj kvs => Json.mkObj (kvs.toList.map (fun (k, v) => (k, substNameWith name repl v)))
    | other => other

/-- Drop the verification-only postcondition markers from a body: every `Ensures` (all are postcondition
conjuncts now) and any `Result()`-bearing `Assert`. A non-`Result` `Assert` stays — it's an in-body
checkpoint, a runtime no-op. (A `Result()`-bearing marker would crash the runnable twin on
`passta.Result`, so those must go.) -/
def stripResultMarkers (body : Array Json) : Array Json :=
  body.filter fun s =>
    match contractArg? s with
    | some (m, arg) => !(m == "Ensures" || (m == "Assert" && jsonMentionsResult arg))
    | none => true

/-- `Ensures`/`Assert` are postconditions, so they must sit at the start and/or end of the function —
never interleaved *between loops* (a `Assert` sandwiched between two `for`/`while` blocks is a
program-point checkpoint about intermediate state, which the Hoare postcondition can't express). A
leading snapshot assignment before an `Ensures` (`orig = n; Ensures(… orig …)`) is fine, so only
`for`/`while` count as "computation" here. Returns `true` if some top-level `Ensures`/`Assert` has a
loop both before AND after it. -/
def hasMidFunctionPostcondition (body : Array Json) : Bool := Id.run do
  -- Only actual postconditions are position-checked: every `Ensures`, and a `Result()`-bearing
  -- `Assert`. A non-`Result` `Assert` is a checkpoint (`Assert(fast is not None)` between two loops)
  -- and may sit anywhere — it's an in-body no-op, not a postcondition.
  let isPostcondition (s : Json) : Bool := match contractArg? s with
    | some (m, arg) => m == "Ensures" || (m == "Assert" && jsonMentionsResult arg)
    | none => false
  let isLoop (s : Json) : Bool := jsonNodeType? s == some "For" || jsonNodeType? s == some "While"
  let mut firstLoop : Option Nat := none
  let mut lastLoop : Nat := 0
  for h : i in [0:body.size] do
    if isLoop body[i] then
      if firstLoop.isNone then firstLoop := some i
      lastLoop := i
  match firstLoop with
  | none => return false
  | some lo =>
    for h : i in [0:body.size] do
      if isPostcondition body[i] && lo < i && i < lastLoop then return true
    return false

/-- Conjoin a list of `Prop` terms (empty → `True`). -/
def conjoin (ps : Array (TSyntax `term)) : PygenM (TSyntax `term) :=
  match ps.toList with
  | [] => `(True)
  | p :: rest => rest.foldlM (fun acc q => `($acc ∧ $q)) p

/-- A *pure, straight-line* contracted function (`Requires`/`Ensures`, `let`s, `return` —
no loops, IO, or `raise`). Splits the body into the runnable statements (contracts stripped) and the
proof data. Returns `(cleanBody, lets, hyps, concl)`. `none` if monadic, if any statement isn't a
fresh `let`/`return`/contract, if an `Invariant`/`Decreases` appears (those imply a loop)
or if there's no `Ensures`/`Assert` to prove. Multiple `Ensures` conjoin into one conclusion. -/
def contractShape? (fnName : String) (referenceFn : Bool) (paramNames : Array String)
    (body substantive : Array Json) :
    Option (Array Json × Array Json × Array Json × Array Json) := Id.run do
  if bodyNeedsIOMonad body || bodyNeedsExceptionMonad body then return none
  let mut lets : Array Json := #[]
  let mut hyps : Array Json := #[]
  let mut concls : Array Json := #[]
  let mut clean : Array Json := #[]
  let mut seen : Array String := #[]
  let mut sawContract := false
  let mut sawReturn := false
  let mut retExpr : Option Json := none
  for s in substantive do
    match contractArg? s with
    | some (member, arg) =>
      sawContract := true
      match member with
      | "Requires" | "Assume" => hyps := hyps.push arg
      | "Ensures" | "Assert" => concls := concls.push arg
      | _ => return none
    | none =>
      match jsonNodeType? s with
      | some "Return" =>
        sawReturn := true
        retExpr := (s.getObjVal? "value").toOption  -- the returned expression, for `Result()`
        clean := clean.push s
      | some "Assign" =>
        let .ok target := s.getObjVal? "target" | return none
        if jsonNodeType? target != some "Name" then return none
        let .ok tname := target.getObjValAs? String "id" | return none
        if paramNames.contains tname || seen.contains tname then return none
        seen := seen.push tname
        lets := lets.push s
        clean := clean.push s
      -- A pure control-flow body that returns on every path (an `if`/`elif: return` chain, e.g. a
      -- classification helper) lowers to a pure `if _ then _ else _` term, so it can stay on Track P
      -- instead of falling to the monadic `Id` path (which would make the value `Id α` and break a
      -- caller that uses it purely). Only when `referenceFn` — the spec then refers to the function by
      -- name rather than a single returned expression (which these branches don't provide).
      | some "If" =>
        if referenceFn && statementDefinitelyReturns s then
          sawReturn := true
          clean := clean.push s
        else return none
      | _ => return none
  if !sawContract || concls.isEmpty || !sawReturn then return none
  -- `Result()` in an `Ensures` denotes the function's return value. Normally we keep the spec
  -- *referring to the function by name* (`fnName params`) rather than inlining the return expression, so
  -- the theorem reads as "the function satisfies its contract". The function is `@[simp]`, so `taste?`'s
  -- `simp_all` unfolds it — same provability, clearer statement.
  -- BUT when the function name is a Python builtin (`sum`, `max`, …), the `Call fnName(params)` node
  -- would dispatch to the *builtin* (`pySum`) instead of the user `def`, so fall back to inlining the
  -- return expression there (`referenceFn = false`).
  let concl := match referenceFn, retExpr with
    | true, _ =>
      let callNode := Json.mkObj [
        ("node_type", Json.str "Call"),
        ("func", Json.mkObj [("node_type", Json.str "Name"), ("id", Json.str fnName)]),
        ("args", Json.arr (paramNames.map (fun p =>
          Json.mkObj [("node_type", Json.str "Name"), ("id", Json.str p)]))),
        ("keywords", Json.mkObj [])]
      concls.map (substResultWith callNode)
    | false, some e => concls.map (substResultWith e)
    | false, none => concls
  return some (clean, lets, hyps, concl)

/-- Build `@[taste_ingr] theorem <thmName> : ∀ params, <hyps> → (let-binders; <concl>) := by taste?`
from extracted proof data. Shared by the lone-assert promotion (`theoremShape?`) and the contract
(`_spec`) path.  -/
def buildSpecTheorem (thmName : TSyntax `ident)
    (argInfos : Array (TSyntax `ident × Option (TSyntax `term)))
    (letJsons hypJsons : Array Json) (conclJsons : Array Json) : PygenM (TSyntax `command) :=
  withFreshVariables do
    for letJson in letJsons do
      if let .ok tname := (letJson.getObjVal? "target").bind (·.getObjValAs? String "id") then
        addVar tname.toName
    -- Conjoin the `Ensures` at the Lean level (as the monadic path does), not by synthesising a
    -- Python `BoolOp` — that would re-lower each conjunct through the `Bool` coercion.
    let mut propTy ← conjoin (← conclJsons.mapM (fun c => withPropCondition true (getCode c `term)))
    for hypJson in hypJsons.reverse do
      propTy ← `($(← withPropCondition true (getCode hypJson `term)) → $propTy)
    for letJson in letJsons.reverse do
      let .ok target := letJson.getObjVal? "target" | throwError "buildSpecTheorem: Assign without target"
      let .ok value := letJson.getObjVal? "value" | throwError "buildSpecTheorem: Assign without value"
      propTy ← `(let $(← getCode target `ident) := $(← getCode value `term)
                 $propTy)
    for (argIdent, ty?) in argInfos.reverse do
      propTy ← match ty? with
        | some ty => `(∀ ($argIdent : $ty), $propTy)
        | none => `(∀ $argIdent, $propTy)
    `(command| @[taste_ingr] theorem $thmName : $propTy := by taste?)

/-- Does any `Assign`/`AugAssign` inside `stmt` (recursing into nested bodies) target `name`? Used
to find which mutable variables a loop threads (its mvcgen state). -/
partial def jsonAssignsName (stmt : Json) (name : String) : Bool :=
  match jsonNodeType? stmt with
  | some "Assign" | some "AugAssign" =>
    match (stmt.getObjVal? "target").toOption with
    | some tgt =>
      -- single `Name` target, OR a tuple target (`a, b = …`) whose elements include `name`.
      tgt.getObjValAs? String "id" == .ok name
        || (match tgt.getObjValAs? (Array Json) "elts" with
            | .ok elts => elts.any (·.getObjValAs? String "id" == .ok name)
            | _ => false)
    | none => false
  | _ => Id.run do
    for key in ["body", "orelse", "finalbody"] do
      if let .ok (arr : Array Json) := stmt.getObjValAs? (Array Json) key then
        for s in arr do
          if jsonAssignsName s name then return true
    return false

/-- Mutable-variable declaration order: top-level `Assign` targets, first occurrence first. This is
the order mvcgen threads them as the loop state tuple. -/
def declaredMutOrder (body : Array Json) : Array String := Id.run do
  let mut acc : Array String := #[]
  let pushName (acc : Array String) (n : String) : Array String :=
    if acc.contains n then acc else acc.push n
  for s in body do
    if jsonNodeType? s == some "Assign" then
      let tgt := (s.getObjVal? "target").toOption
      match tgt.bind (·.getObjValAs? String "id" |>.toOption) with
      | some name => acc := pushName acc name
      | none =>
        -- tuple/list target `a, b = …`: register each element name in source order.
        if let some t := tgt then
          if let .ok (elts : Array Json) := t.getObjValAs? (Array Json) "elts" then
            for e in elts do
              if let .ok name := e.getObjValAs? String "id" then acc := pushName acc name
  return acc

/-- If accumulator `acc` is updated at the loop-body top level by `acc += e` or `acc = acc + e`,
return the contribution `e` — used to auto-derive `acc = (cur.prefix.map (fun v => e)).sum` when the
user gave no `Invariant`. `none` for conditional/other mutations. -/
def accContribution? (loopBody : Array Json) (acc : String) : Option Json := Id.run do
  for s in loopBody do
    match jsonNodeType? s with
    | some "AugAssign" =>
      if (s.getObjVal? "target").bind (·.getObjValAs? String "id") == .ok acc
          && s.getObjValAs? String "op" == .ok "add" then
        return (s.getObjVal? "value").toOption
    | some "Assign" =>
      if (s.getObjVal? "target").bind (·.getObjValAs? String "id") == .ok acc then
        if let some value := (s.getObjVal? "value").toOption then
          if jsonNodeType? value == some "BinOp" && value.getObjValAs? String "op" == .ok "add" then
            match (value.getObjVal? "left").toOption, (value.getObjVal? "right").toOption with
            | some lj, some rj =>
              if lj.getObjValAs? String "id" == .ok acc then return some rj
              if rj.getObjValAs? String "id" == .ok acc then return some lj
            | _, _ => pure ()
    | _ => pure ()
  return none

/-- Does `stmt` early-exit *this* loop (a `return`/`break`, recursing through `if`s but not into a
nested `for`/`while`, which owns its own exits)? Such a loop threads an extra early-return state, so
its invariant must use `Invariant.withEarlyReturn` rather than a plain `⇓` bullet. -/
partial def jsonHasEarlyExit (stmt : Json) : Bool :=
  match jsonNodeType? stmt with
  | some "Return" | some "Break" => true
  | some "For" | some "While" => false
  | _ => Id.run do
    for key in ["body", "orelse", "finalbody"] do
      if let .ok (arr : Array Json) := stmt.getObjValAs? (Array Json) key then
        for s in arr do if jsonHasEarlyExit s then return true
    return false

/-- Per-loop invariant data: the loop variable, whether the iterable is a `range(...)`, the threaded
accumulators (in declaration order), the conjuncts of its `Invariant(...)` markers, the contribution
expressions of `+= e` accumulators (for auto-derivation), and whether the loop early-exits. -/
structure LoopInv where
  loopVar : String
  isRange : Bool
  accumulators : Array String
  invariants : Array Json
  accMutations : Array (String × Json)
  hasEarlyExit : Bool
  /-- `true` for a native `while` loop (needs a variant + `Sum.elim` invariant bullet pair, not the
  cursor-based `for` bullet). -/
  isWhile : Bool := false
  /-- The `Decreases(...)` measure of a `while` loop (the termination variant). -/
  decreases : Option Json := none
  /-- A `while` loop's threaded state: the mutable vars it reassigns, in declaration order. mvcgen
  threads them as a right-nested `MProd` whose `.fst` is the *first*-declared. -/
  whileStateVars : Array String := #[]

/-- All proof data for a monadic contracted function. -/
structure MonadicContract where
  cleanBody : Array Json   -- def body with `Requires`/`Assume` and `Result`-bearing `Ensures` stripped
  requires : Array Json    -- `Requires`/`Assume` predicate args → precondition
  ensures : Array Json     -- `Ensures`/`Assert` args mentioning `Result()` → postcondition
  retName : Option String  -- name of the returned variable (`return x`), used to bind the post result
  loops : Array LoopInv

/-- Builds a LoopInv from one For node. Returns none only if the For lacks a target/iter. -/
def loopInvOf (declaredOrder : Array String) (forNode : Json) : Option LoopInv :=
  match (forNode.getObjVal? "iter").toOption with
  | none => none
  | some iter =>
    -- Loop var: a single `Name` target's id, else a placeholder — a tuple target (`for a, b in …`)
    -- has no `id`; its components are body-locals and a non-range invariant never references the index.
    let loopVar := ((forNode.getObjVal? "target").bind (·.getObjValAs? String "id")).toOption.getD "_loop"
    let isRange := jsonNodeType? iter == some "Range"
    let loopBody := (forNode.getObjValAs? (Array Json) "body").toOption.getD #[]
    let invariants := loopBody.filterMap fun s =>
      match contractArg? s with
      | some ("Invariant", arg) => some arg
      | _ => none
    let accumulators := declaredOrder.filter fun v => loopBody.any (jsonAssignsName · v)
    let accMutations := accumulators.filterMap fun a =>
      (accContribution? loopBody a).map (fun e => (a, e))
    let hasEarlyExit := loopBody.any jsonHasEarlyExit
    some { loopVar, isRange, accumulators, invariants, accMutations, hasEarlyExit }

/-- Builds a LoopInv from one `While` node. mvcgen lowers a native `while` differently from a `for`:
its loop state is the tuple of vars the body reassigns (an `MProd`), and it needs a termination
*variant* alongside the invariant. `none` unless the loop carries a `Decreases(...)` (the variant). -/
def loopInvOfWhile (declaredOrder : Array String) (whileNode : Json) : Option LoopInv := Id.run do
  let loopBody := (whileNode.getObjValAs? (Array Json) "body").toOption.getD #[]
  let invariants := loopBody.filterMap fun s =>
    match contractArg? s with | some ("Invariant", arg) => some arg | _ => none
  let decreases := loopBody.findSome? fun s =>
    match contractArg? s with | some ("Decreases", arg) => some arg | _ => none
  if decreases.isNone then return none
  let stateVars := declaredOrder.filter fun v => loopBody.any (jsonAssignsName · v)
  if stateVars.isEmpty then return none
  -- Every var the loop reassigns must be a captured pre-loop state var, else the mvcgen `MProd` has a
  -- slot we can't place (e.g. a *parameter* mutated in the loop, which has no pre-loop init). Emitting
  -- a bullet then mis-projects the state → a stuck metavariable (a Generated that won't compile). Decline
  -- so the loop falls back to bare `mvcgen` + `sorry` (which always compiles).
  let loopMutated : Array String := loopBody.foldl (init := #[]) fun acc s =>
    match jsonNodeType? s with
    | some "Assign" | some "AugAssign" =>
      match (s.getObjVal? "target").toOption.bind (fun t => (t.getObjValAs? String "id").toOption) with
      | some nm => if acc.contains nm then acc else acc.push nm
      | none => acc
    | _ => acc
  if loopMutated.any (fun v => !stateVars.contains v) then return none
  let hasEarlyExit := loopBody.any jsonHasEarlyExit
  let li : LoopInv := {
    loopVar := "", isRange := false, accumulators := #[], invariants := invariants,
    accMutations := #[], hasEarlyExit := hasEarlyExit, isWhile := true,
    decreases := decreases, whileStateVars := stateVars }
  return some li

/-- A *monadic* contracted function (has a `for` loop with `Invariant(...)`, or effects).
Strips `Requires`/`Assume` (→ precondition), keeps everything else (so `Ensures` stay as in-body
checkpoints and `Invariant` markers stay as provable checkpoints), and records per-loop invariant
data. `none` when there is no contract marker. -/
def monadicContractInfo? (body : Array Json) : Option MonadicContract := Id.run do
  let declared := declaredMutOrder body
  let mut requires : Array Json := #[]
  let mut ensures : Array Json := #[]
  let mut clean : Array Json := #[]
  let mut loops : Array LoopInv := #[]
  let mut retName : Option String := none
  let mut sawContract := false
  for s in body do
    match contractArg? s with
    | some (member, arg) =>
      sawContract := true
      match member with
      | "Requires" | "Assume" => requires := requires.push arg
      -- `Ensures` is a DECLARED postcondition (holds at return): EVERY one becomes a spec postcondition
      -- conjunct, not just the `Result()`-bearing ones — so the proof is meaningful. A non-`Result`
      -- `Ensures` is a claim about the returned value / params (references the result binder — named
      -- after the returned variable — or params).
      | "Ensures" => ensures := ensures.push arg
      -- `Assert` is a program-point CHECKPOINT. Only a `Result()`-bearing one is a postcondition; a
      -- non-`Result` `Assert` asserts intermediate local state (`a is not None`) that the Hoare post
      -- can't express, so it stays an in-body no-op checkpoint (unchanged behavior).
      | "Assert" =>
        if jsonMentionsResult arg then ensures := ensures.push arg
        else clean := clean.push s
      | _ => clean := clean.push s
    | none =>
      if jsonNodeType? s == some "For" then
        if let some li := loopInvOf declared s then
          sawContract := sawContract || !li.invariants.isEmpty
          loops := loops.push li
      if jsonNodeType? s == some "While" then
        if let some li := loopInvOfWhile declared s then
          sawContract := sawContract || !li.invariants.isEmpty
          loops := loops.push li
      -- Record a `return <name>` so the postcondition can bind that variable as its result.
      if jsonNodeType? s == some "Return" then
        if let .ok v := s.getObjVal? "value" then
          if jsonNodeType? v == some "Name" then
            if let .ok rid := v.getObjValAs? String "id" then retName := some rid
      clean := clean.push s
  if !sawContract then return none
  -- Nothing to verify monadically — no `Result()`-postcondition and no loop (just a `Requires` on a
  -- straight-line body) — so decline and let the generic pure/`Id` emission handle it. Otherwise a
  -- `Requires`-only helper becomes `Id α`, breaking a caller that uses it purely (`min(f x for x in …)`
  -- needs `Ord α`, not `Ord (Id α)`).
  if ensures.isEmpty && loops.isEmpty then return none
  -- Inline pre-loop SNAPSHOT locals into the pre- and postcondition. A `Requires`/`Ensures` may
  -- name a local defined before the loop (`n = len(nums)`; `orig = x`; `base = a//b+1`) — but the
  -- Hoare-triple spec binds only the parameters + result, so that name is unbound ("Unknown
  -- identifier"). A *snapshot* — a top-level `x = e` before the first loop, with `x` assigned nowhere
  -- else — has a fixed value, so we substitute `x ↦ e` into them (mirroring the pure track's
  -- `let`-chain). Each snapshot's value is first expanded through earlier snapshots, so the result
  -- names only params/constants.
  let firstLoop := body.findIdx? (fun s => jsonNodeType? s == some "For" || jsonNodeType? s == some "While")
  let preLoop := match firstLoop with | some i => body.extract 0 i | none => body
  let mut snaps : Array (String × Json) := #[]
  for s in preLoop do
    if jsonNodeType? s == some "Assign" then
      if let .ok tname := (s.getObjVal? "target").bind (·.getObjValAs? String "id") then
        if let .ok val := s.getObjVal? "value" then
          if (body.foldl (fun acc st => acc + (if jsonAssignsName st tname then 1 else 0)) 0) == 1 then
            let val' := snaps.foldl (fun e (n, rv) => substNameWith n rv e) val
            snaps := snaps.push (tname, val')
  let inline (e : Json) : Json := snaps.foldl (fun x (n, rv) => substNameWith n rv x) e
  return some { cleanBody := clean, requires := requires.map inline, ensures := ensures.map inline, retName, loops }

/-- A contracted function whose loop is a single straight-line `while` carrying an `Invariant` and a
`Decreases`. This is the shape we lower through `pyWhile` + `pyWhile_correct` (instead of mvcgen's
`for`-only `invariants` bullets). The MVP shape:

    <Requires/Ensures…>
    v₁ = e₁ ; … ; v_k = e_k          -- pre-loop inits of the state vars
    while <test>:
        Invariant(…) …               -- one or more
        Decreases(<measure>)         -- exactly one (the variant μ)
        v_i = e_i' ; …               -- straight-line reassignments of the state vars only
    return <retExpr>                 -- in terms of the state vars

`none` if the body isn't exactly inits + one such `while` + a `return`, if any non-`Assign`/marker
statement appears in the loop, if a loop-assigned var lacks a pre-loop init, or if no `Decreases`. -/
structure WhileShape where
  requires   : Array Json          -- precondition predicates
  ensures    : Array Json          -- postcondition predicates (mention `Result()`)
  retExpr    : Json                -- the returned expression (state-var terms; also the `Result()` value)
  stateVars  : Array String        -- mutable vars threaded through the loop, in init order
  inits      : Array Json          -- initial value expression per state var
  test       : Json                -- the `while` guard
  invariants : Array Json          -- `Invariant(...)` conjuncts
  decreases  : Json                -- the `Decreases(...)` measure (the variant μ)
  bodyAssigns : Array Json         -- the loop body's straight-line assignments (markers stripped)

def whileContractShape? (paramNames : Array String) (substantive : Array Json) :
    Option WhileShape := Id.run do
  if bodyNeedsIOMonad substantive || bodyNeedsExceptionMonad substantive then return none
  let mut requires : Array Json := #[]
  let mut ensures : Array Json := #[]
  let mut initOrder : Array String := #[]            -- pre-loop assign targets, in order
  let mut initVals : Std.HashMap String Json := {}
  let mut retExpr? : Option Json := none
  let mut whileNode? : Option Json := none
  for s in substantive do
    match contractArg? s with
    | some (member, arg) =>
      match member with
      | "Requires" | "Assume" => requires := requires.push arg
      | "Ensures" | "Assert" => if jsonMentionsResult arg then ensures := ensures.push arg
      | _ => return none                              -- a stray Invariant/Decreases outside the loop
    | none =>
      match jsonNodeType? s with
      | some "Assign" =>
        if whileNode?.isSome then return none         -- assignment AFTER the loop: not the MVP shape
        let .ok target := s.getObjVal? "target" | return none
        if jsonNodeType? target != some "Name" then return none
        let .ok tname := target.getObjValAs? String "id" | return none
        let .ok val := s.getObjVal? "value" | return none
        if !initVals.contains tname then initOrder := initOrder.push tname
        initVals := initVals.insert tname val
      | some "While" =>
        if whileNode?.isSome then return none         -- only one loop supported
        whileNode? := some s
      | some "Return" =>
        retExpr? := (s.getObjVal? "value").toOption
      | _ => return none
  let some whileNode := whileNode? | return none
  let some retExpr := retExpr? | return none
  let .ok test := whileNode.getObjVal? "test" | return none
  let loopBody := (whileNode.getObjValAs? (Array Json) "body").toOption.getD #[]
  let mut invariants : Array Json := #[]
  let mut decreases? : Option Json := none
  let mut bodyAssigns : Array Json := #[]
  let mut assignedInLoop : Array String := #[]
  for s in loopBody do
    match contractArg? s with
    | some ("Invariant", arg) => invariants := invariants.push arg
    | some ("Decreases", arg) => decreases? := some arg
    | some _ => return none                           -- other markers inside the loop: bail
    | none =>
      let nt := jsonNodeType? s
      if nt != some "Assign" && nt != some "AugAssign" then return none  -- nested if/break/etc.: bail
      let .ok target := s.getObjVal? "target" | return none
      if jsonNodeType? target != some "Name" then return none
      let .ok tname := target.getObjValAs? String "id" | return none
      if !assignedInLoop.contains tname then assignedInLoop := assignedInLoop.push tname
      bodyAssigns := bodyAssigns.push s
  let some decreases := decreases? | return none      -- need the variant μ
  if invariants.isEmpty then return none
  -- Classify each loop-assigned var: CARRIED state vs a per-iteration TEMPORARY. A var is carried if it
  -- is read in the guard/measure/invariants/return (`liveOut`), OR read in the body before its own first
  -- write (its previous-iteration value is live). A temporary — written before it is read and dead after
  -- the loop (e.g. `mid = (lo+hi)//2`) — is NOT threaded through the state; it stays a plain `let` in the
  -- body lambda, shrinking the state tuple. Only carried vars need a pre-loop init.
  let liveOut := fun (v : String) =>
    jsonRefsName test v || jsonRefsName decreases v ||
      invariants.any (jsonRefsName · v) || jsonRefsName retExpr v
  let mut carried : Array String := #[]
  let mut written : Array String := #[]
  for a in bodyAssigns do
    let val := (a.getObjVal? "value").toOption.getD Json.null
    let tgt := (a.getObjVal? "target").toOption.bind (·.getObjValAs? String "id" |>.toOption)
    let isAug := jsonNodeType? a == some "AugAssign"      -- `v op= e` reads `v`
    for v in assignedInLoop do
      if (jsonRefsName val v || (isAug && tgt == some v)) && !written.contains v && !carried.contains v then
        carried := carried.push v
    if let some t := tgt then if !written.contains t then written := written.push t
  for v in assignedInLoop do
    if liveOut v && !carried.contains v then carried := carried.push v
  -- State vars = carried, ordered by pre-loop init; each carried var must have a pre-loop init.
  let stateVars := initOrder.filter (carried.contains ·)
  if stateVars.isEmpty || carried.any (!initVals.contains ·) then return none
  let inits := stateVars.map (initVals.get! ·)
  return some { requires, ensures, retExpr, stateVars, inits, test, invariants, decreases, bodyAssigns }

/-- One invariant bullet for a loop. The predicate relates the accumulators to `cur.prefix`:
* user `Invariant(...)` markers, conjoined — for a `range` loop the loop variable is bound to
  `cur.prefix.length` (the index), so index-style invariants work;
* otherwise, **auto-derived** from each `acc += e` update: `acc = (cur.prefix.map (fun v => e)).sum`
  (only for non-`range` loops, where `cur.prefix` is the element list);
* else `True`.
The binder is `⇓ cur =>` with no accumulators, `⇓⟨cur, a, …⟩` with some. -/
def buildBullet (li : LoopInv) : PygenM (TSyntax `term) := do
  for a in li.accumulators do addVar a.toName
  addVar li.loopVar.toName
  let cur := mkIdent `cur
  let loopVarId := mkIdent li.loopVar.toName
  let body ←
    if !li.invariants.isEmpty then
      let props ← li.invariants.mapM (fun inv => withPropCondition true (getCode inv `term))
      let conj ← conjoin props
      if li.isRange then `(let $loopVarId := ($(cur).prefix.length : Int); $conj) else pure conj
    else if !li.isRange && !li.accMutations.isEmpty then
      let mut autos : Array (TSyntax `term) := #[]
      for (acc, contrib) in li.accMutations do
        let cStx ← getCode contrib `term
        autos := autos.push
          (← `($(mkIdent acc.toName) = ($(cur).prefix.map (fun $loopVarId => $cStx)).sum))
      conjoin autos
    else
      `(True)
  let accIdents := li.accumulators.map (fun s => mkIdent s.toName)
  -- A `break`/`return` loop supplies its invariant via `Invariant.withEarlyReturn`; carry the user
  -- invariant in `onContinue` (previously dropped to `True`). `onReturn` stays trivial.
  if li.hasEarlyExit then
    -- `onContinue : Cursor → accState → Assertion`: `cur` is the cursor, the accumulators are
    -- projected out of the state `b` (right-nested `MProd` in declaration order).
    let b := mkIdent `b
    let k := li.accumulators.size
    let mut assertBody := body
    for h : i in [0:k] do
      let mut proj : TSyntax `term := b
      for _ in [0:i] do proj ← `($proj |>.snd)
      if k > 1 && i + 1 != k then proj ← `($proj |>.fst)
      assertBody ← `(let $(accIdents[i]!) := $proj; $assertBody)
    return ← `(Invariant.withEarlyReturn (onContinue := fun $cur $b => ⌜$assertBody⌝)
      (onReturn := fun _ _ => ⌜True⌝))
  if li.accumulators.isEmpty then
    `(⇓ $cur => ⌜$body⌝)
  else
    `(⇓⟨$cur, $accIdents,*⟩ => ⌜$body⌝)

/-- The `i`-th projection of a right-nested `MProd` of `k` elements (`.fst`, `.snd.fst`, …, and the
last is `.snd…snd`). For `k = 1` the state is the bare value, so the projection is `base` itself. -/
def mprodProj (base : TSyntax `term) (i k : Nat) : PygenM (TSyntax `term) := do
  if k ≤ 1 then return base
  let mut e := base
  for _ in [0:i] do e ← `($e |>.snd)
  if i + 1 == k then return e else `($e |>.fst)

/-- Bullets for one loop: a `for` loop yields its single cursor invariant; a `while` loop yields a
`[variant, invariant]` pair (mvcgen's native-`while` API). For the `while` case the loop state is a
right-nested `MProd` of the reassigned vars, so we `let`-bind each var name to its projection and then
lower the user's `Decreases`/`Invariant` markers over those names. The invariant is wrapped in
`Sum.elim … (fun _ => True)` because mvcgen's while-invariant ranges over `state ⊕ earlyReturn`. -/
def buildBullets (li : LoopInv) : PygenM (Array (TSyntax `term)) := do
  if !li.isWhile then return #[← buildBullet li]
  let vars := li.whileStateVars
  let k := vars.size
  for v in vars do addVar v.toName
  -- `let vᵢ := base.<projᵢ>; …` prelude so the lowered markers resolve the loop vars.
  let mkLets (base : TSyntax `term) (rest : TSyntax `term) : PygenM (TSyntax `term) := do
    let mut body := rest
    for h : i in [0:k] do
      let proj ← mprodProj base i k
      let vid := mkIdent vars[i]!.toName
      body ← `(let $vid := $proj; $body)
    return body
  let s := mkIdent `s
  let st := mkIdent `st
  -- variant: `fun s => (⟨μ.toNat⟩ : ULift Nat)` — μ the `Decreases` measure over the state vars.
  let measure ← getCode li.decreases.get! `term
  let variantBody ← mkLets s (← `((⟨($measure).toNat⟩ : ULift Nat)))
  let variant ← `(fun $s => $variantBody)
  -- invariant: `⇓ s => ⌜Sum.elim (fun st => <inv>) (fun _ => True) s⌝`.
  let invProps ← li.invariants.mapM (fun inv => withPropCondition true (getCode inv `term))
  let invConj ← conjoin invProps
  let invBody ← mkLets st invConj
  let invariant ← `(⇓ $s => ⌜Sum.elim (fun $st => $invBody) (fun _ => True) $s⌝)
  return #[variant, invariant]

/-- Build the monadic spec theorem `⦃⌜Requires⌝⦄ fn params ⦃⇓ _ => ⌜True⌝⦄` proven by
`mvcgen [fn] invariants …` + a trailing `taste?`. Only the precondition is lifted from `Requires`/
`Assume`; the postcondition stays `True` (`Ensures`/`Assert` are proved as in-body checkpoints). -/
def buildMonadicSpec (thmName correctName fnName : TSyntax `ident) (emitReadable : Bool)
    (argInfos : Array (TSyntax `ident × Option (TSyntax `term)))
    (info : MonadicContract) : PygenM (TSyntax `command) := withFreshVariables do
  let paramIdents : Array (TSyntax `ident) := argInfos.map (·.1)
  for p in paramIdents do addVar p.getId
  let preProps ← info.requires.mapM (fun r => withPropCondition true (getCode r `term))
  let pre ← conjoin preProps
  let bullets := (← info.loops.mapM buildBullets).flatten
  -- mvcgen lemma set is added here
  let lemmas ← #[(⟨fnName.raw⟩ : TSyntax `term), mkIdent ``PastaLean.pyRange_forIn,
      mkIdent ``PastaLean.pyRange_forIn_start].mapM
    (fun t => `(Lean.Parser.Tactic.simpLemma| $t:term))
  -- `taste?` is a TRAILING tactic (not `mvcgen … with taste?`). `with` runs one closer per VC, so
  -- heterogeneous VCs force an ugly `first | …` portfolio in the recorded proof. As a trailing tactic
  -- `taste?` instead sees all the leftover VCs as goals at once and its close-loop records a flat
  -- `c₁; c₂; …` sequence (one closer per goal, in order) — the prove-and-replace splice drops that in
  -- verbatim. If `mvcgen` already discharged every VC, `taste?` runs on no goals and records nothing,
  -- and the splice prunes the dangling `taste?` line, leaving a clean `mvcgen [...]`.
  -- `try`-guard `mvcgen`: with an `invariants` clause it HARD-ERRORS when the function has a `for`
  -- loop that carries no `Invariant(...)` (so no bullet) — "Lacking definitions for the following
  -- invariants". `try` rolls that back to the raw goal, which the trailing `taste? ; all_goals sorry`
  -- degrades to a compiling `sorry`. Transparent when `mvcgen` succeeds.
  let mv ← if bullets.isEmpty then
      `(tactic| mvcgen [$lemmas,*])
    else
      `(tactic| try mvcgen [$lemmas,*] invariants $[· $bullets:term]*)

  -- POSTCONDITION. With no `Result()`-bearing `Ensures` the postcondition stays `True` (any plain
  -- `Ensures`/`Assert` is proved as an in-body checkpoint instead). When the user wrote an
  -- `Ensures(Result() …)`, those args are collected into `info.ensures` (a statement about the return
  -- value), so we lift them into the spec *statement* (Nagini-style, modular `@[spec]` reuse): bind the
  -- returned variable as the result, lower each `Ensures` with `Result()` rewritten to that binder, and
  -- tag the theorem `@[spec]`.
  -- A trailing `all_goals sorry` catch-all: the prove-and-replace splice records closers against the
  -- goals `taste?` saw in the warm backend, but the final file re-elaborates in a fresh env where
  -- `mvcgen` can leave a DIFFERENT goal count — so a spliced single `sorry` under-closes. `all_goals
  -- sorry` mops up any residual; on a fully-closed proof it runs on zero goals (no-op, axiom-clean).
  if info.ensures.isEmpty then
    -- No `Result()` postcondition → the `True`-post triple. For a straight-line `Id`-monad body
    -- `wp⟦x⟧ (fun _ => True)` reduces to `True` and the one-liner closes it. But a body with a loop
    -- and an early `return` leaves a residual `wp` goal that `exact True.intro` can't discharge, so
    -- `try` the one-liner and let `all_goals sorry` mop up any residual (a no-op — axiom-clean — when
    -- the one-liner already closed everything; a `sorry` only for the genuine loop case). PALC accepts
    -- a `sorry` (it compiles); an unsolved-goals *error* it does not.
    let _ := mv
    let specOnly ← `(command| theorem $thmName :
        ⦃⌜$pre⌝⦄ $fnName $paramIdents* ⦃⇓ _ => ⌜True⌝⦄ := by
          try (apply Std.Do.Triple.of_entails_wp; intro _; exact True.intro)
          all_goals sorry)
    return ⟨mkNullNode #[specOnly.raw]⟩
  else
    let retId := info.retName.getD "result"
    let retBinder := mkIdent retId.toName
    addVar retId.toName  -- so `Result()` (rewritten to the `retId` `Name`) lowers to the binder
    let postProps ← info.ensures.mapM
      (fun e => withPropCondition true (getCode (substResult retId e) `term))
    let post ← conjoin postProps
    let specCmd ← `(command| @[spec] theorem $thmName :
        ⦃⌜$pre⌝⦄ $fnName $paramIdents* ⦃⇓ $retBinder => ⌜$post⌝⦄ := by
          $mv:tactic
          taste?
          all_goals sorry)
    -- A helper (`_`-prefixed) keeps only its supporting Hoare `_spec`; the readable `_correct`
    -- corollary is reserved for the one top-level function.
    -- The readable `.run` corollary below relies on `⦃P⦄ x ⦃⇓r => Q r⦄` being DEFEQ to `P → Q x.run`,
    -- which holds for the `Id` monad only. A `try`/`except` body runs in `ExceptT PyException Id`,
    -- where `x.run : Except _ r` (not `r`), so `let result := (fn …).run; result ≥ 0` is ill-typed
    -- (`Except _ ℝ ≥ ℚ`). Keep just the Hoare `_spec` there — it already binds the OK value via `⇓`.
    if !emitReadable || bodyNeedsExceptionMonad info.cleanBody then
      return ⟨mkNullNode #[specCmd.raw]⟩
    -- Human-readable corollary: the same fact with the `Id` monad + Hoare braces stripped —
    -- `∀ params, Requires → (let result := (fn params).run; Ensures)` — proved straight from the
    -- triple (for `Id`, `⦃⌜P⌝⦄ x ⦃⇓r => ⌜Q r⌝⦄` is defeq to `P → Q x.run`, so `exact <spec> h` closes it).
    let runResult ← `(($fnName $paramIdents*).run)
    let readableConcl ← `(let $retBinder := $runResult; $post)
    let hpre := mkIdent `hpre
    let mut body : TSyntax `term := readableConcl
    let proof ← if info.requires.isEmpty
      then `(tactic| exact $thmName True.intro)
      else `(tactic| exact $thmName $hpre)
    if !info.requires.isEmpty then
      body ← `($pre → $body)
    let introTac ← if info.requires.isEmpty
      then `(tactic| intro $paramIdents*)
      else `(tactic| intro $paramIdents* $hpre:ident)
    for (argIdent, ty?) in argInfos.reverse do
      body ← match ty? with
        | some ty => `(∀ ($argIdent : $ty), $body)
        | none => `(∀ $argIdent, $body)
    let correctCmd ← `(command| theorem $correctName : $body := by
          $introTac:tactic
          $proof:tactic)
    return ⟨mkNullNode #[specCmd.raw, correctCmd.raw]⟩

end PastaLean

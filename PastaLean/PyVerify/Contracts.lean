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

/-- Drop `Ensures`/`Assert` markers whose predicate mentions `Result()` from a body. Such a marker is
verification-only: its content becomes the spec postcondition and `Result()` has NO runtime lowering,
so it must not appear in ANY emitted runnable body — including the `'rn` twin, which keeps the other
markers (`Requires`/`Invariant`/…) as runtime no-ops but would crash on `passta.Result`. -/
def stripResultMarkers (body : Array Json) : Array Json :=
  body.filter fun s =>
    match contractArg? s with
    | some (m, arg) => !((m == "Ensures" || m == "Assert") && jsonMentionsResult arg)
    | none => true

/-- A *pure, straight-line* contracted function (`Requires`/`Ensures`, `let`s, `return` —
no loops, IO, or `raise`). Splits the body into the runnable statements (contracts stripped) and the
proof data. Returns `(cleanBody, lets, hyps, concl)`. `none` if monadic, if any statement isn't a
fresh `let`/`return`/contract, if an `Invariant`/`Decreases` appears (those imply a loop)
or if there's no `Ensures`/`Assert` to prove. Multiple `Ensures` conjoin into one conclusion. -/
def contractShape? (paramNames : Array String) (body substantive : Array Json) :
    Option (Array Json × Array Json × Array Json × Json) := Id.run do
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
      | _ => return none
  if !sawContract || concls.isEmpty || !sawReturn then return none
  let concl0 := if concls.size == 1 then concls[0]!
    else Json.mkObj [("node_type", Json.str "BoolOp"), ("op", Json.str "and"), ("values", Json.arr concls)]
  -- A pure function has no return *binder*; `Result()` in an `Ensures` denotes the returned
  -- expression, so substitute it in (e.g. `Ensures(Result() == 2*x)` with `return 2*x` ⇒ `2*x = 2*x`).
  let concl := match retExpr with
    | some e => substResultWith e concl0
    | none => concl0
  return some (clean, lets, hyps, concl)

/-- Build `@[taste_ingr] theorem <thmName> : ∀ params, <hyps> → (let-binders; <concl>) := by taste?`
from extracted proof data. Shared by the lone-assert promotion (`theoremShape?`) and the contract
(`_spec`) path.  -/
def buildSpecTheorem (thmName : TSyntax `ident)
    (argInfos : Array (TSyntax `ident × Option (TSyntax `term)))
    (letJsons hypJsons : Array Json) (conclJson : Json) : PygenM (TSyntax `command) :=
  withFreshVariables do
    for letJson in letJsons do
      if let .ok tname := (letJson.getObjVal? "target").bind (·.getObjValAs? String "id") then
        addVar tname.toName
    let mut propTy ← withPropCondition true (getCode conclJson `term)
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
    ((stmt.getObjVal? "target").bind (·.getObjValAs? String "id")) == .ok name
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
  for s in body do
    if jsonNodeType? s == some "Assign" then
      if let .ok name := (s.getObjVal? "target").bind (·.getObjValAs? String "id") then
        if !acc.contains name then acc := acc.push name
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

/-- All proof data for a monadic contracted function. -/
structure MonadicContract where
  cleanBody : Array Json   -- def body with `Requires`/`Assume` and `Result`-bearing `Ensures` stripped
  requires : Array Json    -- `Requires`/`Assume` predicate args → precondition
  ensures : Array Json     -- `Ensures`/`Assert` args mentioning `Result()` → postcondition
  retName : Option String  -- name of the returned variable (`return x`), used to bind the post result
  loops : Array LoopInv

/-- Builds a LoopInv from one For node. Returns none only if the For lacks a target/iter. -/
def loopInvOf (declaredOrder : Array String) (forNode : Json) : Option LoopInv :=
  match (forNode.getObjVal? "target").bind (·.getObjValAs? String "id"),
        (forNode.getObjVal? "iter").toOption with
  | .ok loopVar, some iter =>
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
  | _, _ => none

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
      -- `Ensures`/`Assert` are treated identically. One mentioning `Result()` is a statement about
      -- the return value, so it becomes the spec *postcondition* (stripped from the body, where the
      -- return value doesn't exist yet); otherwise it stays an in-body checkpoint as before.
      | "Ensures" | "Assert" =>
        if jsonMentionsResult arg then ensures := ensures.push arg
        else clean := clean.push s
      | _ => clean := clean.push s
    | none =>
      if jsonNodeType? s == some "For" then
        if let some li := loopInvOf declared s then
          sawContract := sawContract || !li.invariants.isEmpty
          loops := loops.push li
      -- Record a `return <name>` so the postcondition can bind that variable as its result.
      if jsonNodeType? s == some "Return" then
        if let .ok v := s.getObjVal? "value" then
          if jsonNodeType? v == some "Name" then
            if let .ok rid := v.getObjValAs? String "id" then retName := some rid
      clean := clean.push s
  if !sawContract then return none
  return some { cleanBody := clean, requires, ensures, retName, loops }

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
  -- State vars: those assigned in the loop, each of which must have a pre-loop init. Ordered by init.
  let stateVars := initOrder.filter (assignedInLoop.contains ·)
  if stateVars.isEmpty || assignedInLoop.any (!initVals.contains ·) then return none
  let inits := stateVars.map (initVals.get! ·)
  return some { requires, ensures, retExpr, stateVars, inits, test, invariants, decreases, bodyAssigns }

/-- Conjoin a list of `Prop` terms (empty → `True`). -/
def conjoin (ps : Array (TSyntax `term)) : PygenM (TSyntax `term) :=
  match ps.toList with
  | [] => `(True)
  | p :: rest => rest.foldlM (fun acc q => `($acc ∧ $q)) p

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
  -- A loop that `return`s/`break`s threads an early-return state; its invariant is supplied via
  -- `Invariant.withEarlyReturnNewDo` (the new `do` elaborator uses `Prod`, not `MProd`). For the
  -- `True` postcondition a trivial pair discharges it.
  if li.hasEarlyExit then
    return ← `(Invariant.withEarlyReturnNewDo (onReturn := fun _ _ => ⌜True⌝) (onContinue := fun _ _ => ⌜True⌝))
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
  if li.accumulators.isEmpty then
    `(⇓ $cur => ⌜$body⌝)
  else
    -- mvcgen threads the loop state as a right-nested `MProd` whose `.fst` is the *last*-declared
    -- mutable variable, i.e. the tuple is in **reverse** declaration order.
    let accIdents := li.accumulators.reverse.map (fun s => mkIdent s.toName)
    `(⇓⟨$cur, $accIdents,*⟩ => ⌜$body⌝)

/-- Build the monadic spec theorem `⦃⌜Requires⌝⦄ fn params ⦃⇓ _ => ⌜True⌝⦄` proven by
`mvcgen [fn] invariants …` + a trailing `taste?`. Only the precondition is lifted from `Requires`/
`Assume`; the postcondition stays `True` (`Ensures`/`Assert` are proved as in-body checkpoints). -/
def buildMonadicSpec (thmName fnName : TSyntax `ident) (paramIdents : Array (TSyntax `ident))
    (info : MonadicContract) : PygenM (TSyntax `command) := withFreshVariables do
  for p in paramIdents do addVar p.getId
  let preProps ← info.requires.mapM (fun r => withPropCondition true (getCode r `term))
  let pre ← conjoin preProps
  let bullets ← info.loops.mapM buildBullet
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
  let mv ← if bullets.isEmpty then
      `(tactic| mvcgen [$lemmas,*])
    else
      `(tactic| mvcgen [$lemmas,*] invariants $[· $bullets:term]*)

  -- POSTCONDITION. With no `Result()`-bearing `Ensures` the postcondition stays `True` (any plain
  -- `Ensures`/`Assert` is proved as an in-body checkpoint instead). When the user wrote an
  -- `Ensures(Result() …)`, those args are collected into `info.ensures` (a statement about the return
  -- value), so we lift them into the spec *statement* (Nagini-style, modular `@[spec]` reuse): bind the
  -- returned variable as the result, lower each `Ensures` with `Result()` rewritten to that binder, and
  -- tag the theorem `@[spec]`.
  if info.ensures.isEmpty then
    `(command| theorem $thmName :
        ⦃⌜$pre⌝⦄ $fnName $paramIdents* ⦃⇓ _ => ⌜True⌝⦄ := by
          $mv:tactic
          taste?)
  else
    let retId := info.retName.getD "result"
    let retBinder := mkIdent retId.toName
    addVar retId.toName  -- so `Result()` (rewritten to the `retId` `Name`) lowers to the binder
    let postProps ← info.ensures.mapM
      (fun e => withPropCondition true (getCode (substResult retId e) `term))
    let post ← conjoin postProps
    `(command| @[spec] theorem $thmName :
        ⦃⌜$pre⌝⦄ $fnName $paramIdents* ⦃⇓ $retBinder => ⌜$post⌝⦄ := by
          $mv:tactic
          taste?)

end PastaLean

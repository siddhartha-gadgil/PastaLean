import PastaLean.PyVerify.Refute.Solve

/-!
# SMT models as refute candidates

`smtSolve` hands guards ∧ ¬body, after the unfolding `solveObligation` does, to an external SMT solver
(z3 or cvc5, SMT-LIB 2 over a pipe). Nothing the solver says is trusted:

* `sat`: its model becomes a witness that `runTarget` judges in both worlds and certifies with
  `refute_at`, exactly like a `grind` model;
* `unsat`: reported, never counted as a proof (that needs reconstruction, see `docs/smt.md`).

The translation over-approximates: a subterm outside the fragment (linear and nonlinear `Int`/`Nat`/`ℚ`
arithmetic with Lean's and Python's division conventions, `Bool`/`Prop` connectives, `if`, and `String`
length / concatenation / prefix / suffix / indexing) becomes a fresh constant, so a model may be
spurious but is never lost to an untranslatable side condition.

The solver binary is `$PASTALEAN_SMT` (a `z3` or `cvc5` executable), else `z3` then `cvc5` on `PATH`
or in `~/.local/bin`. `$PASTALEAN_SMT_DUMP=<dir>` saves each script there.
-/

namespace PastaLean.Refute.Smt

open Lean Meta Elab

inductive Srt where
  | int | bool | str | real
  deriving BEq, Inhabited

def Srt.name : Srt → String
  | .int => "Int" | .bool => "Bool" | .str => "String" | .real => "Real"

structure St where
  decls : Array String := #[]
  /-- SMT symbol, the binder's user name, its sort. -/
  consts : Array (String × Name × Srt) := #[]
  fvars : Std.HashMap FVarId String := {}
  atoms : Array (Expr × String) := #[]
  side : Array String := #[]
  fresh : Nat := 0

abbrev M := StateT St MetaM

/-- The sort of a term of type `ty` (`Nat` is an `Int` kept non-negative). -/
def sortOfType (ty : Expr) : MetaM (Option Srt) := do
  let ty ← whnfD (← instantiateMVars ty)
  if ty.isProp then return some .bool
  return match ty.getAppFn.constName? with
    | some ``Int | some ``Nat => some .int
    | some ``Bool => some .bool
    | some ``String => some .str
    | some ``Rat => some .real
    | _ => none

def isNatType (ty : Expr) : MetaM Bool := do
  return (← whnfD (← instantiateMVars ty)).isConstOf ``Nat

def freshSym (pfx : String) : M String := do
  let s ← get
  set { s with fresh := s.fresh + 1 }
  return s!"{pfx}{s.fresh}"

def declare (sym : String) (srt : Srt) (nat : Bool) : M Unit := do
  modify fun s => { s with decls := s.decls.push s!"(declare-const {sym} {srt.name})" }
  if nat then modify fun s => { s with side := s.side.push s!"(>= {sym} 0)" }

/-- An opaque subterm as a constant, shared between equal occurrences. -/
def atom (e : Expr) (srt : Srt) : M String := do
  if let some (_, sym) := (← get).atoms.find? (·.1 == e) then return sym
  let sym ← freshSym "a"
  declare sym srt (← isNatType (← inferType e))
  modify fun s => { s with atoms := s.atoms.push (e, sym) }
  return sym

def strLit (s : String) : String := Id.run do
  let mut out := "\""
  for c in s.toList do
    if c == '"' then out := out ++ "\"\""
    else if c.toNat ≥ 32 && c.toNat < 127 && c != '\\' then out := out.push c
    else out := out ++ s!"\\u\{{String.ofList (Nat.toDigits 16 c.toNat)}}"
  return out ++ "\""

def natLit? (e : Expr) : Option Nat :=
  match e with
  | .lit (.natVal n) => some n
  | _ => if e.isAppOfArity ``OfNat.ofNat 3 then
      match e.getArg! 1 with
      | .lit (.natVal n) => some n
      | _ => none
    else none

def ite' (c t e : String) : String := s!"(ite {c} {t} {e})"

/-- Python's `a % b` on ints (sign of the divisor; `a` when `b = 0`, as `pyMod` returns). -/
def pyModSmt (a b : String) : String :=
  ite' s!"(= {b} 0)" a (ite' s!"(or (> {b} 0) (= (mod {a} {b}) 0))" s!"(mod {a} {b})" s!"(+ (mod {a} {b}) {b})")

/-- Floor division (`Int.fdiv`, Python `//`; `0` when `b = 0`). -/
def fdivSmt (a b : String) : String :=
  ite' s!"(= {b} 0)" "0" (ite' s!"(or (> {b} 0) (= (mod {a} {b}) 0))" s!"(div {a} {b})" s!"(- (div {a} {b}) 1)")

mutual

/-- `e` as an SMT term of its own sort; an untranslatable subterm of a supported sort becomes an atom.
`none` only when `e`'s sort is unsupported. -/
partial def tr (e : Expr) (fuel : Nat := 6) : M (Option String) := do
  let e ← instantiateMVars e
  let ty ← inferType e
  let some srt ← sortOfType ty | return none
  let nat ← isNatType ty
  if let some s ← trCore e srt nat then return some s
  -- an unknown head: unfold it (instances included) and retry, else keep it opaque
  if fuel > 0 && e.getAppFn.isConst then
    let e'? ← try
        match ← unfoldProjInst? e with
        | some e' => pure (some e')
        | none => withTransparency .default (unfoldDefinition? e)
      catch _ => pure none
    if let some e' := e'? then return ← tr (← whnfCore e') (fuel - 1)
  return some (← atom e srt)

partial def tr! (e : Expr) : M String := do
  match ← tr e with
  | some s => return s
  | none => throwError "smt: unsupported sort"

partial def trCore (e : Expr) (srt : Srt) (nat : Bool) : M (Option String) := do
  if let some n := natLit? e then
    return some (if srt == .real then s!"{n}.0" else toString n)
  match e with
  | .lit (.strVal s) => return some (strLit s)
  | .fvar id =>
    if let some sym := (← get).fvars[id]? then return some sym
    let d ← id.getDecl
    if let some v := d.value? then return ← tr v
    let sym ← freshSym "x"
    declare sym srt nat
    modify fun s => { s with fvars := s.fvars.insert id sym, consts := s.consts.push (sym, d.userName, srt) }
    return some sym
  | .mdata _ b => return ← tr b
  | .letE _ _ v b _ => return ← tr (b.instantiate1 v)
  | .forallE _ d b _ =>
    if !b.hasLooseBVars && (← isProp d) && (← isProp b) then
      let some a ← tr d | return none
      let some c ← tr b | return none
      return some s!"(=> {a} {c})"
    return none
  | _ => pure ()
  let fn := e.getAppFn
  let args := e.getAppArgs
  let some c := fn.constName? | return none
  let a (i : Nat) : M String := tr! args[i]!
  let bin (op : String) (i j : Nat) : M (Option String) := do return some s!"({op} {← a i} {← a j})"
  let n := args.size
  match c, n with
  | ``True, 0 | ``Bool.true, 0 => return some "true"
  | ``False, 0 | ``Bool.false, 0 => return some "false"
  | ``Not, 1 | ``not, 1 => return some s!"(not {← a 0})"
  | ``And, 2 | ``and, 2 => bin "and" 0 1
  | ``Or, 2 | ``or, 2 => bin "or" 0 1
  | ``Iff, 2 => bin "=" 0 1
  | ``xor, 2 => bin "xor" 0 1
  | ``Decidable.decide, 2 => return some (← a 0)
  | ``Eq, 3 | ``BEq.beq, 4 | ``Ne, 3 | ``bne, 4 =>
    let (l, r) := if n == 3 then (args[1]!, args[2]!) else (args[2]!, args[3]!)
    -- `==` is equality only on the carriers this fragment knows
    let some _ ← sortOfType (← inferType l) | return none
    let some x ← tr l | return none
    let some y ← tr r | return none
    let eq := s!"(= {x} {y})"
    return some (if c == ``Ne || c == ``bne then s!"(not {eq})" else eq)
  | ``LT.lt, 4 => bin "<" 2 3
  | ``LE.le, 4 => bin "<=" 2 3
  | ``GT.gt, 4 => bin ">" 2 3
  | ``GE.ge, 4 => bin ">=" 2 3
  | ``ite, 5 | ``cond, 4 =>
    let (ci, ti, ei) := if c == ``ite then (1, 3, 4) else (1, 2, 3)
    return some (ite' (← a ci) (← a ti) (← a ei))
  | ``dite, 5 =>
    match args[3]!, args[4]! with
    | .lam _ _ t _, .lam _ _ f _ =>
      if t.hasLooseBVars || f.hasLooseBVars then return none
      return some (ite' (← a 1) (← tr! t) (← tr! f))
    | _, _ => return none
  | ``Neg.neg, 3 | ``Int.neg, 1 => return some s!"(- {← a (n - 1)})"
  | ``HAdd.hAdd, 6 | ``Int.add, 2 | ``Nat.add, 2 => bin "+" (n - 2) (n - 1)
  | ``HMul.hMul, 6 | ``Int.mul, 2 | ``Nat.mul, 2 => bin "*" (n - 2) (n - 1)
  | ``HSub.hSub, 6 | ``Int.sub, 2 | ``Nat.sub, 2 =>
    let x ← a (n - 2)
    let y ← a (n - 1)
    return some (if nat then ite' s!"(>= {x} {y})" s!"(- {x} {y})" "0" else s!"(- {x} {y})")
  | ``HDiv.hDiv, 6 | ``Int.ediv, 2 | ``Nat.div, 2 =>
    let x ← a (n - 2)
    let y ← a (n - 1)
    return some (if srt == .real then ite' s!"(= {y} 0.0)" "0.0" s!"(/ {x} {y})"
      else ite' s!"(= {y} 0)" "0" s!"(div {x} {y})")
  | ``HMod.hMod, 6 | ``Int.emod, 2 | ``Nat.mod, 2 =>
    if srt == .real then return none
    let x ← a (n - 2)
    let y ← a (n - 1)
    return some (ite' s!"(= {y} 0)" x s!"(mod {x} {y})")
  | ``Int.fdiv, 2 => return some (fdivSmt (← a 0) (← a 1))
  | ``PastaLean.pyMod, 2 => return some (pyModSmt (← a 0) (← a 1))
  | ``HPow.hPow, 6 =>
    let some k := natLit? args[5]! | return none
    if k > 8 then return none
    let x ← a 4
    return some (if k == 0 then (if srt == .real then "1.0" else "1")
      else if k == 1 then x else s!"(* {" ".intercalate (List.replicate k x)})")
  | ``Nat.cast, 3 | ``NatCast.natCast, 3 | ``Int.cast, 3 | ``IntCast.intCast, 3 | ``Int.ofNat, 1 =>
    let x ← a (n - 1)
    return some (if srt == .real then s!"(to_real {x})" else x)
  | ``Int.toNat, 1 => let x ← a 0; return some (ite' s!"(>= {x} 0)" x "0")
  | ``Int.natAbs, 1 => let x ← a 0; return some (ite' s!"(>= {x} 0)" x s!"(- {x})")
  | ``abs, _ => let x ← a (n - 1); return some (ite' s!"(>= {x} {if srt == .real then "0.0" else "0"})" x s!"(- {x})")
  | ``Max.max, 4 => let x ← a 2; let y ← a 3; return some (ite' s!"(>= {x} {y})" x y)
  | ``Min.min, 4 => let x ← a 2; let y ← a 3; return some (ite' s!"(<= {x} {y})" x y)
  -- strings
  | ``String.length, 1 => return some s!"(str.len {← a 0})"
  | ``HAppend.hAppend, 6 => if srt == .str then bin "str.++" 4 5 else return none
  | ``String.append, 2 => bin "str.++" 0 1
  | ``String.startsWith, 2 => return some s!"(str.prefixof {← a 1} {← a 0})"
  | ``String.endsWith, 2 => return some s!"(str.suffixof {← a 1} {← a 0})"
  | ``String.isPrefixOf, 2 => bin "str.prefixof" 0 1
  | ``PastaLean.pyStringStartswith, 4 =>
    if args[2]!.isAppOf ``Option.none && args[3]!.isAppOf ``Option.none then
      return some s!"(str.prefixof {← a 1} {← a 0})"
    return none
  | ``PastaLean.pyStringEndswith, 4 =>
    if args[2]!.isAppOf ``Option.none && args[3]!.isAppOf ``Option.none then
      return some s!"(str.suffixof {← a 1} {← a 0})"
    return none
  | ``PastaLean.pyStrContainsSubstr, 2 => bin "str.contains" 0 1
  | ``PastaLean.pyStringReplace, 3 => return some s!"(str.replace_all {← a 0} {← a 1} {← a 2})"
  | ``PastaLean.pyStringFind, 4 =>
    let s ← a 0
    if natLit? args[2]! != some 0 || (← a 3) != s!"(str.len {s})" then return none
    return some s!"(str.indexof {s} {← a 1} 0)"
  | ``PastaLean.pyStringSlice, 3 =>
    let s ← a 0
    let len := s!"(str.len {s})"
    -- Python's clamping of a slice bound into `[0, len]`
    let idx (o : Expr) (dflt : String) : M (Option String) := do
      if o.isAppOfArity ``Option.none 1 then return some dflt
      if o.isAppOfArity ``Option.some 2 then
        let i ← tr! (o.getArg! 1)
        return some (ite' s!"(< {i} 0)" (ite' s!"(< (+ {len} {i}) 0)" "0" s!"(+ {len} {i})")
          (ite' s!"(> {i} {len})" len i))
      return none
    let some lo ← idx args[1]! "0" | return none
    let some hi ← idx args[2]! len | return none
    return some s!"(str.substr {s} {lo} (- {hi} {lo}))"
  | ``PastaLean.pyStringGetItemStr, 2 =>
    let s ← a 0
    let i ← a 1
    return some (ite' s!"(< {i} 0)" s!"(str.at {s} (+ (str.len {s}) {i}))" s!"(str.at {s} {i})")
  | _, _ => return none

end

/-- The script: every hypothesis of `g` that translates (an untranslatable one is dropped), then a
`get-value` of the constants standing for the obligation's inputs. -/
def script (g : MVarId) : MetaM (Option (String × Array (String × Name × Srt))) := g.withContext do
  let run : M (Array String) := do
    let mut asserts := #[]
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      if !(← isProp d.type) then continue
      try
        if let some s ← tr d.type then asserts := asserts.push s!"(assert {s})"
      catch _ => pure ()
    return asserts
  let (asserts, st) ← run.run {}
  if asserts.isEmpty then return none
  let ins := st.consts
  let notes ← st.atoms.mapM fun (e, sym) => do
    return s!"; {sym} := {(toString (← ppExpr e)).replace "\n" " " |>.take 200}"
  let body := #["(set-option :produce-models true)", "(set-logic ALL)"] ++ notes ++ st.decls ++
    st.side.map (s!"(assert {·})") ++ asserts ++ #["(check-sat)"] ++
    (if ins.isEmpty then #[] else #[s!"(get-value ({" ".intercalate (ins.toList.map (·.1))}))"]) ++ #["(exit)"]
  return some ("\n".intercalate body.toList, ins)

/-! ### Talking to the solver -/

inductive SExp where
  | atom (s : String)
  | str (s : String)
  | list (xs : List SExp)
  deriving Inhabited

partial def parseSExps (cs : List Char) (acc : Array SExp := #[]) : Array SExp × List Char :=
  match cs with
  | [] => (acc, [])
  | c :: rest =>
    if c.isWhitespace then parseSExps rest acc
    else if c == '(' then
      let (xs, rest') := parseSExps rest
      parseSExps rest' (acc.push (.list xs.toList))
    else if c == ')' then (acc, rest)
    else if c == '"' then
      let rec str (cs : List Char) (out : String) : String × List Char :=
        match cs with
        | '"' :: '"' :: r => str r (out.push '"')
        | '"' :: r => (out, r)
        | x :: r => str r (out.push x)
        | [] => (out, [])
      let (s, rest') := str rest ""
      parseSExps rest' (acc.push (.str s))
    else
      let tok := (c :: rest).takeWhile fun x => !x.isWhitespace && x != '(' && x != ')'
      parseSExps ((c :: rest).drop tok.length) (acc.push (.atom (String.ofList tok)))

/-- `\u{XXXX}` / `\uXXXX` escapes of an SMT-LIB string literal. -/
partial def unescape (cs : List Char) (out : String := "") : String :=
  match cs with
  | '\\' :: 'u' :: '{' :: r =>
    let hex := r.takeWhile (· != '}')
    let v := hex.foldl (fun n d => n * 16 + (if d.isDigit then d.toNat - 48 else d.toLower.toNat - 87)) 0
    unescape (r.drop (hex.length + 1)) (out.push (Char.ofNat v))
  | '\\' :: 'u' :: a :: b :: c :: d :: r =>
    if [a, b, c, d].all Char.isHexDigit then
      let v := [a, b, c, d].foldl (fun n x => n * 16 + (if x.isDigit then x.toNat - 48 else x.toLower.toNat - 87)) 0
      unescape r (out.push (Char.ofNat v))
    else unescape (a :: b :: c :: d :: r) (out ++ "\\u")
  | x :: r => unescape r (out.push x)
  | [] => out

def decimal? (s : String) : Option Rat :=
  match s.splitOn "." with
  | [i] => i.toNat?.map fun k => (k : Rat)
  | [i, f] => do
    let iv ← i.toNat?
    let fv ← if f.isEmpty then some 0 else f.toNat?
    return (iv : Rat) + (fv : Rat) / (10 ^ f.length : Nat)
  | _ => none

partial def numVal? : SExp → Option Rat
  | .atom s => decimal? s
  | .list [.atom "-", x] => (numVal? x).map (- ·)
  | .list [.atom "/", x, y] => do let a ← numVal? x; let b ← numVal? y; return a / b
  | _ => none

inductive Val where
  | num (q : Rat)
  | bool (b : Bool)
  | str (s : String)

def val? : SExp → Option Val
  | .atom "true" => some (.bool true)
  | .atom "false" => some (.bool false)
  | .str s => some (.str (unescape s.toList))
  | e => (numVal? e).map .num

/-- The solver to run: `(path, is-cvc5)`. -/
def findSolver : IO (Option (String × Bool)) := do
  let isCvc5 (p : String) := (System.FilePath.mk p).fileName.any (·.startsWith "cvc5")
  if let some p ← IO.getEnv "PASTALEAN_SMT" then
    if !p.isEmpty then return some (p, isCvc5 p)
  let home := (← IO.getEnv "HOME").getD ""
  let path := ((← IO.getEnv "PATH").getD "").splitOn ":" ++ [s!"{home}/.local/bin"]
  for exe in ["z3", "cvc5"] do
    for dir in path do
      let p := System.FilePath.mk dir / exe
      if ← p.pathExists then return some (p.toString, exe == "cvc5")
  return none

/-- Run the solver on `script` with a `ms` budget: its first answer line and the rest of its output. -/
def runSolver (script : String) (ms : Nat) : IO (Except String (String × String)) := do
  let some (exe, cvc5) ← findSolver | return .error "no SMT solver (set PASTALEAN_SMT or install z3/cvc5)"
  let args := if cvc5 then #["--lang=smt2", s!"--tlimit={ms}", "--strings-exp"]
    else #["-in", "-smt2", s!"-t:{ms}", s!"-T:{ms / 1000 + 1}"]
  let child ← IO.Process.spawn { cmd := exe, args, stdin := .piped, stdout := .piped, stderr := .null }
  let (stdin, child) ← child.takeStdin
  stdin.putStr script
  stdin.flush
  let out ← child.stdout.readToEnd
  discard child.wait
  let ls := out.splitOn "\n"
  return .ok ((ls.headD "").trimAscii.toString, "\n".intercalate (ls.drop 1))

inductive SmtResult where
  /-- A model of the inputs: `(binder user name, value)`. -/
  | sat (vals : Array (Name × Val))
  | unsat
  | unknown (why : String)

instance : ToString Val where
  toString
    | .num q => toString q
    | .bool b => toString b
    | .str s => s!"{repr s}"

/-- Translate guards ∧ ¬body of `ty` (unfolded as for `grind`) and ask the solver for a model. -/
def smtSolve (ty : Expr) (ms : Nat := 2000) (dump : Option (IO.Ref String) := none) : TermElabM SmtResult := do
  try
    withObligation ty fun ob => do
      let defs ← userDefs (#[ob.body] ++ (← ob.guards.mapM inferType))
      withLocalDeclD `hneg (mkNot ob.body) fun _ => do
        let goal ← mkFreshExprMVar (mkConst ``False)
        let lemmas ← (defs.toList ++ operatorUnfolds).filterM (fun n => return (← getEnv).contains n)
        let ids : Array (TSyntax `Lean.Parser.Tactic.simpLemma) ←
          lemmas.toArray.mapM fun n => `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):ident)
        let simpStx ← `(tactic| simp only [$ids,*] at *)
        let goals ← try Term.TermElabM.run' (Tactic.run goal.mvarId! (Tactic.evalTactic simpStx))
          catch _ => pure [goal.mvarId!]
        -- simp closed it: no input violates the obligation (a Lean proof, not the solver's word)
        let some g := goals.head? | return .unsat
        let some (src, ins) ← script g | return .unknown "nothing to translate"
        if let some r := dump then r.set src
        if let some dir ← IO.getEnv "PASTALEAN_SMT_DUMP" then
          IO.FS.writeFile (System.FilePath.mk dir / s!"{hash src}.smt2") src
        match ← runSolver src ms with
        | .error e => return .unknown e
        | .ok ("sat", rest) =>
          let (sexps, _) := parseSExps rest.toList
          let pairs : List (String × Val) := match sexps[0]? with
            | some (SExp.list ps) => ps.filterMap fun
                | SExp.list [SExp.atom s, v] => (val? v).map (s, ·)
                | _ => none
            | _ => []
          return .sat (ins.filterMap fun (sym, n, _) => (pairs.find? (·.1 == sym)).map fun (_, v) => (n, v))
        | .ok ("unsat", _) => return .unsat
        | .ok (other, _) => return .unknown s!"solver: {other}"
  catch e => return .unknown (← e.toMessageData.toString)

/-- A model as a witness for the binders `names`: numbers through `modelWitness`, then `Bool` and
`String` binders from the model. -/
def smtWitness (names : Array (Name × Expr)) (vals : Array (Name × Val)) : MetaM (Option (List PyLit)) := do
  let nums := vals.filterMap fun | (n, .num q) => some (n, q) | _ => none
  let some ws ← modelWitness names nums | return none
  let find (n : Name) := (vals.find? (·.1.eraseMacroScopes == n.eraseMacroScopes)).map (·.2)
  return some ((names.toList.zip ws).map fun ((n, _), w) =>
    match w, find n with
    | .bool _, some (.bool b) => .bool b
    | .str _, some (.str s) => .str s
    | w, _ => w)

/-- The SMT step of a refute target: its report and, on `sat`, the witness to judge. -/
def smtStep (ty : Expr) (ms : Nat) : TermElabM (Json × Option (List PyLit)) := do
  let t0 ← IO.monoMsNow
  let r ← smtSolve ty ms
  let dt := (← IO.monoMsNow) - t0
  match r with
  | .sat vals =>
    let shown := Json.mkObj (vals.toList.map fun (n, v) => (n.eraseMacroScopes.toString, toJson (toString v)))
    let ws ← smtWitness (← obligationBinders ty) vals
    return (Json.mkObj [("status", toJson (if ws.isSome then "model" else "model-unusable")),
      ("model", shown), ("ms", toJson dt)], ws)
  -- `unsat` is the solver's claim only: it proves nothing here
  | .unsat => return (Json.mkObj [("status", toJson "unsat-untrusted"), ("ms", toJson dt)], none)
  | .unknown why => return (Json.mkObj [("status", toJson "unknown"), ("why", toJson (why.take 300)), ("ms", toJson dt)], none)

/-- `solvePlateau` with the solver in place of `grind`. -/
def smtPlateau (ty : Expr) (seed : List PyLit) (ms : Nat) : TermElabM (Option (List PyLit)) := do
  let (marked, orig) := (seed.mapM (markLeaves 8)).run #[]
  let some stmt ← (try plateauStatement ty seed marked orig.size catch _ => pure none) | return none
  match ← smtSolve stmt ms with
  | .sat m =>
    let vals := orig.mapIdx fun i n =>
      ((m.find? (·.1.eraseMacroScopes == Name.mkSimple s!"leaf{i}")).bind fun
        | (_, .num q) => some q.floor
        | _ => none).getD n
    return some (marked.map (unmarkLeaves vals))
  | _ => return none

end PastaLean.Refute.Smt

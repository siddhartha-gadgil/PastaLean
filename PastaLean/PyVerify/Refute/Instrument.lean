import PastaLean.PyVerify.Refute.Coverage

/-!
# The instrumented program

A copy of the definitions a property reaches (the translated program, `PastaLean.User`, and the
libraries it calls, `Libraries`) with a probe on every decision: the `Decidable` instance of each
`if`/`dite`/`decide` becomes `covDec id dist inst`, and each Bool comparison `a == b` becomes
`covBool id dist (a == b)`. Probes return the decision unchanged, so the copy computes what the
original computes; it also reports which branches ran and how close each came to flipping.

A definition is copied only when its copy compiles on its own: recursive definitions (compiled from
equations the environment does not keep), matchers, and `implemented_by`/`extern` definitions are
called as they are.
-/

namespace PastaLean.Refute

open Lean Meta

structure InstrState where
  done : Std.HashMap Name Name := {}
  /-- Copies named but not yet built: original, copy, the code to instrument. -/
  queue : Array (Name × Name × DefinitionVal) := #[]
  nextId : Nat := 0
  budget : Nat := 400

abbrev InstrM := StateRefT InstrState MetaM

/-- Copies get a fresh suffix per instrumentation, so repeated runs in one environment do not clash. -/
initialize instrRound : IO.Ref Nat ← IO.mkRef 0

def scalarKind? (α : Expr) : Option Name :=
  match α.constName? with
  | some n => if [``Int, ``Nat, ``String, ``Char, ``Float].contains n then some n else none
  | none => none

/-- `distEq*` / `distLt*` for operands of a scalar type, or `none`. -/
def cmpDist? (rel : Name) (α a b : Expr) : Option Expr :=
  let int (x : Expr) : Expr := if α.isConstOf ``Nat then mkApp (mkConst ``Int.ofNat) x else x
  match scalarKind? α, rel with
  | some ``String, ``Eq => some (mkApp2 (mkConst ``distEqStr) a b)
  | some ``Float, r =>
      if r == ``Eq then some (mkApp2 (mkConst ``distEqFloat) a b)
      else if r == ``LT.lt then some (mkApp2 (mkConst ``distLtFloat) a b)
      else if r == ``LE.le then some (mkApp2 (mkConst ``distLeFloat) a b)
      else none
  | some ``Char, ``Eq => some (mkApp2 (mkConst ``distEqChar) a b)
  | some ``Int, r | some ``Nat, r =>
      if r == ``Eq then some (mkApp2 (mkConst ``distEqInt) (int a) (int b))
      else if r == ``LT.lt then some (mkApp2 (mkConst ``distLtInt) (int a) (int b))
      else if r == ``LE.le then some (mkApp2 (mkConst ``distLeInt) (int a) (int b))
      else none
  | _, _ => none

mutual

/-- Distances of the proposition `p` (decided by `inst`). -/
partial def propDist (p inst : Expr) : Expr :=
  let generic := mkApp (mkConst ``distBool) (mkApp2 (mkConst ``decide) p inst)
  let args := p.getAppArgs
  match p.getAppFn.constName? with
  | some ``Eq =>
      if args.size == 3 && args[0]!.isConstOf ``Bool && args[2]!.isConstOf ``Bool.true then boolDist args[1]!
      else if args.size == 3 && args[0]!.isConstOf ``Bool && args[2]!.isConstOf ``Bool.false then
        mkApp (mkConst ``distNot) (boolDist args[1]!)
      else if args.size == 3 then (cmpDist? ``Eq args[0]! args[1]! args[2]!).getD generic
      else generic
  | some ``Ne =>
      if args.size == 3 then ((cmpDist? ``Eq args[0]! args[1]! args[2]!).map (mkApp (mkConst ``distNot))).getD generic
      else generic
  | some ``LT.lt => if args.size == 4 then (cmpDist? ``LT.lt args[0]! args[2]! args[3]!).getD generic else generic
  | some ``LE.le => if args.size == 4 then (cmpDist? ``LE.le args[0]! args[2]! args[3]!).getD generic else generic
  | some ``GT.gt => if args.size == 4 then (cmpDist? ``LT.lt args[0]! args[3]! args[2]!).getD generic else generic
  | some ``GE.ge => if args.size == 4 then (cmpDist? ``LE.le args[0]! args[3]! args[2]!).getD generic else generic
  | some ``Not =>
      -- `instDecidableNot` carries the inner instance as its last argument
      match inst.getAppFn.constName?, inst.getAppArgs.back? with
      | some ``instDecidableNot, some i => mkApp (mkConst ``distNot) (propDist args[0]! i)
      | _, _ => generic
  | some ``And | some ``Or =>
      match inst.getAppFn.constName?, inst.getAppArgs with
      | some ``instDecidableAnd, #[_, _, i, j] => mkApp2 (mkConst ``distAnd) (propDist args[0]! i) (.lam `_ (mkConst ``Unit) ((propDist args[1]! j).liftLooseBVars 0 1) .default)
      | some ``instDecidableOr, #[_, _, i, j] => mkApp2 (mkConst ``distOr) (propDist args[0]! i) (.lam `_ (mkConst ``Unit) ((propDist args[1]! j).liftLooseBVars 0 1) .default)
      | _, _ => generic
  | _ => generic

/-- Distances of the Bool `b` to `true` and to `false`. -/
partial def boolDist (b : Expr) : Expr :=
  let args := b.getAppArgs
  match b.getAppFn.constName? with
  | some ``BEq.beq => if args.size == 4 then (cmpDist? ``Eq args[0]! args[2]! args[3]!).getD (mkApp (mkConst ``distBool) b)
      else mkApp (mkConst ``distBool) b
  | some ``bne => if args.size == 4 then
        ((cmpDist? ``Eq args[0]! args[2]! args[3]!).map (mkApp (mkConst ``distNot))).getD (mkApp (mkConst ``distBool) b)
      else mkApp (mkConst ``distBool) b
  | some ``and => if args.size == 2 then mkApp2 (mkConst ``distAnd) (boolDist args[0]!) (.lam `_ (mkConst ``Unit) ((boolDist args[1]!).liftLooseBVars 0 1) .default)
      else mkApp (mkConst ``distBool) b
  | some ``or => if args.size == 2 then mkApp2 (mkConst ``distOr) (boolDist args[0]!) (.lam `_ (mkConst ``Unit) ((boolDist args[1]!).liftLooseBVars 0 1) .default)
      else mkApp (mkConst ``distBool) b
  | some ``not => if args.size == 1 then mkApp (mkConst ``distNot) (boolDist args[0]!) else mkApp (mkConst ``distBool) b
  | some ``decide => if args.size == 2 then propDist args[0]! args[1]! else mkApp (mkConst ``distBool) b
  | some ``PastaLean.pySetEq =>
      if args.size == 5 then mkAppN (mkConst ``distSetEq) args else mkApp (mkConst ``distBool) b
  | some ``PastaLean.pyContains =>
      -- `x in xs` over a list of ints or strings
      match args.toList with
      | [α, _, _, c, x] =>
          if α.isAppOfArity ``List 1 && α.appArg!.isConstOf ``Int then mkApp2 (mkConst ``distInListInt) c x
          else if α.isAppOfArity ``List 1 && α.appArg!.isConstOf ``String then mkApp2 (mkConst ``distInListStr) c x
          else mkApp (mkConst ``distBool) b
      | _ => mkApp (mkConst ``distBool) b
  | _ => mkApp (mkConst ``distBool) b

end

/-- `fun _ : Unit => d`, with `d`'s loose bound variables shifted under the new binder. -/
def distThunk (d : Expr) : Expr := .lam `_ (mkConst ``Unit) (d.liftLooseBVars 0 1) .default

def freshBranch : InstrM Nat := modifyGet fun s => (s.nextId, { s with nextId := s.nextId + 1 })

def probeDec (p inst : Expr) : InstrM Expr := do
  return mkApp4 (mkConst ``covDec) p (mkNatLit (← freshBranch)) (distThunk (propDist p inst)) inst

/-- Whether `c`'s value can be copied and compiled on its own. -/
def copyable (c : Name) (value : Expr) : MetaM Bool := do
  let env ← getEnv
  if !isProgramConst c then return false
  if (Compiler.getImplementedBy? env c).isSome || isExtern env c || (← isMatcher c) then return false
  return !value.getUsedConstants.any fun d =>
    isRecCore env d || d == ``WellFounded.fix || d.isStr && (d.getString! == "brecOn" || d.getString! == "binductionOn")

mutual

partial def instrExpr (e : Expr) : InstrM Expr := do
  match e with
  | .app .. =>
      let fn := e.getAppFn
      let args ← e.getAppArgs.mapM instrExpr
      let fn' ← match fn with
        | .const c us => pure (Expr.const (← instrConst c) us)
        | f => instrExpr f
      match fn.constName?, args.size with
      | some ``ite, 5 | some ``dite, 5 =>
          return mkAppN fn' (args.set! 2 (← probeDec args[1]! args[2]!))
      | some ``decide, 2 => return mkApp2 fn' args[0]! (← probeDec args[0]! args[1]!)
      | some ``BEq.beq, 4 =>
          let b := mkAppN fn' args
          if (scalarKind? args[0]!).isSome then
            return mkApp3 (mkConst ``covBool) (mkNatLit (← freshBranch)) (distThunk (boolDist b)) b
          if args[0]!.isAppOfArity ``List 1 then
            -- the list's element `BEq` is the argument of the list's own `BEq` (`List.instBEq`)
            let some elemInst := (if args[1]!.isAppOfArity ``List.instBEq 2 then some args[1]!.appArg! else none)
              | return b
            let d := mkAppN (mkConst ``distEqList) #[args[0]!.appArg!, elemInst, args[2]!, args[3]!]
            return mkApp3 (mkConst ``covBool) (mkNatLit (← freshBranch)) (distThunk d) b
          return b
      | some ``PastaLean.pySetEq, 5 | some ``PastaLean.pyContains, 5 =>
          let b := mkAppN fn' args
          return mkApp3 (mkConst ``covBool) (mkNatLit (← freshBranch)) (distThunk (boolDist b)) b
      | _, _ => return mkAppN fn' args
  | .const c us => return .const (← instrConst c) us
  | .lam n t b bi => return .lam n t (← instrExpr b) bi
  | .letE n t v b nd => return .letE n t (← instrExpr v) (← instrExpr b) nd
  | .mdata d b => return .mdata d (← instrExpr b)
  | .proj s i b => return .proj s i (← instrExpr b)
  | _ => return e

/-- The name of `c`'s instrumented copy (queued for `instrument` to build), or `c` itself when it
cannot be copied. A `partial def` is an opaque constant whose code is `c._unsafe_rec`, which names
itself for its recursive calls: both names map to the one copy, built from that code. -/
partial def instrConst (c : Name) : InstrM Name := do
  let c := match c with | .str p "_unsafe_rec" => p | c => c
  let s ← get
  if let some c' := s.done[c]? then return c'
  if s.budget == 0 then return c
  let some d := defBody? (← getEnv) c | return c
  if !(← copyable c d.value) then
    modify fun s => { s with done := s.done.insert c c }
    return c
  let c' := c.str s!"_cov{← instrRound.get}"
  modify fun s => { s with done := s.done.insert c c', queue := s.queue.push (c, c', d), budget := s.budget - 1 }
  return c'

end

/-- `es` with every reachable program/library definition replaced by its instrumented copy, and the
number of probes placed. The copies are `unsafe` and added as one mutual block (library code is
mutually recursive); if the block does not build, `es` come back uninstrumented. -/
def instrument (es : Array Expr) : MetaM (Array Expr × Nat) := do
  instrRound.modify (· + 1)
  let (out, st) ← (do
      let es' ← es.mapM instrExpr
      let mut decls : Array DefinitionVal := #[]
      let mut i := 0
      while i < (← get).queue.size do
        let (_, c', d) := (← get).queue[i]!
        decls := decls.push { d with name := c', value := ← instrExpr d.value, hints := .opaque, safety := .unsafe }
        i := i + 1
      return (es', decls)).run {}
  let (es', decls) := out
  if decls.isEmpty then return (es', st.nextId)
  let saved ← saveState
  try
    addDecl (.mutualDefnDecl decls.toList)
    compileDecls (decls.map (·.name))
    return (es', st.nextId)
  catch _ =>
    saved.restore
    return (es, 0)

end PastaLean.Refute

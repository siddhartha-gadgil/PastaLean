import PastaLean
import Libraries
import Std.Tactic.Do

open PastaLean
open Libraries
open Std.Do

set_option linter.all false
set_option mvcgen.warning false

set_option maxHeartbeats 800000

/-
2x2 matrix algebra + a discrete linear dynamical system.

A second, different-flavour stress test for the "decompose deep, wrap thin" recipe (cf. the 3D
vector model in `../orbital/orbital_model.py`): the leaves are the scalar entries of 2x2 matrix
operations -- determinant, trace, and the four entries of a matrix product -- and they compose
upward into the classical identities of linear algebra. `main` is the single monadic island: it
reads a 2x2 matrix and a vector and iterates the linear map x -> A x, printing the orbit and the
(conserved-up-to-det) quantities.

Everything with an `assert` is a *provable invariant*, transpiled to `theorem ... := by taste?`:

  * ring identities  -- determinant multiplicativity det(AB)=det(A)det(B), the adjugate inverse
                        A.adj(A)=det(A).I, the Cayley-Hamilton theorem A^2 - tr(A)A + det(A)I = 0,
                        trace cyclicity tr(AB)=tr(BA), det of the transpose / adjugate, scaling;
  * constrained laws -- a rotation matrix (c^2+s^2=1) has determinant 1 and preserves the norm.

Every entry is a polynomial over the rationals -- no transcendentals -- so `ring` / `nlinarith`
reach the proofs directly.
-/
-- ----------------------------------------------------------------------------------------------
-- Tier-0 leaves: scalar entries of 2x2 matrix operations.  A 2x2 matrix is its four entries
-- (a b ; c d); a product of A=(a b ; c d) and B=(e f ; g h) has the four entries below.
-- ----------------------------------------------------------------------------------------------
def det := fun (a : Rat) ↦ fun (b : Rat) ↦ fun (c : Rat) ↦ fun (d : Rat) ↦
  /-
  Determinant of (a b ; c d).
  -/
  a *ₚ d -ₚ b *ₚ c

attribute [simp, taste_ingr] det

def det'rn := fun (a : Float) ↦ fun (b : Float) ↦ fun (c : Float) ↦ fun (d : Float) ↦
  /-
  Determinant of (a b ; c d).
  -/
  a *ₚ d -ₚ b *ₚ c

def trace := fun (a : Rat) ↦ fun (b : Rat) ↦ fun (c : Rat) ↦ fun (d : Rat) ↦
  /-
  Trace of (a b ; c d).
  -/
  a +ₚ d

attribute [simp, taste_ingr] trace

def trace'rn := fun (a : Float) ↦ fun (b : Float) ↦ fun (c : Float) ↦ fun (d : Float) ↦
  /-
  Trace of (a b ; c d).
  -/
  a +ₚ d

def mul11 := fun (a : Rat) ↦ fun (b : Rat) ↦ fun (c : Rat) ↦ fun (d : Rat) ↦ fun (e : Rat) ↦ fun (f : Rat) ↦
  fun (g : Rat) ↦ fun (h : Rat) ↦
  /-
  (1,1) entry of A B.
  -/
  a *ₚ e +ₚ b *ₚ g

attribute [simp, taste_ingr] mul11

def mul11'rn := fun (a : Float) ↦ fun (b : Float) ↦ fun (c : Float) ↦ fun (d : Float) ↦ fun (e : Float) ↦
  fun (f : Float) ↦ fun (g : Float) ↦ fun (h : Float) ↦
  /-
  (1,1) entry of A B.
  -/
  a *ₚ e +ₚ b *ₚ g

def mul12 := fun (a : Rat) ↦ fun (b : Rat) ↦ fun (c : Rat) ↦ fun (d : Rat) ↦ fun (e : Rat) ↦ fun (f : Rat) ↦
  fun (g : Rat) ↦ fun (h : Rat) ↦
  /-
  (1,2) entry of A B.
  -/
  a *ₚ f +ₚ b *ₚ h

attribute [simp, taste_ingr] mul12

def mul12'rn := fun (a : Float) ↦ fun (b : Float) ↦ fun (c : Float) ↦ fun (d : Float) ↦ fun (e : Float) ↦
  fun (f : Float) ↦ fun (g : Float) ↦ fun (h : Float) ↦
  /-
  (1,2) entry of A B.
  -/
  a *ₚ f +ₚ b *ₚ h

def mul21 := fun (a : Rat) ↦ fun (b : Rat) ↦ fun (c : Rat) ↦ fun (d : Rat) ↦ fun (e : Rat) ↦ fun (f : Rat) ↦
  fun (g : Rat) ↦ fun (h : Rat) ↦
  /-
  (2,1) entry of A B.
  -/
  c *ₚ e +ₚ d *ₚ g

attribute [simp, taste_ingr] mul21

def mul21'rn := fun (a : Float) ↦ fun (b : Float) ↦ fun (c : Float) ↦ fun (d : Float) ↦ fun (e : Float) ↦
  fun (f : Float) ↦ fun (g : Float) ↦ fun (h : Float) ↦
  /-
  (2,1) entry of A B.
  -/
  c *ₚ e +ₚ d *ₚ g

def mul22 := fun (a : Rat) ↦ fun (b : Rat) ↦ fun (c : Rat) ↦ fun (d : Rat) ↦ fun (e : Rat) ↦ fun (f : Rat) ↦
  fun (g : Rat) ↦ fun (h : Rat) ↦
  /-
  (2,2) entry of A B.
  -/
  c *ₚ f +ₚ d *ₚ h

attribute [simp, taste_ingr] mul22

def mul22'rn := fun (a : Float) ↦ fun (b : Float) ↦ fun (c : Float) ↦ fun (d : Float) ↦ fun (e : Float) ↦
  fun (f : Float) ↦ fun (g : Float) ↦ fun (h : Float) ↦
  /-
  (2,2) entry of A B.
  -/
  c *ₚ f +ₚ d *ₚ h

-- ----------------------------------------------------------------------------------------------
-- Provable invariants: ring identities  (lone `assert` -> named `theorem`, closed by `ring`)
-- ----------------------------------------------------------------------------------------------
@[taste_ingr]
theorem det_multiplicative :
    ∀ (a : Rat),
      ∀ (b : Rat),
        ∀ (c : Rat),
          ∀ (d : Rat),
            ∀ (e : Rat),
              ∀ (f : Rat),
                ∀ (g : Rat),
                  ∀ (h : Rat),
                    det (mul11 a b c d e f g h) (mul12 a b c d e f g h) (mul21 a b c d e f g h)
                        (mul22 a b c d e f g h) =
                      det a b c d *ₚ det e f g h :=
  by intros; simp_all (config := { zetaDelta := true }) [taste_ingr]; pyany_cases <;> grind +locals

@[taste_ingr]
theorem trace_cyclic :
    ∀ (a : Rat),
      ∀ (b : Rat),
        ∀ (c : Rat),
          ∀ (d : Rat),
            ∀ (e : Rat),
              ∀ (f : Rat),
                ∀ (g : Rat),
                  ∀ (h : Rat),
                    mul11 a b c d e f g h +ₚ mul22 a b c d e f g h = mul11 e f g h a b c d +ₚ mul22 e f g h a b c d :=
  by intros; simp_all (config := { zetaDelta := true }) [taste_ingr]; pyany_cases <;> grind +locals

@[taste_ingr]
theorem det_transpose : ∀ (a : Rat), ∀ (b : Rat), ∀ (c : Rat), ∀ (d : Rat), det a c b d = det a b c d := by intros; simp_all (config := { zetaDelta := true }) [taste_ingr]; pyany_cases <;> grind +locals

@[taste_ingr]
theorem det_scale :
    ∀ (k : Rat),
      ∀ (a : Rat),
        ∀ (b : Rat), ∀ (c : Rat), ∀ (d : Rat), det (k *ₚ a) (k *ₚ b) (k *ₚ c) (k *ₚ d) = k *ₚ k *ₚ det a b c d :=
  by intros; simp_all (config := { zetaDelta := true }) [taste_ingr]; pyany_cases <;> grind +locals

@[taste_ingr]
theorem det_adjugate : ∀ (a : Rat), ∀ (b : Rat), ∀ (c : Rat), ∀ (d : Rat), det d (-b) (-c) a = det a b c d := by intros; simp_all (config := { zetaDelta := true }) [taste_ingr]; pyany_cases <;> grind +locals

@[taste_ingr]
theorem trace_additive :
    ∀ (a : Rat),
      ∀ (b : Rat),
        ∀ (c : Rat),
          ∀ (d : Rat),
            ∀ (e : Rat),
              ∀ (f : Rat),
                ∀ (g : Rat), ∀ (h : Rat), trace (a +ₚ e) (b +ₚ f) (c +ₚ g) (d +ₚ h) = trace a b c d +ₚ trace e f g h :=
  by intros; simp_all (config := { zetaDelta := true }) [taste_ingr]; pyany_cases <;> grind +locals

@[taste_ingr]
theorem adjugate_inverse_diag :
    ∀ (a : Rat), ∀ (b : Rat), ∀ (c : Rat), ∀ (d : Rat), mul11 a b c d d (-b) (-c) a = det a b c d := by intros; simp_all (config := { zetaDelta := true }) [taste_ingr]; pyany_cases <;> grind +locals

@[taste_ingr]
theorem adjugate_inverse_offdiag :
    ∀ (a : Rat), ∀ (b : Rat), ∀ (c : Rat), ∀ (d : Rat), mul12 a b c d d (-b) (-c) a = (0 : Int) := by intros; simp_all (config := { zetaDelta := true }) [taste_ingr]; pyany_cases <;> grind +locals

@[taste_ingr]
theorem cayley_hamilton_diag :
    ∀ (a : Rat),
      ∀ (b : Rat), ∀ (c : Rat), ∀ (d : Rat), mul11 a b c d a b c d -ₚ trace a b c d *ₚ a +ₚ det a b c d = (0 : Int) :=
  by intros; simp_all (config := { zetaDelta := true }) [taste_ingr]; pyany_cases <;> grind +locals

@[taste_ingr]
theorem cayley_hamilton_offdiag :
    ∀ (a : Rat), ∀ (b : Rat), ∀ (c : Rat), ∀ (d : Rat), mul12 a b c d a b c d -ₚ trace a b c d *ₚ b = (0 : Int) := by
  intros; simp_all (config := { zetaDelta := true }) [taste_ingr]; pyany_cases <;> grind +locals

-- ----------------------------------------------------------------------------------------------
-- Provable invariants: constrained laws  (`if`-guard -> hypotheses; ring / nlinarith)
-- ----------------------------------------------------------------------------------------------
@[taste_ingr]
theorem rotation_has_unit_det : ∀ (c : Rat), ∀ (s : Rat), c *ₚ c +ₚ s *ₚ s = (1 : Int) → det c (-s) s c = (1 : Int) :=
  by intros; simp_all (config := { zetaDelta := true }) [taste_ingr]

@[taste_ingr]
theorem rotation_preserves_norm :
    ∀ (c : Rat),
      ∀ (s : Rat),
        ∀ (x : Rat),
          ∀ (y : Rat),
            c *ₚ c +ₚ s *ₚ s = (1 : Int) →
              (c *ₚ x -ₚ s *ₚ y) *ₚ (c *ₚ x -ₚ s *ₚ y) +ₚ (s *ₚ x +ₚ c *ₚ y) *ₚ (s *ₚ x +ₚ c *ₚ y) = x *ₚ x +ₚ y *ₚ y :=
  by intros; simp_all (config := { zetaDelta := true }) [taste_ingr]; pyany_cases <;> grind +locals

@[taste_ingr]
theorem det_nonneg_of_symmetric_psd :
    ∀ (a : Rat), ∀ (b : Rat), ∀ (d : Rat), a *ₚ d ≥ b *ₚ b → det a b b d ≥ (0 : Int) := by intros; simp_all (config := { zetaDelta := true }) [taste_ingr]

-- ----------------------------------------------------------------------------------------------
-- EDGE: main -- iterate the linear map x -> A x (a discrete linear dynamical system); NOT proved
-- ----------------------------------------------------------------------------------------------
def main' :=
  ((do
      let mut a := PastaLean.pyRat (← (PastaLean.ProofMode.pyInputProof ""))
      let mut b := PastaLean.pyRat (← (PastaLean.ProofMode.pyInputProof ""))
      let mut c := PastaLean.pyRat (← (PastaLean.ProofMode.pyInputProof ""))
      let mut d := PastaLean.pyRat (← (PastaLean.ProofMode.pyInputProof ""))
      let mut x := PastaLean.pyRat (← (PastaLean.ProofMode.pyInputProof ""))
      let mut y := PastaLean.pyRat (← (PastaLean.ProofMode.pyInputProof ""))
      let mut nsteps : Int := PastaLean.pyInt (← (PastaLean.ProofMode.pyInputProof ""))
      let mut every : Int := PastaLean.pyInt (← (PastaLean.ProofMode.pyInputProof ""))
      let mut detA := det a b c d
      for step in (PastaLean.pyRange nsteps) do
        -- One step of the linear map (x, y) -> (a x + b y, c x + d y).
        let mut nx := a *ₚ x +ₚ b *ₚ y
        let mut ny := c *ₚ x +ₚ d *ₚ y
        x := nx
        y := ny
        if h_1 : step %ₚ every = (0 : Int) then 
          let _ ←
            PastaLean.ProofMode.pyPrintProof
                [pyPrintArg "S", pyPrintArg step, pyPrintArg x, pyPrintArg y, pyPrintArg detA]
        else
          let _ := ()) :
    PastaLean.ProofMode.PyProofM _)

attribute [simp] main'

def main''rn :=
  ((do
      let mut a := PastaLean.pyFloat (← (PastaLean.pyInputIO ""))
      let mut b := PastaLean.pyFloat (← (PastaLean.pyInputIO ""))
      let mut c := PastaLean.pyFloat (← (PastaLean.pyInputIO ""))
      let mut d := PastaLean.pyFloat (← (PastaLean.pyInputIO ""))
      let mut x := PastaLean.pyFloat (← (PastaLean.pyInputIO ""))
      let mut y := PastaLean.pyFloat (← (PastaLean.pyInputIO ""))
      let mut nsteps : Int := PastaLean.pyInt (← (PastaLean.pyInputIO ""))
      let mut every : Int := PastaLean.pyInt (← (PastaLean.pyInputIO ""))
      let mut detA := det'rn a b c d
      for step in (PastaLean.pyRange nsteps) do
        -- One step of the linear map (x, y) -> (a x + b y, c x + d y).
        let mut nx := a *ₚ x +ₚ b *ₚ y
        let mut ny := c *ₚ x +ₚ d *ₚ y
        x := nx
        y := ny
        if h_1 : step %ₚ every == (0 : Int) then 
          let _ ← pyPrintIO [pyPrintArg "S", pyPrintArg step, pyPrintArg x, pyPrintArg y, pyPrintArg detA]
        else
          let _ := ()) :
    IO _)

def main : IO Unit := do
  let inputText ← IO.getStdin >>= fun h => h.readToEnd
  let inputLines := String.splitOn inputText "\n"
  let inputStream : PastaLean.ProofMode.IOStream :=
    ⟨0, fun i => PastaLean.ProofMode.IOResult.success (List.getD inputLines i "")⟩
  let initState : PastaLean.ProofMode.IOState := ⟨inputStream, []⟩
  let (result, finalState) :=
    (((do
          let _ ← main'
          pure ()) :
        PastaLean.ProofMode.PyProofM Unit))
      initState
  let outputLines := finalState.output
  for line in outputLines do
    IO.print line
  match result with
  | .ok _ =>
    pure ()
  | .error err =>
    throw (IO.userError (toString err))

def main'rn : IO Unit := do
  let _ ← main''rn
  pure ()
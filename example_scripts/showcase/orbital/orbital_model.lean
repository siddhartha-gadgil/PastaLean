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
3D coupled two-body harmonic oscillator with a symplectic velocity-Verlet integrator.

The "decompose deep, wrap thin" recipe pushed harder than `pk_model.py`: a foundation of pure
3-vector algebra leaves (dot, cross, squared-norm) composes upward into the conserved quantities of
mechanics -- linear momentum, angular momentum, kinetic energy, spring potential -- and a
velocity-Verlet step that advances two masses joined by a Hooke spring (a linear, polynomial
restoring force, so the whole model stays exact-rational and provable). `main` is the only monadic
island: it reads the bodies' masses and phase-space state, integrates, and prints the conserved
quantities so you can watch them stay flat.

Everything with an `assert` is a *provable invariant*, transpiled to `theorem ... := by taste?`:

  * vector identities  -- bilinearity, antisymmetry, orthogonality of the cross product, the
                          Lagrange identity, parallelogram / polarization laws, the BAC-CAB rule;
  * physical laws      -- a central force exerts no torque (angular momentum is conserved), equal
                          and opposite spring forces conserve total momentum, kinetic and spring
                          energy are non-negative, Cauchy-Schwarz bounds the dot product.

Each is a single-expression Tier-0 term, so `ring` / `nlinarith` / `positivity` reach them directly.
No transcendentals (`sqrt`, `**0.5`) appear anywhere, so every quantity is a polynomial over the
rationals -- which is exactly what keeps the proofs in reach of the automation.
-/
-- ----------------------------------------------------------------------------------------------
-- Tier-0 vector-algebra leaves  (each one expression; provable, and everything below composes them)
-- ----------------------------------------------------------------------------------------------
def dot := fun (ax : Rat) ↦ fun (ay : Rat) ↦ fun (az : Rat) ↦ fun (bx : Rat) ↦ fun («by» : Rat) ↦ fun (bz : Rat) ↦
  /-
  Euclidean inner product a . b.
  -/
  ax *ₚ bx +ₚ ay *ₚ «by» +ₚ az *ₚ bz

attribute [simp, taste_ingr] dot

def dot'rn := fun (ax : Float) ↦ fun (ay : Float) ↦ fun (az : Float) ↦ fun (bx : Float) ↦ fun («by» : Float) ↦
  fun (bz : Float) ↦
  /-
  Euclidean inner product a . b.
  -/
  ax *ₚ bx +ₚ ay *ₚ «by» +ₚ az *ₚ bz

def cross_x := fun (ax : Rat) ↦ fun (ay : Rat) ↦ fun (az : Rat) ↦ fun (bx : Rat) ↦ fun («by» : Rat) ↦ fun (bz : Rat) ↦
  /-
  x-component of a x b.
  -/
  ay *ₚ bz -ₚ az *ₚ «by»

attribute [simp, taste_ingr] cross_x

def cross_x'rn := fun (ax : Float) ↦ fun (ay : Float) ↦ fun (az : Float) ↦ fun (bx : Float) ↦ fun («by» : Float) ↦
  fun (bz : Float) ↦
  /-
  x-component of a x b.
  -/
  ay *ₚ bz -ₚ az *ₚ «by»

def cross_y := fun (ax : Rat) ↦ fun (ay : Rat) ↦ fun (az : Rat) ↦ fun (bx : Rat) ↦ fun («by» : Rat) ↦ fun (bz : Rat) ↦
  /-
  y-component of a x b.
  -/
  az *ₚ bx -ₚ ax *ₚ bz

attribute [simp, taste_ingr] cross_y

def cross_y'rn := fun (ax : Float) ↦ fun (ay : Float) ↦ fun (az : Float) ↦ fun (bx : Float) ↦ fun («by» : Float) ↦
  fun (bz : Float) ↦
  /-
  y-component of a x b.
  -/
  az *ₚ bx -ₚ ax *ₚ bz

def cross_z := fun (ax : Rat) ↦ fun (ay : Rat) ↦ fun (az : Rat) ↦ fun (bx : Rat) ↦ fun («by» : Rat) ↦ fun (bz : Rat) ↦
  /-
  z-component of a x b.
  -/
  ax *ₚ «by» -ₚ ay *ₚ bx

attribute [simp, taste_ingr] cross_z

def cross_z'rn := fun (ax : Float) ↦ fun (ay : Float) ↦ fun (az : Float) ↦ fun (bx : Float) ↦ fun («by» : Float) ↦
  fun (bz : Float) ↦
  /-
  z-component of a x b.
  -/
  ax *ₚ «by» -ₚ ay *ₚ bx

def norm_sq := fun (ax : Rat) ↦ fun (ay : Rat) ↦ fun (az : Rat) ↦
  /-
  Squared Euclidean norm |a|^2 = a . a.
  -/
  ax *ₚ ax +ₚ ay *ₚ ay +ₚ az *ₚ az

attribute [simp, taste_ingr] norm_sq

def norm_sq'rn := fun (ax : Float) ↦ fun (ay : Float) ↦ fun (az : Float) ↦
  /-
  Squared Euclidean norm |a|^2 = a . a.
  -/
  ax *ₚ ax +ₚ ay *ₚ ay +ₚ az *ₚ az

def kinetic := fun (m : Rat) ↦ fun (vx : Rat) ↦ fun (vy : Rat) ↦ fun (vz : Rat) ↦
  /-
  Kinetic energy (1/2) m |v|^2.
  -/
  (0.5 : Rat) *ₚ m *ₚ norm_sq vx vy vz

attribute [simp, taste_ingr] kinetic

def kinetic'rn := fun (m : Float) ↦ fun (vx : Float) ↦ fun (vy : Float) ↦ fun (vz : Float) ↦
  /-
  Kinetic energy (1/2) m |v|^2.
  -/
  (0.5 : Float) *ₚ m *ₚ norm_sq'rn vx vy vz

def spring_energy := fun (k : Rat) ↦ fun (dx : Rat) ↦ fun (dy : Rat) ↦ fun (dz : Rat) ↦
  /-
  Hooke potential energy (1/2) k |d|^2 stored in a spring stretched by displacement d.
  -/
  (0.5 : Rat) *ₚ k *ₚ norm_sq dx dy dz

attribute [simp, taste_ingr] spring_energy

def spring_energy'rn := fun (k : Float) ↦ fun (dx : Float) ↦ fun (dy : Float) ↦ fun (dz : Float) ↦
  /-
  Hooke potential energy (1/2) k |d|^2 stored in a spring stretched by displacement d.
  -/
  (0.5 : Float) *ₚ k *ₚ norm_sq'rn dx dy dz

-- ----------------------------------------------------------------------------------------------
-- Provable invariants: vector identities  (lone `assert` -> named `theorem`, closed by `ring`)
-- ----------------------------------------------------------------------------------------------
@[taste_ingr]
theorem dot_commutes :
    ∀ (ax : Rat),
      ∀ (ay : Rat),
        ∀ (az : Rat), ∀ (bx : Rat), ∀ («by» : Rat), ∀ (bz : Rat), dot ax ay az bx «by» bz = dot bx «by» bz ax ay az :=
  by intros; simp_all (config := { zetaDelta := true }) [taste_ingr]; pyany_cases <;> grind +locals

@[taste_ingr]
theorem dot_additive :
    ∀ (ax : Rat),
      ∀ (ay : Rat),
        ∀ (az : Rat),
          ∀ (cx : Rat),
            ∀ (cy : Rat),
              ∀ (cz : Rat),
                ∀ (bx : Rat),
                  ∀ («by» : Rat),
                    ∀ (bz : Rat),
                      dot (ax +ₚ cx) (ay +ₚ cy) (az +ₚ cz) bx «by» bz =
                        dot ax ay az bx «by» bz +ₚ dot cx cy cz bx «by» bz :=
  by intros; simp_all (config := { zetaDelta := true }) [taste_ingr]; pyany_cases <;> grind +locals

@[taste_ingr]
theorem dot_homogeneous :
    ∀ (s : Rat),
      ∀ (ax : Rat),
        ∀ (ay : Rat),
          ∀ (az : Rat),
            ∀ (bx : Rat),
              ∀ («by» : Rat),
                ∀ (bz : Rat), dot (s *ₚ ax) (s *ₚ ay) (s *ₚ az) bx «by» bz = s *ₚ dot ax ay az bx «by» bz :=
  by intros; simp_all (config := { zetaDelta := true }) [taste_ingr]; pyany_cases <;> grind +locals

@[taste_ingr]
theorem cross_antisymmetric :
    ∀ (ax : Rat),
      ∀ (ay : Rat),
        ∀ (az : Rat),
          ∀ (bx : Rat), ∀ («by» : Rat), ∀ (bz : Rat), cross_x ax ay az bx «by» bz = -cross_x bx «by» bz ax ay az :=
  by intros; simp_all (config := { zetaDelta := true }) [taste_ingr]; pyany_cases <;> grind +locals

@[taste_ingr]
theorem cross_self_zero : ∀ (ax : Rat), ∀ (ay : Rat), ∀ (az : Rat), cross_x ax ay az ax ay az = (0 : Int) := by intros; simp_all (config := { zetaDelta := true }) [taste_ingr]; pyany_cases <;> grind +locals

@[taste_ingr]
theorem cross_perp_first :
    ∀ (ax : Rat),
      ∀ (ay : Rat),
        ∀ (az : Rat),
          ∀ (bx : Rat),
            ∀ («by» : Rat),
              ∀ (bz : Rat),
                dot ax ay az (cross_x ax ay az bx «by» bz) (cross_y ax ay az bx «by» bz) (cross_z ax ay az bx «by» bz) =
                  (0 : Int) :=
  by intros; simp_all (config := { zetaDelta := true }) [taste_ingr]; pyany_cases <;> grind +locals

@[taste_ingr]
theorem cross_perp_second :
    ∀ (ax : Rat),
      ∀ (ay : Rat),
        ∀ (az : Rat),
          ∀ (bx : Rat),
            ∀ («by» : Rat),
              ∀ (bz : Rat),
                dot bx «by» bz (cross_x ax ay az bx «by» bz) (cross_y ax ay az bx «by» bz)
                    (cross_z ax ay az bx «by» bz) =
                  (0 : Int) :=
  by intros; simp_all (config := { zetaDelta := true }) [taste_ingr]; pyany_cases <;> grind +locals

@[taste_ingr]
theorem lagrange_identity :
    ∀ (ax : Rat),
      ∀ (ay : Rat),
        ∀ (az : Rat),
          ∀ (bx : Rat),
            ∀ («by» : Rat),
              ∀ (bz : Rat),
                norm_sq (cross_x ax ay az bx «by» bz) (cross_y ax ay az bx «by» bz) (cross_z ax ay az bx «by» bz) +ₚ
                    dot ax ay az bx «by» bz *ₚ dot ax ay az bx «by» bz =
                  norm_sq ax ay az *ₚ norm_sq bx «by» bz :=
  by intros; simp_all (config := { zetaDelta := true }) [taste_ingr]; pyany_cases <;> grind +locals

@[taste_ingr]
theorem parallelogram_identity :
    ∀ (ax : Rat),
      ∀ (ay : Rat),
        ∀ (az : Rat),
          ∀ (bx : Rat),
            ∀ («by» : Rat),
              ∀ (bz : Rat),
                norm_sq (ax +ₚ bx) (ay +ₚ «by») (az +ₚ bz) +ₚ norm_sq (ax -ₚ bx) (ay -ₚ «by») (az -ₚ bz) =
                  (2.0 : Rat) *ₚ norm_sq ax ay az +ₚ (2.0 : Rat) *ₚ norm_sq bx «by» bz :=
  by intros; simp_all (config := { zetaDelta := true }) [taste_ingr]; pyany_cases <;> grind +locals

@[taste_ingr]
theorem polarization_identity :
    ∀ (ax : Rat),
      ∀ (ay : Rat),
        ∀ (az : Rat),
          ∀ (bx : Rat),
            ∀ («by» : Rat),
              ∀ (bz : Rat),
                (2.0 : Rat) *ₚ dot ax ay az bx «by» bz =
                  norm_sq (ax +ₚ bx) (ay +ₚ «by») (az +ₚ bz) -ₚ norm_sq ax ay az -ₚ norm_sq bx «by» bz :=
  by intros; simp_all (config := { zetaDelta := true }) [taste_ingr]; pyany_cases <;> grind +locals

@[taste_ingr]
theorem bac_cab_rule :
    ∀ (ax : Rat),
      ∀ (ay : Rat),
        ∀ (az : Rat),
          ∀ (bx : Rat),
            ∀ («by» : Rat),
              ∀ (bz : Rat),
                ∀ (cx : Rat),
                  ∀ (cy : Rat),
                    ∀ (cz : Rat),
                      cross_x ax ay az (cross_x bx «by» bz cx cy cz) (cross_y bx «by» bz cx cy cz)
                          (cross_z bx «by» bz cx cy cz) =
                        bx *ₚ dot ax ay az cx cy cz -ₚ cx *ₚ dot ax ay az bx «by» bz :=
  by intros; simp_all (config := { zetaDelta := true }) [taste_ingr]; pyany_cases <;> grind +locals

-- ----------------------------------------------------------------------------------------------
-- Provable invariants: non-negativity & bounds  (`if`-guard -> hypotheses; nlinarith / positivity)
-- ----------------------------------------------------------------------------------------------
@[taste_ingr]
theorem norm_sq_nonneg : ∀ (ax : Rat), ∀ (ay : Rat), ∀ (az : Rat), norm_sq ax ay az ≥ (0 : Int) := by intros; simp_all (config := { zetaDelta := true }) [taste_ingr]; nlinarith

@[taste_ingr]
theorem kinetic_nonneg :
    ∀ (m : Rat), ∀ (vx : Rat), ∀ (vy : Rat), ∀ (vz : Rat), m ≥ (0 : Int) → kinetic m vx vy vz ≥ (0 : Int) := by intros; simp_all (config := { zetaDelta := true }) [taste_ingr]; nlinarith

@[taste_ingr]
theorem spring_energy_nonneg :
    ∀ (k : Rat), ∀ (dx : Rat), ∀ (dy : Rat), ∀ (dz : Rat), k ≥ (0 : Int) → spring_energy k dx dy dz ≥ (0 : Int) := by
  intros; simp_all (config := { zetaDelta := true }) [taste_ingr]; nlinarith

def cauchy_schwarz := fun (ax : Rat) ↦ fun (ay : Rat) ↦ fun (az : Rat) ↦ fun (bx : Rat) ↦ fun («by» : Rat) ↦
  fun (bz : Rat) ↦
  /-
  Cauchy-Schwarz: (a . b)^2 <= |a|^2 |b|^2, built from two helper facts that land in scope as
      local hypotheses (so `linarith` composes them) -- the SOS certificate bare `nlinarith` can't find:
        1. Lagrange's identity   |a x b|^2 + (a . b)^2 = |a|^2 |b|^2, and
        2. the cross norm is non-negative   |a x b|^2 >= 0,
      whence (a . b)^2 = |a|^2 |b|^2 - |a x b|^2 <= |a|^2 |b|^2.
  -/
  have ht_1 :
    norm_sq (cross_x ax ay az bx «by» bz) (cross_y ax ay az bx «by» bz) (cross_z ax ay az bx «by» bz) +ₚ
        dot ax ay az bx «by» bz *ₚ dot ax ay az bx «by» bz =
      norm_sq ax ay az *ₚ norm_sq bx «by» bz :=
    by simp_all (config := { zetaDelta := true }) [taste_ingr]; pyany_cases <;> grind +locals
  have ht_2 :
    norm_sq (cross_x ax ay az bx «by» bz) (cross_y ax ay az bx «by» bz) (cross_z ax ay az bx «by» bz) ≥ (0 : Int) := by
    simp_all (config := { zetaDelta := true }) [taste_ingr]; nlinarith
  have ht_3 : dot ax ay az bx «by» bz *ₚ dot ax ay az bx «by» bz ≤ norm_sq ax ay az *ₚ norm_sq bx «by» bz := by simp_all (config := { zetaDelta := true }) [taste_ingr]; pyany_cases <;> grind +locals
  ()

attribute [simp] cauchy_schwarz

def cauchy_schwarz'rn := fun (ax : Float) ↦ fun (ay : Float) ↦ fun (az : Float) ↦ fun (bx : Float) ↦
  fun («by» : Float) ↦ fun (bz : Float) ↦
  /-
  Cauchy-Schwarz: (a . b)^2 <= |a|^2 |b|^2, built from two helper facts that land in scope as
      local hypotheses (so `linarith` composes them) -- the SOS certificate bare `nlinarith` can't find:
        1. Lagrange's identity   |a x b|^2 + (a . b)^2 = |a|^2 |b|^2, and
        2. the cross norm is non-negative   |a x b|^2 >= 0,
      whence (a . b)^2 = |a|^2 |b|^2 - |a x b|^2 <= |a|^2 |b|^2.
  -/
  ()

-- ----------------------------------------------------------------------------------------------
-- Provable invariants: physical conservation laws
-- ----------------------------------------------------------------------------------------------
@[taste_ingr]
theorem central_force_no_torque :
    ∀ (rx : Rat),
      ∀ (ry : Rat), ∀ (rz : Rat), ∀ (lam : Rat), cross_x rx ry rz (lam *ₚ rx) (lam *ₚ ry) (lam *ₚ rz) = (0 : Int) :=
  by intros; simp_all (config := { zetaDelta := true }) [taste_ingr]; pyany_cases <;> grind +locals

@[taste_ingr]
theorem momentum_conserved :
    ∀ (m1 : Rat),
      ∀ (v1 : Rat), ∀ (m2 : Rat), ∀ (v2 : Rat), ∀ (j : Rat), m1 *ₚ v1 +ₚ j +ₚ (m2 *ₚ v2 -ₚ j) = m1 *ₚ v1 +ₚ m2 *ₚ v2 :=
  by intros; simp_all (config := { zetaDelta := true }) [taste_ingr]

@[taste_ingr]
theorem angular_momentum_is_moment :
    ∀ (m : Rat),
      ∀ (rx : Rat),
        ∀ (ry : Rat),
          ∀ (rz : Rat),
            ∀ (vx : Rat),
              ∀ (vy : Rat),
                ∀ (vz : Rat), cross_x rx ry rz (m *ₚ vx) (m *ₚ vy) (m *ₚ vz) = m *ₚ cross_x rx ry rz vx vy vz :=
  by intros; simp_all (config := { zetaDelta := true }) [taste_ingr]; pyany_cases <;> grind +locals

@[taste_ingr]
theorem spring_force_is_central :
    ∀ (k : Rat),
      ∀ (dx : Rat), ∀ (dy : Rat), ∀ (dz : Rat), cross_x dx dy dz (-k *ₚ dx) (-k *ₚ dy) (-k *ₚ dz) = (0 : Int) :=
  by intros; simp_all (config := { zetaDelta := true }) [taste_ingr]; pyany_cases <;> grind +locals

-- ----------------------------------------------------------------------------------------------
-- EDGE: main -- the single monadic island (reads input, integrates, prints; NOT proved)
-- ----------------------------------------------------------------------------------------------
def main' :=
  ((do
      let mut k := PastaLean.pyRat (← (PastaLean.ProofMode.pyInputProof ""))
      let mut m1 := PastaLean.pyRat (← (PastaLean.ProofMode.pyInputProof ""))
      let mut m2 := PastaLean.pyRat (← (PastaLean.ProofMode.pyInputProof ""))
      let mut r1x := PastaLean.pyRat (← (PastaLean.ProofMode.pyInputProof ""))
      let mut r1y := PastaLean.pyRat (← (PastaLean.ProofMode.pyInputProof ""))
      let mut r1z := PastaLean.pyRat (← (PastaLean.ProofMode.pyInputProof ""))
      let mut r2x := PastaLean.pyRat (← (PastaLean.ProofMode.pyInputProof ""))
      let mut r2y := PastaLean.pyRat (← (PastaLean.ProofMode.pyInputProof ""))
      let mut r2z := PastaLean.pyRat (← (PastaLean.ProofMode.pyInputProof ""))
      let mut v1x := PastaLean.pyRat (← (PastaLean.ProofMode.pyInputProof ""))
      let mut v1y := PastaLean.pyRat (← (PastaLean.ProofMode.pyInputProof ""))
      let mut v1z := PastaLean.pyRat (← (PastaLean.ProofMode.pyInputProof ""))
      let mut v2x := PastaLean.pyRat (← (PastaLean.ProofMode.pyInputProof ""))
      let mut v2y := PastaLean.pyRat (← (PastaLean.ProofMode.pyInputProof ""))
      let mut v2z := PastaLean.pyRat (← (PastaLean.ProofMode.pyInputProof ""))
      let mut dt := PastaLean.pyRat (← (PastaLean.ProofMode.pyInputProof ""))
      let mut nsteps : Int := PastaLean.pyInt (← (PastaLean.ProofMode.pyInputProof ""))
      let mut every : Int := PastaLean.pyInt (← (PastaLean.ProofMode.pyInputProof ""))
      let mut t := (0.0 : Rat)
      for step in (PastaLean.pyRange nsteps) do
        -- Hooke spring (rest length 0): force F = -k (r1 - r2) on body 1, +k (r1 - r2) on body 2.
        -- Acceleration is F / m; all polynomial, no transcendentals.
        let mut dx := r1x -ₚ r2x
        let mut dy := r1y -ₚ r2y
        let mut dz := r1z -ₚ r2z
        let mut a1x := -k *ₚ dx /ₚ m1
        let mut a1y := -k *ₚ dy /ₚ m1
        let mut a1z := -k *ₚ dz /ₚ m1
        let mut a2x := k *ₚ dx /ₚ m2
        let mut a2y := k *ₚ dy /ₚ m2
        let mut a2z := k *ₚ dz /ₚ m2
        -- Velocity-Verlet (here the force is linear, so a half/full kick step is exact enough).
        v1x := v1x +ₚ a1x *ₚ dt
        v1y := v1y +ₚ a1y *ₚ dt
        v1z := v1z +ₚ a1z *ₚ dt
        v2x := v2x +ₚ a2x *ₚ dt
        v2y := v2y +ₚ a2y *ₚ dt
        v2z := v2z +ₚ a2z *ₚ dt
        r1x := r1x +ₚ v1x *ₚ dt
        r1y := r1y +ₚ v1y *ₚ dt
        r1z := r1z +ₚ v1z *ₚ dt
        r2x := r2x +ₚ v2x *ₚ dt
        r2y := r2y +ₚ v2y *ₚ dt
        r2z := r2z +ₚ v2z *ₚ dt
        t := t +ₚ dt
        if h_1 : step %ₚ every = (0 : Int) then 
          let mut energy :=
            kinetic m1 v1x v1y v1z +ₚ kinetic m2 v2x v2y v2z +ₚ spring_energy k (r1x -ₚ r2x) (r1y -ₚ r2y) (r1z -ₚ r2z)
          let mut px := m1 *ₚ v1x +ₚ m2 *ₚ v2x
          let mut lx :=
            cross_x r1x r1y r1z (m1 *ₚ v1x) (m1 *ₚ v1y) (m1 *ₚ v1z) +ₚ
              cross_x r2x r2y r2z (m2 *ₚ v2x) (m2 *ₚ v2y) (m2 *ₚ v2z)
          let _ ←
            PastaLean.ProofMode.pyPrintProof
                [pyPrintArg "S", pyPrintArg step, pyPrintArg t, pyPrintArg energy, pyPrintArg px, pyPrintArg lx]
        else
          let _ := ()) :
    PastaLean.ProofMode.PyProofM _)

attribute [simp] main'

def main''rn :=
  ((do
      let mut k := PastaLean.pyFloat (← (PastaLean.pyInputIO ""))
      let mut m1 := PastaLean.pyFloat (← (PastaLean.pyInputIO ""))
      let mut m2 := PastaLean.pyFloat (← (PastaLean.pyInputIO ""))
      let mut r1x := PastaLean.pyFloat (← (PastaLean.pyInputIO ""))
      let mut r1y := PastaLean.pyFloat (← (PastaLean.pyInputIO ""))
      let mut r1z := PastaLean.pyFloat (← (PastaLean.pyInputIO ""))
      let mut r2x := PastaLean.pyFloat (← (PastaLean.pyInputIO ""))
      let mut r2y := PastaLean.pyFloat (← (PastaLean.pyInputIO ""))
      let mut r2z := PastaLean.pyFloat (← (PastaLean.pyInputIO ""))
      let mut v1x := PastaLean.pyFloat (← (PastaLean.pyInputIO ""))
      let mut v1y := PastaLean.pyFloat (← (PastaLean.pyInputIO ""))
      let mut v1z := PastaLean.pyFloat (← (PastaLean.pyInputIO ""))
      let mut v2x := PastaLean.pyFloat (← (PastaLean.pyInputIO ""))
      let mut v2y := PastaLean.pyFloat (← (PastaLean.pyInputIO ""))
      let mut v2z := PastaLean.pyFloat (← (PastaLean.pyInputIO ""))
      let mut dt := PastaLean.pyFloat (← (PastaLean.pyInputIO ""))
      let mut nsteps : Int := PastaLean.pyInt (← (PastaLean.pyInputIO ""))
      let mut every : Int := PastaLean.pyInt (← (PastaLean.pyInputIO ""))
      let mut t := (0.0 : Float)
      for step in (PastaLean.pyRange nsteps) do
        -- Hooke spring (rest length 0): force F = -k (r1 - r2) on body 1, +k (r1 - r2) on body 2.
        -- Acceleration is F / m; all polynomial, no transcendentals.
        let mut dx := r1x -ₚ r2x
        let mut dy := r1y -ₚ r2y
        let mut dz := r1z -ₚ r2z
        let mut a1x := PastaLean.pyFloat (-k *ₚ dx) /ₚ m1
        let mut a1y := PastaLean.pyFloat (-k *ₚ dy) /ₚ m1
        let mut a1z := PastaLean.pyFloat (-k *ₚ dz) /ₚ m1
        let mut a2x := PastaLean.pyFloat (k *ₚ dx) /ₚ m2
        let mut a2y := PastaLean.pyFloat (k *ₚ dy) /ₚ m2
        let mut a2z := PastaLean.pyFloat (k *ₚ dz) /ₚ m2
        -- Velocity-Verlet (here the force is linear, so a half/full kick step is exact enough).
        v1x := v1x +ₚ a1x *ₚ dt
        v1y := v1y +ₚ a1y *ₚ dt
        v1z := v1z +ₚ a1z *ₚ dt
        v2x := v2x +ₚ a2x *ₚ dt
        v2y := v2y +ₚ a2y *ₚ dt
        v2z := v2z +ₚ a2z *ₚ dt
        r1x := r1x +ₚ v1x *ₚ dt
        r1y := r1y +ₚ v1y *ₚ dt
        r1z := r1z +ₚ v1z *ₚ dt
        r2x := r2x +ₚ v2x *ₚ dt
        r2y := r2y +ₚ v2y *ₚ dt
        r2z := r2z +ₚ v2z *ₚ dt
        t := t +ₚ dt
        if h_1 : step %ₚ every == (0 : Int) then 
          let mut energy :=
            kinetic'rn m1 v1x v1y v1z +ₚ kinetic'rn m2 v2x v2y v2z +ₚ
              spring_energy'rn k (r1x -ₚ r2x) (r1y -ₚ r2y) (r1z -ₚ r2z)
          let mut px := m1 *ₚ v1x +ₚ m2 *ₚ v2x
          let mut lx :=
            cross_x'rn r1x r1y r1z (m1 *ₚ v1x) (m1 *ₚ v1y) (m1 *ₚ v1z) +ₚ
              cross_x'rn r2x r2y r2z (m2 *ₚ v2x) (m2 *ₚ v2y) (m2 *ₚ v2z)
          let _ ←
            pyPrintIO [pyPrintArg "S", pyPrintArg step, pyPrintArg t, pyPrintArg energy, pyPrintArg px, pyPrintArg lx]
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
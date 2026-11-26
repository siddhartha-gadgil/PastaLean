import PastaLean
import Libraries
import Std.Tactic.Do

open PastaLean
open Libraries
open Std.Do

set_option linter.all false

set_option maxHeartbeats 200000

namespace PastaLean.User.Root

-- --- PURE MATH (Tier 0, provable) ---
-- Exact mode lowers these to ℚ (rational, computable AND provable); calc_entropy uses
-- math.log so it is ℝ/noncomputable but still provable. The runnable simulation (odeint,
-- linspace, IO loop) lives in pk_simulation.py and is generated with --approx (all Float).
-- parameters for the 3-body system (grass, rabbits, wolves)
def r :=
  (1.2 : Rat)

def k :=
  (100.0 : Rat)

def a :=
  (0.1 : Rat)

def b :=
  (0.05 : Rat)

def d :=
  (0.4 : Rat)

def c :=
  (0.1 : Rat)

def e :=
  (0.02 : Rat)

private def _f :=
  (0.3 : Rat)

def grass_rate := fun (g : Rat) ↦ fun (r_pop : Rat) ↦
  (show Rat from r *ₚ g *ₚ ((1.0 : Rat) -ₚ g /ₚ k) -ₚ a *ₚ g *ₚ r_pop)

attribute [simp, taste_ingr] grass_rate

def grass_rate'rn := fun (g : Float) ↦ fun (r_pop : Float) ↦
  (show Float from r *ₚ g *ₚ ((1.0 : Float) -ₚ PastaLean.pyTrueDiv g k) -ₚ a *ₚ g *ₚ r_pop)

def rabbit_rate := fun (g : Rat) ↦ fun (r_pop : Rat) ↦ fun (w : Rat) ↦
  (show Rat from b *ₚ g *ₚ r_pop -ₚ d *ₚ r_pop -ₚ c *ₚ r_pop *ₚ w)

attribute [simp, taste_ingr] rabbit_rate

def rabbit_rate'rn := fun (g : Float) ↦ fun (r_pop : Float) ↦ fun (w : Float) ↦
  (show Float from b *ₚ g *ₚ r_pop -ₚ d *ₚ r_pop -ₚ c *ₚ r_pop *ₚ w)

def wolf_rate := fun (r_pop : Rat) ↦ fun (w : Rat) ↦ (show Rat from e *ₚ r_pop *ₚ w -ₚ _f *ₚ w)

attribute [simp, taste_ingr] wolf_rate

def wolf_rate'rn := fun (r_pop : Float) ↦ fun (w : Float) ↦ (show Float from e *ₚ r_pop *ₚ w -ₚ _f *ₚ w)

def system_deriv := fun (state : List Rat) ↦ fun (t : Rat) ↦
  (show List Rat from
    /-
    Derivative function for the ODE system. Pure (Tier 0).
    -/
    [grass_rate state⦋(0 : Int)⦌ state⦋(1 : Int)⦌, rabbit_rate state⦋(0 : Int)⦌ state⦋(1 : Int)⦌ state⦋(2 : Int)⦌,
      wolf_rate state⦋(1 : Int)⦌ state⦋(2 : Int)⦌])

attribute [simp, taste_ingr] system_deriv

def system_deriv'rn := fun (state : List Float) ↦ fun (t : Float) ↦
  (show List Float from
    /-
    Derivative function for the ODE system. Pure (Tier 0).
    -/
    [grass_rate'rn state⦋(0 : Int)⦌ state⦋(1 : Int)⦌, rabbit_rate'rn state⦋(0 : Int)⦌ state⦋(1 : Int)⦌ state⦋(2 : Int)⦌,
      wolf_rate'rn state⦋(1 : Int)⦌ state⦋(2 : Int)⦌])

def calc_avg := fun (g : Rat) ↦ fun (r_p : Rat) ↦ fun (w : Rat) ↦ (show Rat from (g +ₚ r_p +ₚ w) /ₚ (3.0 : Rat))

attribute [simp, taste_ingr] calc_avg

def calc_avg'rn := fun (g : Float) ↦ fun (r_p : Float) ↦ fun (w : Float) ↦
  (show Float from PastaLean.pyTrueDiv (g +ₚ r_p +ₚ w) (3.0 : Float))

noncomputable def calc_entropy := fun (g : Rat) ↦ fun (r_p : Rat) ↦ fun (w : Rat) ↦
  -(g *ₚ Libraries.math.pyMathLogR (g +ₚ (1.0 : Rat)) +ₚ r_p *ₚ Libraries.math.pyMathLogR (r_p +ₚ (1.0 : Rat)) +ₚ
      w *ₚ Libraries.math.pyMathLogR (w +ₚ (1.0 : Rat)))

attribute [simp] calc_entropy

def calc_entropy'rn := fun (g : Float) ↦ fun (r_p : Float) ↦ fun (w : Float) ↦
  (show Float from
    -(g *ₚ Libraries.math.pyMathLog (g +ₚ (1.0 : Float)) +ₚ r_p *ₚ Libraries.math.pyMathLog (r_p +ₚ (1.0 : Float)) +ₚ
        w *ₚ Libraries.math.pyMathLog (w +ₚ (1.0 : Float))))

def is_ecosystem_surviving := fun (w_final : Rat) ↦ decide (w_final > (0.1 : Rat))

attribute [simp, taste_ingr] is_ecosystem_surviving

def is_ecosystem_surviving'rn := fun (w_final : Float) ↦ decide (w_final > (0.1 : Float))

end PastaLean.User.Root

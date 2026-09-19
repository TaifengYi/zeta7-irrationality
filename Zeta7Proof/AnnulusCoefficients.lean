import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.PowerSeries.GaussNorm
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.SpecificLimits.Basic

/-! Two-sided coefficient model for non-Archimedean open annuli.
Both tails decay at every interior real radius. This is not a modular-form
definition and does not assert convergence of any particular target. -/

set_option autoImplicit false
noncomputable section
namespace Zeta7Annulus
open Filter Topology PowerSeries
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

abbrev LaurentCoefficients := ℤ → ℚ_[7]

def DecaysAt (a : LaurentCoefficients) (ρ : ℝ) : Prop :=
  Tendsto (fun n : ℕ => ‖a (n : ℤ)‖ * ρ ^ n) atTop (𝓝 0) ∧
  Tendsto (fun n : ℕ => ‖a (-(n : ℤ))‖ * (ρ⁻¹) ^ n) atTop (𝓝 0)

def DecaysOn (a : LaurentCoefficients) (inner outer : ℝ) : Prop :=
  ∀ ρ : ℝ, inner < ρ → ρ < outer → DecaysAt a ρ

def reverse (a : LaurentCoefficients) : LaurentCoefficients := fun i => a (-i)

theorem reverse_reverse (a : LaurentCoefficients) : reverse (reverse a) = a := by
  funext i
  simp [reverse]

theorem reverse_decaysAt_iff (a : LaurentCoefficients) (ρ : ℝ) :
    DecaysAt (reverse a) ρ ↔ DecaysAt a ρ⁻¹ := by
  simp only [DecaysAt, reverse, neg_neg, inv_inv]
  exact and_comm

/-- Positive and negative powers both define convergent p-adic sums on each circle. -/
theorem DecaysAt.summable_tails {a : LaurentCoefficients} {z : ℚ_[7]}
    (ha : DecaysAt a ‖z‖) :
    Summable (fun n : ℕ => a (n : ℤ) * z ^ n) ∧
    Summable (fun n : ℕ => a (-(n : ℤ)) * (z⁻¹) ^ n) := by
  constructor
  · apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa only [norm_mul, norm_pow, Nat.cofinite_eq_atTop] using ha.1
  · apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa only [norm_mul, norm_pow, norm_inv, Nat.cofinite_eq_atTop] using ha.2

/-- Zero is counted once in evaluation; the two summable tails each contain it. -/
def eval (a : LaurentCoefficients) (z : ℚ_[7]) : ℚ_[7] :=
  (∑' n : ℕ, a (n : ℤ) * z ^ n) +
    (∑' n : ℕ, a (-(n : ℤ)) * (z⁻¹) ^ n) - a 0

theorem eval_reverse (a : LaurentCoefficients) (z : ℚ_[7]) :
    eval (reverse a) z = eval a z⁻¹ := by
  simp only [eval, reverse, neg_neg, neg_zero, inv_inv]
  ring

def ofPowerSeries (f : ℚ_[7]⟦X⟧) : LaurentCoefficients
  | .ofNat n => coeff n f
  | .negSucc _ => 0

@[simp] theorem ofPowerSeries_nat (f : ℚ_[7]⟦X⟧) (n : ℕ) :
    ofPowerSeries f (n : ℤ) = coeff n f := rfl

@[simp] theorem ofPowerSeries_negSucc (f : ℚ_[7]⟦X⟧) (n : ℕ) :
    ofPowerSeries f (Int.negSucc n) = 0 := rfl

/-- The two-sided condition specializes to the usual weighted Taylor condition. -/
theorem ofPowerSeries_decaysAt_iff (f : ℚ_[7]⟦X⟧) (ρ : ℝ) :
    DecaysAt (ofPowerSeries f) ρ ↔
      Tendsto (fun n : ℕ => ‖coeff n f‖ * ρ ^ n) atTop (𝓝 0) := by
  constructor
  · exact fun h => h.1
  · intro h
    refine ⟨h, ?_⟩
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    change (0 : ℝ) = ‖(0 : ℚ_[7])‖ * (ρ⁻¹) ^ (m + 1)
    simp

/-- A genuine Gauss bound follows from weighted decay; boundedness is not assumed. -/
theorem hasGaussNorm_of_decay (f : ℚ_[7]⟦X⟧) (ρ : ℝ)
    (h : Tendsto (fun n : ℕ => ‖coeff n f‖ * ρ ^ n) atTop (𝓝 0)) :
    HasGaussNorm (norm : ℚ_[7] → ℝ) ρ f := by
  exact h.bddAbove_range

end Zeta7Annulus

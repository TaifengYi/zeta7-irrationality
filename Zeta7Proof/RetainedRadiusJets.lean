import Zeta7Proof.Radius49Internal
import Zeta7Proof.CommonRationalGerms

/-! Consequences of the internally proved radius-49 theorem for the actual jets.
Only H and its Euler derivatives are covered here. K and its primitives
still require the cancellation argument at the inner root of P. -/
set_option autoImplicit false
noncomputable section
open PowerSeries Filter Topology
namespace Zeta7Common
open Zeta7Main
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

theorem euler_iterate_coeff (f : ℚ_[7]⟦X⟧) (k n : ℕ) :
    coeff n (euler^[k] f) = (n : ℚ_[7]) ^ k * coeff n f := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', euler_coeff, ih]
    ring

theorem euler_iterate_coeff_norm_le (f : ℚ_[7]⟦X⟧) (k n : ℕ) :
    ‖coeff n (euler^[k] f)‖ ≤ ‖coeff n f‖ := by
  rw [euler_iterate_coeff, norm_mul, norm_pow]
  have hn := IsUltrametricDist.norm_natCast_le_one ℚ_[7] n
  exact (mul_le_mul_of_nonneg_right (pow_le_one₀ (norm_nonneg _) hn) (norm_nonneg _)).trans_eq
    (one_mul _)

theorem euler_rescale (f : ℚ_[7]⟦X⟧) (a : ℚ_[7]) :
    euler (rescale a f) = rescale a (euler f) := by
  ext n
  simp only [euler_coeff, coeff_rescale]
  ring

theorem euler_iterate_rescale (f : ℚ_[7]⟦X⟧) (a : ℚ_[7]) (k : ℕ) :
    euler^[k] (rescale a f) = rescale a (euler^[k] f) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih, euler_rescale,
      Function.iterate_succ_apply']

/-- Arbitrarily high Euler jets preserve radius 49 (from the internal radius theorem). -/
theorem HSeries_euler_iterate_radius49 (k : ℕ) (ρ : ℝ) (hρ : 0 < ρ) (hρ49 : ρ < 49) :
    Tendsto (fun n : ℕ => ‖coeff n (euler^[k] HSeries)‖ * ρ ^ n) atTop (𝓝 0) := by
  apply squeeze_zero (fun n => mul_nonneg (norm_nonneg _) (pow_nonneg hρ.le n))
    (fun n => mul_le_mul_of_nonneg_right (euler_iterate_coeff_norm_le HSeries k n)
      (pow_nonneg hρ.le n))
  exact HSeries_radius49 ρ hρ hρ49

theorem normalisedHSeries_euler_iterate_radius1
    (k : ℕ) (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    Tendsto (fun n : ℕ => ‖coeff n (euler^[k] normalisedHSeries)‖ * ρ ^ n)
      atTop (𝓝 0) := by
  apply squeeze_zero (fun n => mul_nonneg (norm_nonneg _) (pow_nonneg hρ.le n))
    (fun n => mul_le_mul_of_nonneg_right
      (euler_iterate_coeff_norm_le normalisedHSeries k n) (pow_nonneg hρ.le n))
  exact normalisedHSeries_radius1 ρ hρ hρ1

/-- A single epsilon-dependent constant works for every jet order and every coefficient. -/
theorem normalisedHSeries_all_jets_norm_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ k n : ℕ,
      ‖coeff n (rescale (49 : ℚ_[7])⁻¹ (euler^[k] HSeries))‖ ≤
        (7 : ℝ) ^ (ε * n + B) := by
  obtain ⟨B, hB, hb⟩ := normalisedHSeries_epsilon_norm_bound ε hε
  refine ⟨B, hB, fun k n => ?_⟩
  rw [← euler_iterate_rescale]
  exact (euler_iterate_coeff_norm_le normalisedHSeries k n).trans (hb n)

theorem targetGerms_jet (j : Fin 3) :
    targetGerms (Fin.castLE (by decide) j) = euler^[j.val] HSeries := by
  fin_cases j <;> rfl

/-- Equation (4) in norm form for the first three actual target blocks.
The remaining three blocks are not covered by this theorem. -/
theorem targetGerms_first_three_norm_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (j : Fin 3) (n : ℕ),
      ‖coeff n (rescale (49 : ℚ_[7])⁻¹ (targetGerms (Fin.castLE (by decide) j)))‖ ≤
        (7 : ℝ) ^ (ε * n + B) := by
  obtain ⟨B, hB, hb⟩ := normalisedHSeries_all_jets_norm_bound ε hε
  refine ⟨B, hB, fun j n => ?_⟩
  rw [targetGerms_jet]
  exact hb j.val n

end Zeta7Common

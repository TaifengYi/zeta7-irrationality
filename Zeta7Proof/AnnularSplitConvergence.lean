import Zeta7Proof.AnnularFiniteForcing

/-! Analytic domains of the actual two parts, derived from their original coefficients. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
namespace Zeta7Annulus
open Filter Topology
local instance AnnularSplitConvergence_local1 : Fact (Nat.Prime 7) := ⟨by decide⟩

theorem annularPositivePart_decays (ρ : ℝ) (hρ : 0 < ρ) (h49 : ρ < 49) :
    DecaysAt annularPositivePart ρ := by
  have hσ : 1 < max 2 ρ := (by norm_num : (1 : ℝ) < 2).trans_le (le_max_left _ _)
  have ha := annularCandidateA_decays (max 2 ρ) hσ (max_lt (by norm_num) h49)
  constructor
  · apply squeeze_zero (fun n => mul_nonneg (norm_nonneg _) (pow_nonneg hρ.le n)) ?_ ha.1
    intro n
    have he : annularPositivePart (n : ℤ) = annularCandidateA n := by
      simp only [annularPositivePart, if_pos (by omega : -2 ≤ (n : ℤ))]
    rw [he]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hρ.le (le_max_right 2 ρ) n) (norm_nonneg _)
  · apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop 2] with n hn
    simp only [annularPositivePart_below (by omega : -(n : ℤ) < -2), norm_zero, zero_mul]

theorem annularNegativePart_decays (ρ : ℝ) (hρ : 1 < ρ) : DecaysAt annularNegativePart ρ := by
  have hσ : 1 < min ρ 2 := lt_min hρ (by norm_num)
  have ha := annularCandidateA_decays (min ρ 2) hσ
    ((min_le_right _ _).trans_lt (by norm_num : (2 : ℝ) < 49))
  constructor
  · have he : (fun n : ℕ => ‖annularNegativePart (n : ℤ)‖ * ρ ^ n) = fun _ => 0 := by
      funext n
      simp only [annularNegativePart_above (by omega : -2 ≤ (n : ℤ)), norm_zero, zero_mul]
    rw [he]
    exact tendsto_const_nhds
  · apply squeeze_zero' (Eventually.of_forall (fun n =>
      mul_nonneg (norm_nonneg _) (pow_nonneg (inv_nonneg.mpr (by linarith : 0 ≤ ρ)) n))) ?_ ha.2
    filter_upwards [eventually_gt_atTop 2] with n hn
    have he : annularNegativePart (-(n : ℤ)) = annularCandidateA (-(n : ℤ)) := by
      simp only [annularNegativePart, Pi.sub_apply,
        annularPositivePart_below (by omega : -(n : ℤ) < -2), sub_zero]
    rw [he]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (inv_nonneg.mpr (by linarith : 0 ≤ ρ))
        (inv_anti₀ (by linarith : 0 < min ρ 2) (min_le_left _ _)) n) (norm_nonneg _)

end Zeta7Annulus

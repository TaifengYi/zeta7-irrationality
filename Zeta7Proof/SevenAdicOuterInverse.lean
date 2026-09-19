import Zeta7Proof.ActualSevenAdicRoots
import Zeta7Proof.ActualTargetClearedEquation
import Zeta7Proof.SevenAdicSeriesEvaluation

/-! Explicit inverse for the outer linear factor, with its actual radius. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
open PowerSeries Filter Topology
namespace Zeta7Common
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

def linearReciprocal (b : ℚ_[7]) : ℚ_[7]⟦X⟧ := C (-b⁻¹) * rescale b⁻¹ (mk 1)

theorem linearReciprocal_mul (b : ℚ_[7]) (hb : b ≠ 0) :
    (X - C b) * linearReciprocal b = 1 := by
  have h := congrArg (rescale b⁻¹) (mk_one_mul_one_sub_eq_one ℚ_[7])
  simp only [map_mul, map_sub, map_one, rescale_X] at h
  have hc : (C b : ℚ_[7]⟦X⟧) * C b⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hb, map_one]
  unfold linearReciprocal
  rw [map_neg]
  linear_combination h + rescale b⁻¹ (mk 1) * hc

theorem linearReciprocal_coeff (b : ℚ_[7]) (n : ℕ) :
    coeff n (linearReciprocal b) = -b⁻¹ * b⁻¹ ^ n := by
  simp [linearReciprocal, coeff_C_mul, coeff_rescale]

theorem outerReciprocal_restricted (r : ℝ) (hr : 0 ≤ r) (hr49 : r < 49) :
    IsRestricted r (linearReciprocal outerPotentialRoot) := by
  rw [isRestricted_iff']
  have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hr (by norm_num))
    ((div_lt_one (by norm_num : (0 : ℝ) < 49)).mpr hr49)).const_mul ((49 : ℝ)⁻¹)
  convert ht using 1
  · funext n
    rw [linearReciprocal_coeff, norm_mul, norm_neg, norm_inv, norm_pow, norm_inv,
      outerPotentialRoot_norm, div_pow]
    ring_nf
    simp only [one_div]
  · simp

theorem targetP_factorization :
    targetP = C (49 : ℚ_[7]) * (X - C innerPotentialRoot) * (X - C outerPotentialRoot) := by
  have hp : (1 + 13 * Polynomial.X + 49 * Polynomial.X ^ 2 : Polynomial ℚ_[7]) =
      Polynomial.C 49 * (Polynomial.X - Polynomial.C innerPotentialRoot) *
        (Polynomial.X - Polynomial.C outerPotentialRoot) := by
    apply Polynomial.funext
    intro x
    simpa [map_ofNat] using potential_root_factorization x
  have h := congrArg Polynomial.coeToPowerSeries.ringHom hp
  simpa only [map_add, map_mul, map_pow, map_sub, map_one, map_ofNat,
    Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X, Polynomial.coe_C,
    map_ofNat, targetP] using h

theorem targetP_ne_zero : targetP ≠ 0 := by
  intro h
  have hh := congrArg constantCoeff h
  norm_num [targetP] at hh

end Zeta7Common

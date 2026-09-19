import Zeta7Proof.AnnularHypergeometricUnits

/-! Radius-seven nonvanishing of the original compatible annular candidate. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
namespace Zeta7Annulus
local instance AnnularCandidateNonzero_local1 : Fact (Nat.Prime 7) := ⟨by decide⟩
local instance AnnularCandidateNonzero_local2 : Fact (0 < (7 : ℝ)) := ⟨by norm_num⟩

namespace ClosedAnnulus

local instance AnnularCandidateNonzero_local3 : Nontrivial (ClosedAnnulus 7 7) := ⟨⟨0, 1, by
  intro h
  have hn := congrArg norm h
  norm_num only [norm_zero, norm_one] at hn⟩⟩

theorem annularT_seven_sub_one_bound : ‖annularT (r := 7) (R := 7) - 1‖ ≤ (7 : ℝ)⁻¹ := by
  have h1 : ‖monomial (r := 7) (R := 7) 1 (-490)‖ ≤ (7 : ℝ)⁻¹ := by
    have hv : ‖(490 : ℚ_[7])‖ = (7 : ℝ)⁻¹ ^ 2 := by
      simpa only [Nat.cast_ofNat] using norm_integer_factor 490 10 2 (by decide) (by decide)
    rw [monomial_norm, norm_neg, hv]
    norm_num
  have h2 : ‖monomial (r := 7) (R := 7) 2 (-21609)‖ ≤ (7 : ℝ)⁻¹ := by
    have hv : ‖(21609 : ℚ_[7])‖ = (7 : ℝ)⁻¹ ^ 4 := by
      simpa only [Nat.cast_ofNat] using norm_integer_factor 21609 9 4 (by decide) (by decide)
    rw [monomial_norm, norm_neg, hv]
    norm_num
  have h3 : ‖monomial (r := 7) (R := 7) 3 (-235298)‖ ≤ (7 : ℝ)⁻¹ := by
    have hv : ‖(235298 : ℚ_[7])‖ = (7 : ℝ)⁻¹ ^ 6 := by
      simpa only [Nat.cast_ofNat] using norm_integer_factor 235298 2 6 (by decide) (by decide)
    rw [monomial_norm, norm_neg, hv]
    norm_num
  have h4 : ‖monomial (r := 7) (R := 7) 4 (-823543)‖ ≤ (7 : ℝ)⁻¹ := by
    have hv : ‖(823543 : ℚ_[7])‖ = (7 : ℝ)⁻¹ ^ 7 := by
      simpa only [Nat.cast_ofNat] using norm_integer_factor 823543 1 7 (by decide) (by decide)
    rw [monomial_norm, norm_neg, hv]
    norm_num
  have he : annularT (r := 7) (R := 7) - 1 =
      monomial 1 (-490) + monomial 2 (-21609) + monomial 3 (-235298) + monomial 4 (-823543) := by
    unfold annularT; ring
  rw [he]
  exact (norm_add_le_max _ _).trans (max_le
    ((norm_add_le_max _ _).trans (max_le ((norm_add_le_max _ _).trans (max_le h1 h2)) h3)) h4)

theorem annularT_seven_isUnit : IsUnit (annularT (r := 7) (R := 7)) := by
  have ht : ‖1 - annularT (r := 7) (R := 7)‖ < 1 := by
    rw [norm_sub_rev]
    exact annularT_seven_sub_one_bound.trans_lt (by norm_num)
  simpa only [sub_sub_cancel] using isUnit_one_sub_of_norm_lt_one ht

theorem annularSubstitution_seven_norm_bound :
    ‖annularSubstitution (r := 7) (R := 7)‖ ≤ (7 : ℝ)⁻¹ := by
  have ht : ‖annularT (r := 7) (R := 7)‖ ≤ 1 := by
    convert annularT_circle_bound (ρ := 7) (by norm_num) using 1 <;> norm_num
  have hp := pInverse_norm_le (r := 7) (R := 7) (by norm_num) (by norm_num) le_rfl
  have hn := nInverse_norm_le (r := 7) (R := 7) (by norm_num) (by norm_num) le_rfl
  unfold annularSubstitution
  calc
    _ ≤ (‖annularT (r := 7) (R := 7)‖ ^ 2 * ‖pInverse (r := 7) (R := 7)‖) *
        ‖nInverse (r := 7) (R := 7)‖ ^ 3 := by
      exact (norm_mul_le _ _).trans (mul_le_mul
        ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_pow_le _ _) (norm_nonneg _)))
        (norm_pow_le _ _) (norm_nonneg _) (by positivity))
    _ ≤ (1 * (7 : ℝ)⁻¹) * 1 := mul_le_mul
      (mul_le_mul (pow_le_one₀ (norm_nonneg _) ht) hp (norm_nonneg _) zero_le_one)
      (pow_le_one₀ (norm_nonneg _) hn) (by positivity) (by positivity)
    _ = _ := by ring

theorem actualHypergeometricValue_seven_isUnit (i : Fin 2) :
    IsUnit (actualHypergeometricValue (r := 7) (R := 7) i) :=
  hypergeometricCompose_isUnit i _ annularSubstitution_seven_norm_bound

theorem candidateB_seven_isUnit : IsUnit (candidateB (r := 7) (R := 7)) := by
  have hn : IsUnit (nInverse (r := 7) (R := 7)) := by
    have hprod : IsUnit (annularN (r := 7) (R := 7) * nInverse) := by
      rw [annularN_mul_inverse (by norm_num) (by norm_num) le_rfl]
      exact isUnit_one
    exact isUnit_of_mul_isUnit_right hprod
  exact ((annularT_seven_isUnit.mul (hn.pow 2)).mul
    (actualHypergeometricValue_seven_isUnit 0)).mul (actualHypergeometricValue_seven_isUnit 1)

theorem candidateB_seven_ne_zero : candidateB (r := 7) (R := 7) ≠ 0 :=
  candidateB_seven_isUnit.ne_zero

end ClosedAnnulus

theorem annularCandidateB_ne_zero : annularCandidateB ≠ 0 := by
  intro h
  have he := annularCandidateCoefficients_eq (r := 7) (R := 7) (by norm_num) (by norm_num) le_rfl 0
  have hc : (ClosedAnnulus.candidateB (r := 7) (R := 7)).coeffs = 0 := by
    simpa only [annularCandidateB, ClosedAnnulus.candidate, ite_true] using he.symm.trans h
  exact ClosedAnnulus.candidateB_seven_ne_zero (ClosedAnnulus.ext hc)

end Zeta7Annulus

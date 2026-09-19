import Zeta7Proof.AnnularSevenApproximation
import Zeta7Proof.AnnularForcingCorrection

/-! Nonvanishing of the actual forcing, from a strict Gauss approximation. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
namespace Zeta7Annulus
local instance AnnularForcingNonzero_prime : Fact (Nat.Prime 7) := ⟨by decide⟩
local instance AnnularForcingNonzero_radius : Fact (0 < (7 : ℝ)) := ⟨by norm_num⟩

theorem annularCandidateA_seven_coefficients :
    annularCandidateA = (ClosedAnnulus.candidateA (r := 7) (R := 7)).coeffs := by
  simpa only [annularCandidateA, ClosedAnnulus.candidate, show (1 : Fin 2) ≠ 0 by decide, ite_false] using
    annularCandidateCoefficients_eq (r := 7) (R := 7) (by norm_num) (by norm_num) le_rfl 1

theorem annularCandidateA_coefficient_bound (k : ℤ) :
    ‖annularCandidateA k‖ ≤ (7 : ℝ)⁻¹ * (7 : ℝ) ^ (-k) := by
  rw [annularCandidateA_seven_coefficients]
  exact ((ClosedAnnulus.candidateA (r := 7) (R := 7)).coeff_norm_le k).trans
    (mul_le_mul_of_nonneg_right ClosedAnnulus.candidateA_seven_norm_bound (by positivity))

theorem annularCandidateA_residue_approximation :
    ‖annularCandidateA (-1) - (1 / 13 : ℚ_[7])‖ ≤ (7 : ℝ)⁻¹ := by
  have hc := (ClosedAnnulus.candidateA (r := 7) (R := 7) -
    ClosedAnnulus.monomial (-1) (1 / 13)).coeff_norm_le (-1)
  have hb := mul_le_mul_of_nonneg_right ClosedAnnulus.candidateA_seven_approximation
    (show (0 : ℝ) ≤ 7 ^ (-(-1 : ℤ)) by positivity)
  rw [annularCandidateA_seven_coefficients]
  have h := hc.trans hb
  norm_num [ClosedAnnulus.coeffs_sub, bilateralMonomial] at h ⊢
  exact h

theorem annularCandidateA_residue_ne_zero : annularCandidateA (-1) ≠ 0 := by
  intro hz
  have h := annularCandidateA_residue_approximation
  rw [hz, zero_sub, norm_neg, norm_div, norm_one, ClosedAnnulus.norm_thirteen] at h
  norm_num at h

theorem annularForcingQuadratic_ne_zero : annularForcingQuadratic ≠ 0 := by
  intro hz
  have h0 := congrArg (fun f : Polynomial ℚ_[7] => f.coeff 0) hz
  have h1 := congrArg (fun f : Polynomial ℚ_[7] => f.coeff 1) hz
  have h2 := congrArg (fun f : Polynomial ℚ_[7] => f.coeff 2) hz
  simp [annularForcingQuadratic] at h0 h1 h2
  have hr : annularForcingReversed = 0 := by
    simp [annularForcingReversed, h0, h1, h2]
  have hp : annularCorrectedForcingPolynomial = 0 := by
    rw [annularCorrectedForcing_factorization, hr, mul_zero]
  rw [annularCorrectedForcing_coefficients] at hp
  have hc0 := congrArg (fun f : Polynomial ℚ_[7] => f.coeff 0) hp
  have hc1 := congrArg (fun f : Polynomial ℚ_[7] => f.coeff 1) hp
  simp at hc0 hc1
  have hf := annularFiniteForcing_coefficients
  unfold correctedForcing₀ at hc0
  unfold correctedForcing₁ at hc1
  rw [hf.1] at hc0
  rw [hf.2.1] at hc1
  apply annularCandidateA_residue_ne_zero
  linear_combination (105 / 8 : ℚ_[7]) * hc0 - hc1

end Zeta7Annulus

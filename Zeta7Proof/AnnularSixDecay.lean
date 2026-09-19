import Zeta7Proof.AnnularPolynomialCoefficients

/-! Convergence and uniform negative-tail bounds of the actual six coefficients. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
namespace Zeta7Annulus
local instance AnnularSixDecay_prime : Fact (Nat.Prime 7) := ⟨by decide⟩
local instance AnnularSixDecay_radius : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
namespace ClosedAnnulus

theorem circle_coefficients_add_decay {a b : ClosedAnnulus 1 1} {ρ : ℝ} (hρ : 0 < ρ)
    (ha : DecaysAt a.coeffs ρ) (hb : DecaysAt b.coeffs ρ) : DecaysAt (a + b).coeffs ρ :=
  ha.add hb hρ

theorem circle_coefficients_mul_decay {a b : ClosedAnnulus 1 1} {ρ : ℝ} (hρ : 0 < ρ)
    (ha : DecaysAt a.coeffs ρ) (hb : DecaysAt b.coeffs ρ) : DecaysAt (a * b).coeffs ρ :=
  ha.bilateralConvolution hb hρ

theorem circle_coefficients_neg_decay {a : ClosedAnnulus 1 1} {ρ : ℝ}
    (ha : DecaysAt a.coeffs ρ) : DecaysAt (-a).coeffs ρ := ha.neg

theorem circle_coefficients_euler_decay {a : ClosedAnnulus 1 1} {ρ : ℝ} (hρ : 0 < ρ)
    (ha : DecaysAt a.coeffs ρ) : DecaysAt (euler a).coeffs ρ := ha.euler hρ

theorem polynomial_coefficients_decay (f : Polynomial ℚ_[7]) {ρ : ℝ} (hρ : 0 < ρ) :
    DecaysAt (padicPolynomialMap (r := 1) (R := 1) f).coeffs ρ := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg => rw [map_add]; exact circle_coefficients_add_decay hρ hf hg
  | monomial n a =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial, padicPolynomialMap_C_mul_X_pow]
      exact bilateralMonomial_decays _ _ _

theorem reflectedCorrectedSolution_decay {ρ : ℝ} (hρ : (1 / 49 : ℝ) < ρ) :
    DecaysAt reflectedCorrectedSolution.coeffs ρ := by
  have hp : 0 < ρ := lt_trans (by norm_num) hρ
  have he : reflectedCorrectedSolution.coeffs = reverse annularCorrectedCoefficients := by
    funext k; exact reflectedCorrectedSolution_coefficients k
  rw [he, reverse_decaysAt_iff]
  apply annularCorrectedCoefficients_decays _ (inv_pos.mpr hp)
  exact (inv_lt_comm₀ hp (by norm_num)).mpr (by simpa using hρ)

theorem actualAnnularSix_decay (j : Fin 6) {ρ : ℝ} (hρ : (1 / 49 : ℝ) < ρ) :
    DecaysAt (actualAnnularSix j).coeffs ρ := by
  have hp : 0 < ρ := lt_trans (by norm_num) hρ
  have hq : DecaysAt (reflectedQ ^ 2).coeffs ρ := by
    rw [reflectedQ, ← map_pow]
    exact polynomial_coefficients_decay _ hp
  have hv := reflectedCorrectedSolution_decay hρ
  have hd := circle_coefficients_euler_decay hp hv
  have hdd := circle_coefficients_euler_decay hp hd
  have hf : DecaysAt reflectedPotentialNumerator.coeffs ρ :=
    circle_coefficients_add_decay hp
      (circle_coefficients_add_decay hp (bilateralMonomial_decays _ _ _) (bilateralMonomial_decays _ _ _))
      (bilateralMonomial_decays _ _ _)
  fin_cases j <;> simp only [actualAnnularSix, Matrix.cons_val_zero', Matrix.cons_val_succ']
  · exact circle_coefficients_add_decay hp
      (circle_coefficients_neg_decay (circle_coefficients_mul_decay hp hq hdd))
      (circle_coefficients_mul_decay hp hf hv)
  · exact circle_coefficients_mul_decay hp hq hd
  · exact circle_coefficients_neg_decay (circle_coefficients_mul_decay hp hq hv)
  · exact circle_coefficients_mul_decay hp hq (polynomial_coefficients_decay _ hp)
  · exact circle_coefficients_neg_decay (circle_coefficients_mul_decay hp
      (circle_coefficients_mul_decay hp (bilateralMonomial_decays _ _ _) hq)
      (polynomial_coefficients_decay _ hp))
  · exact circle_coefficients_mul_decay hp
      (circle_coefficients_mul_decay hp (bilateralMonomial_decays _ _ _) hq)
      (polynomial_coefficients_decay _ hp)

end ClosedAnnulus

theorem actualAnnularCoefficients_decay (j : Fin 6) {ρ : ℝ} (hρ : (1 / 49 : ℝ) < ρ) :
    DecaysAt (actualAnnularCoefficients j) ρ := ClosedAnnulus.actualAnnularSix_decay j hρ

/-- One constant for all six original coefficients, including index zero.
The radius is fixed before the uniform constant and the integer index. -/
theorem actualAnnularCoefficients_negative_bound {ρ : ℝ} (hρ : (1 / 49 : ℝ) < ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (j : Fin 6) (n : ℕ),
      ‖actualAnnularCoefficients j (-(n : ℤ))‖ ≤ C * ρ ^ n := by
  classical
  have hp : 0 < ρ := lt_trans (by norm_num) hρ
  let C : ℝ := ∑ j : Fin 6, bilateralGauss (actualAnnularCoefficients j) ρ
  have hc (j : Fin 6) : 0 ≤ bilateralGauss (actualAnnularCoefficients j) ρ :=
    bilateralGauss_nonneg (actualAnnularCoefficients_decay j hρ) hp
  refine ⟨C, Finset.sum_nonneg (fun j _ => hc j), fun j n => ?_⟩
  have hle : bilateralGauss (actualAnnularCoefficients j) ρ ≤ C :=
    Finset.single_le_sum (fun i _ => hc i) (Finset.mem_univ j)
  have hn := coefficient_norm_le_gauss (actualAnnularCoefficients_decay j hρ) hp (-(n : ℤ))
  simp only [neg_neg, zpow_natCast] at hn
  exact hn.trans (mul_le_mul_of_nonneg_right hle (pow_nonneg hp.le _))

end Zeta7Annulus

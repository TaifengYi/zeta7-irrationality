import Zeta7Proof.AnnularForcingNonzero

/-! Exact radius-seven bounds for the actual finite forcing and correction. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
namespace Zeta7Annulus
local instance AnnularCorrectionBounds_prime : Fact (Nat.Prime 7) := ⟨by decide⟩

theorem padic_mul_bound {a b : ℚ_[7]} {A B : ℝ}
    (ha : ‖a‖ ≤ A) (hb : ‖b‖ ≤ B) : ‖a * b‖ ≤ A * B := by
  rw [norm_mul]
  exact mul_le_mul ha hb (norm_nonneg _) ((norm_nonneg _).trans ha)

theorem padic_add_bound {a b : ℚ_[7]} {C : ℝ}
    (ha : ‖a‖ ≤ C) (hb : ‖b‖ ≤ C) : ‖a + b‖ ≤ C :=
  (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)

theorem padic_sub_bound {a b : ℚ_[7]} {C : ℝ}
    (ha : ‖a‖ ≤ C) (hb : ‖b‖ ≤ C) : ‖a - b‖ ≤ C := by
  simpa only [sub_eq_add_neg, norm_neg] using padic_add_bound ha
    (show ‖-b‖ ≤ C by simpa only [norm_neg] using hb)

theorem padic_int_mul_bound (n : ℤ) {a : ℚ_[7]} {A : ℝ}
    (ha : ‖a‖ ≤ A) : ‖(n : ℚ_[7]) * a‖ ≤ A := by
  simpa only [one_mul] using padic_mul_bound (Padic.norm_int_le_one n) ha

theorem norm_105_seven : ‖(105 : ℚ_[7])‖ = (1 / 7 : ℝ) := by
  have h := ClosedAnnulus.norm_integer_factor 105 15 1 (by decide) (by decide)
  simpa using h

theorem norm_441_seven : ‖(441 : ℚ_[7])‖ = (1 / 49 : ℝ) := by
  have h := ClosedAnnulus.norm_integer_factor 441 9 2 (by decide) (by decide)
  norm_num at h ⊢
  exact h

theorem annularFiniteForcing_bounds :
    ‖annularFiniteForcing (-2)‖ ≤ 7 ∧ ‖annularFiniteForcing (-1)‖ ≤ 1 ∧
    ‖annularFiniteForcing 0‖ ≤ 7 ∧ ‖annularFiniteForcing 1‖ ≤ (1 / 7 : ℝ) := by
  have ha2 : ‖annularCandidateA (-2)‖ ≤ 7 := by
    have h := annularCandidateA_coefficient_bound (-2)
    norm_num at h ⊢; exact h
  have ha1 : ‖annularCandidateA (-1)‖ ≤ 1 := by
    simpa using annularCandidateA_coefficient_bound (-1)
  have ha0 : ‖annularCandidateA 0‖ ≤ (1 / 7 : ℝ) := by
    simpa using annularCandidateA_coefficient_bound 0
  have hap : ‖annularCandidateA 1‖ ≤ (1 / 49 : ℝ) := by
    convert annularCandidateA_coefficient_bound 1 using 1 <;> norm_num
  rcases annularFiniteForcing_coefficients with ⟨h2, h1, h0, hp⟩
  rw [h2, h1, h0, hp]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using padic_int_mul_bound (-8) ha2
  · apply padic_sub_bound
    · simpa only [norm_neg] using ha1
    · have h := padic_mul_bound norm_105_seven.le ha2
      norm_num at h ⊢; exact h
  · apply padic_sub_bound
    · simpa only [neg_mul, norm_neg, Int.cast_ofNat, Nat.cast_ofNat] using
        (padic_int_mul_bound 9 ha1).trans (by norm_num : (1 : ℝ) ≤ 7)
    · exact padic_int_mul_bound 433 ha2
  · apply padic_sub_bound
    · exact padic_add_bound (hap.trans (by norm_num)) (padic_int_mul_bound 9 ha0)
    · have h := padic_mul_bound norm_441_seven.le ha2
      norm_num at h ⊢; exact h

theorem annularBoundaryPoint_norm : ‖annularBoundaryPoint‖ = (49 : ℝ) := by
  have h10 : ‖(10 : ℚ_[7])‖ = 1 := Padic.norm_natCast_eq_one_iff.mpr (by decide)
  rw [annularBoundaryPoint, norm_div, norm_neg, h10, ClosedAnnulus.norm_fortynine]
  norm_num

theorem annularForcingPolynomial_boundary_bound :
    ‖annularForcingPolynomial.eval annularBoundaryPoint‖ ≤ (16807 : ℝ) := by
  simp only [annularForcingPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow]
  rcases annularFiniteForcing_bounds with ⟨h2, h1, h0, hp⟩
  apply padic_add_bound
  · apply padic_add_bound
    · apply padic_add_bound (h2.trans (by norm_num))
      exact (padic_mul_bound h1 annularBoundaryPoint_norm.le).trans (by norm_num)
    · exact (padic_mul_bound h0 (by rw [norm_pow, annularBoundaryPoint_norm] :
        ‖annularBoundaryPoint ^ 2‖ ≤ (49 : ℝ) ^ 2)).trans (by norm_num)
  · exact (padic_mul_bound hp (by rw [norm_pow, annularBoundaryPoint_norm] :
      ‖annularBoundaryPoint ^ 3‖ ≤ (49 : ℝ) ^ 3)).trans (by norm_num)

theorem annularCorrectionConstant_bound : ‖annularCorrectionConstant‖ ≤ (2401 : ℝ) := by
  have h6 : ‖(6 : ℚ_[7])‖ = 1 := Padic.norm_natCast_eq_one_iff.mpr (by decide)
  have h7 : ‖(7 : ℚ_[7])‖ = (1 / 7 : ℝ) := by simpa using Padic.norm_p (p := 7)
  rw [annularCorrectionConstant, norm_div, annularBaseForcingPolynomial_boundary,
    norm_div, norm_neg, h6, h7]
  have h := annularForcingPolynomial_boundary_bound
  norm_num at h ⊢
  linarith

theorem correctedForcing_bounds :
    ‖correctedForcing₀‖ ≤ 2401 ∧ ‖correctedForcing₁‖ ≤ 343 ∧
    ‖correctedForcing₂‖ ≤ 2401 ∧ ‖correctedForcing₃‖ ≤ (49 : ℝ) := by
  rcases annularFiniteForcing_bounds with ⟨h2, h1, h0, hp⟩
  refine ⟨padic_add_bound (h2.trans (by norm_num)) (padic_int_mul_bound 8 annularCorrectionConstant_bound),
    padic_add_bound (h1.trans (by norm_num)) ?_,
    padic_add_bound (h0.trans (by norm_num)) (padic_int_mul_bound 433 annularCorrectionConstant_bound),
    padic_add_bound (hp.trans (by norm_num)) ?_⟩
  · exact (padic_mul_bound norm_105_seven.le annularCorrectionConstant_bound).trans (by norm_num)
  · exact (padic_mul_bound norm_441_seven.le annularCorrectionConstant_bound).trans (by norm_num)

theorem annularQuadratic₂_from_constant :
    annularQuadratic₂ = -(49 / 10 : ℚ_[7]) * correctedForcing₀ := by
  have hc := congrArg (fun f : Polynomial ℚ_[7] => f.coeff 0)
    annularCorrectedForcing_factorization
  rw [annularCorrectedForcing_coefficients] at hc
  simp [annularForcingReversed] at hc
  linear_combination (49 / 10 : ℚ_[7]) * hc

theorem annularQuadratic_bounds :
    ‖annularQuadratic₀‖ ≤ 49 ∧ ‖annularQuadratic₁‖ ≤ 2401 ∧
    ‖annularQuadratic₂‖ ≤ (49 : ℝ) := by
  rcases correctedForcing_bounds with ⟨h0, _, h2, h3⟩
  have h10 : ‖(10 : ℚ_[7])‖ = 1 := Padic.norm_natCast_eq_one_iff.mpr (by decide)
  refine ⟨by simpa only [annularQuadratic₀, norm_neg] using h3, ?_, ?_⟩
  · unfold annularQuadratic₁
    apply padic_add_bound (by simpa only [norm_neg] using h2)
    have he : (10 : ℚ_[7]) * correctedForcing₃ / 49 = (10 / 49) * correctedForcing₃ := by ring
    rw [he]
    exact (padic_mul_bound (by rw [norm_div, h10, ClosedAnnulus.norm_fortynine]; norm_num :
      ‖(10 / 49 : ℚ_[7])‖ ≤ 49) h3).trans (by norm_num)
  · rw [annularQuadratic₂_from_constant]
    exact (padic_mul_bound (by rw [norm_neg, norm_div, ClosedAnnulus.norm_fortynine, h10]; norm_num :
      ‖(-(49 / 10) : ℚ_[7])‖ ≤ (1 / 49 : ℝ)) h0).trans (by norm_num)

end Zeta7Annulus

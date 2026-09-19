import Zeta7Proof.AnnularCorrectedCoefficients

/-! The six specified Laurent coefficients and their uniform C=4 normalization.
These are constructed from the original corrected solution and quadratic. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
namespace Zeta7Annulus
local instance AnnularSixCoefficients_prime : Fact (Nat.Prime 7) := ⟨by decide⟩
local instance AnnularSixCoefficients_radius : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
namespace ClosedAnnulus

def reflectedQPolynomial : Polynomial ℚ_[7] := 49 + 13 * Polynomial.X + Polynomial.X ^ 2
def reflectedQ : ClosedAnnulus 1 1 := padicPolynomialMap reflectedQPolynomial
def reflectedPotentialNumerator : ClosedAnnulus 1 1 :=
  monomial 1 (8 * 49) + monomial 2 (8 * 16) + monomial 3 8

theorem reflectedQ_eq : reflectedQ = constant 49 + monomial 1 13 + monomial 2 1 := by
  simp only [reflectedQ, reflectedQPolynomial, map_add, map_mul, map_pow, map_ofNat,
    padicPolynomialMap_X, monomial_Y_pow]
  change (49 : ClosedAnnulus 1 1) + 13 * monomial 1 1 + monomial 2 1 = _
  rw [← map_ofNat constant 49, ← map_ofNat constant 13]
  change constant 49 + monomial 0 13 * monomial 1 1 + monomial 2 1 = _
  rw [monomial_mul]; norm_num

theorem unitCircle_monomial_int_bound (k n : ℤ) :
    ‖monomial (r := 1) (R := 1) k (n : ℚ_[7])‖ ≤ 1 := by
  rw [monomial_norm]
  simpa only [one_zpow, mul_one, max_self] using Padic.norm_int_le_one n

theorem unitCircle_add_bound {a b : ClosedAnnulus 1 1} {C : ℝ}
    (ha : ‖a‖ ≤ C) (hb : ‖b‖ ≤ C) : ‖a + b‖ ≤ C :=
  (norm_add_le_max _ _).trans (max_le ha hb)

theorem unitCircle_mul_bound {a b : ClosedAnnulus 1 1} {A B : ℝ}
    (ha : ‖a‖ ≤ A) (hb : ‖b‖ ≤ B) : ‖a * b‖ ≤ A * B :=
  (norm_mul_le _ _).trans (mul_le_mul ha hb (norm_nonneg _) ((norm_nonneg _).trans ha))

theorem reflectedQ_norm_bound : ‖reflectedQ‖ ≤ 1 := by
  rw [reflectedQ_eq]
  exact unitCircle_add_bound (unitCircle_add_bound
    (unitCircle_monomial_int_bound 0 49) (unitCircle_monomial_int_bound 1 13))
    (unitCircle_monomial_int_bound 2 1)

theorem reflectedPotentialNumerator_norm_bound : ‖reflectedPotentialNumerator‖ ≤ 1 := by
  simpa only [reflectedPotentialNumerator, Int.cast_mul, Int.cast_ofNat, Nat.cast_ofNat] using unitCircle_add_bound (unitCircle_add_bound
    (unitCircle_monomial_int_bound 1 (8 * 49)) (unitCircle_monomial_int_bound 2 (8 * 16)))
    (unitCircle_monomial_int_bound 3 8)

theorem forcingPolynomial_norm_bound :
    ‖padicPolynomialMap (r := 1) (R := 1) annularForcingQuadratic‖ ≤ (2401 : ℝ) := by
  have h := annularQuadratic_bounds
  have he : padicPolynomialMap (r := 1) (R := 1) annularForcingQuadratic =
      constant annularQuadratic₀ + monomial 1 annularQuadratic₁ + monomial 2 annularQuadratic₂ := by
    simp only [annularForcingQuadratic, map_add, padicPolynomialMap_C,
      map_mul, map_pow, padicPolynomialMap_X, monomial_Y_pow]
    change monomial 0 _ + monomial 0 _ * monomial 1 1 + monomial 0 _ * monomial 2 1 = _
    simp only [monomial_mul, zero_add, mul_one]
    rfl
  rw [he]
  apply unitCircle_add_bound
  · apply unitCircle_add_bound
    · simpa only [constant_norm] using h.1.trans (by norm_num : (49 : ℝ) ≤ 2401)
    · simpa only [monomial_norm, one_zpow, mul_one, max_self] using h.2.1
  · simpa only [monomial_norm, one_zpow, mul_one, max_self] using
      h.2.2.trans (by norm_num : (49 : ℝ) ≤ 2401)

theorem forcingDerivative_eq : annularForcingQuadratic.derivative =
    Polynomial.C annularQuadratic₁ + Polynomial.C (2 * annularQuadratic₂) * Polynomial.X := by
  simp only [annularForcingQuadratic, Polynomial.derivative_add, Polynomial.derivative_C,
    Polynomial.derivative_C_mul, Polynomial.derivative_X, Polynomial.derivative_X_pow]
  polynomial

theorem forcingSecondDerivative_eq : annularForcingQuadratic.derivative.derivative =
    Polynomial.C (2 * annularQuadratic₂) := by
  rw [forcingDerivative_eq]
  simp

theorem forcingDerivative_norm_bound :
    ‖padicPolynomialMap (r := 1) (R := 1) annularForcingQuadratic.derivative‖ ≤ (2401 : ℝ) := by
  rw [forcingDerivative_eq, map_add, map_mul, padicPolynomialMap_C,
    padicPolynomialMap_C, padicPolynomialMap_X]
  apply unitCircle_add_bound
  · simpa only [constant_norm] using annularQuadratic_bounds.2.1
  · have hh : ‖constant (r := 1) (R := 1) (2 * annularQuadratic₂)‖ ≤ (2401 : ℝ) := by
      simpa only [constant_norm, Int.cast_ofNat, Nat.cast_ofNat] using (padic_int_mul_bound 2 annularQuadratic_bounds.2.2).trans
        (by norm_num : (49 : ℝ) ≤ 2401)
    simpa only [mul_one, Int.cast_one] using unitCircle_mul_bound hh (unitCircle_monomial_int_bound 1 1)

theorem forcingSecondDerivative_norm_bound :
    ‖padicPolynomialMap (r := 1) (R := 1) annularForcingQuadratic.derivative.derivative‖ ≤ (2401 : ℝ) := by
  rw [forcingSecondDerivative_eq, padicPolynomialMap_C, constant_norm]
  exact (padic_int_mul_bound 2 annularQuadratic_bounds.2.2).trans (by norm_num)

/-- The guide's coefficients in the original six-germ order. The derivatives
of h are ordinary polynomial derivatives; those of v are Euler derivatives. -/
def actualAnnularSix : Fin 6 → ClosedAnnulus 1 1 := ![
  -(reflectedQ ^ 2 * euler (euler reflectedCorrectedSolution)) +
    reflectedPotentialNumerator * reflectedCorrectedSolution,
  reflectedQ ^ 2 * euler reflectedCorrectedSolution,
  -(reflectedQ ^ 2 * reflectedCorrectedSolution),
  reflectedQ ^ 2 * padicPolynomialMap annularForcingQuadratic,
  -(constant 49 * reflectedQ ^ 2 * padicPolynomialMap annularForcingQuadratic.derivative),
  constant (49 ^ 2) * reflectedQ ^ 2 * padicPolynomialMap annularForcingQuadratic.derivative.derivative]

theorem actualAnnularSix_norm_bound (j : Fin 6) : ‖actualAnnularSix j‖ ≤ (2401 : ℝ) := by
  have hq : ‖reflectedQ ^ 2‖ ≤ 1 :=
    (norm_pow_le _ _).trans (pow_le_one₀ (norm_nonneg _) reflectedQ_norm_bound)
  have hv := reflectedCorrectedSolution_norm_bound
  have hd := (euler_norm_le reflectedCorrectedSolution).trans hv
  have hdd := (euler_norm_le (euler reflectedCorrectedSolution)).trans hd
  have h49 : ‖constant (r := 1) (R := 1) 49‖ ≤ 1 := unitCircle_monomial_int_bound 0 49
  have h49sq : ‖constant (r := 1) (R := 1) (49 ^ 2)‖ ≤ 1 :=
    unitCircle_monomial_int_bound 0 (49 ^ 2)
  fin_cases j <;> simp only [actualAnnularSix, Matrix.cons_val_zero', Matrix.cons_val_succ',
    Matrix.head_cons, norm_neg]
  · exact unitCircle_add_bound (by simpa only [norm_neg, one_mul] using unitCircle_mul_bound hq hdd)
      (by simpa only [one_mul] using unitCircle_mul_bound reflectedPotentialNumerator_norm_bound hv)
  · simpa only [one_mul] using unitCircle_mul_bound hq hd
  · simpa only [one_mul] using unitCircle_mul_bound hq hv
  · simpa only [one_mul] using unitCircle_mul_bound hq forcingPolynomial_norm_bound
  · simpa only [one_mul] using unitCircle_mul_bound (unitCircle_mul_bound h49 hq) forcingDerivative_norm_bound
  · simpa only [one_mul] using unitCircle_mul_bound (unitCircle_mul_bound h49sq hq) forcingSecondDerivative_norm_bound

end ClosedAnnulus

def actualAnnularCoefficients (j : Fin 6) : LaurentCoefficients :=
  (ClosedAnnulus.actualAnnularSix j).coeffs

theorem actualAnnularCoefficients_bound (j : Fin 6) (k : ℤ) :
    ‖actualAnnularCoefficients j k‖ ≤ (2401 : ℝ) := by
  have h := (ClosedAnnulus.actualAnnularSix j).coeff_norm_le k
  simp only [one_zpow, mul_one] at h
  exact h.trans (ClosedAnnulus.actualAnnularSix_norm_bound j)

theorem actualAnnularCoefficients_integral (j : Fin 6) (k : ℤ) :
    ‖(7 : ℚ_[7]) ^ 4 * actualAnnularCoefficients j k‖ ≤ 1 := by
  have h7 : ‖(7 : ℚ_[7])‖ = (1 / 7 : ℝ) := by simpa using Padic.norm_p (p := 7)
  have hn : ‖(7 : ℚ_[7]) ^ 4‖ ≤ (1 / 2401 : ℝ) := by rw [norm_pow, h7]; norm_num
  exact (padic_mul_bound hn (actualAnnularCoefficients_bound j k)).trans (by norm_num)

def actualIntegralAnnularCoefficients (j : Fin 6) (k : ℤ) : ℤ_[7] :=
  ⟨7 ^ 4 * actualAnnularCoefficients j k, actualAnnularCoefficients_integral j k⟩

theorem actualIntegralAnnularCoefficients_cast (j : Fin 6) (k : ℤ) :
    (actualIntegralAnnularCoefficients j k : ℚ_[7]) = 7 ^ 4 * actualAnnularCoefficients j k := rfl

end Zeta7Annulus

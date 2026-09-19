import Zeta7Proof.AnnularSixCoefficients
import Zeta7Proof.AnnularSourceConstruction

/-! Coefficientwise comparison with the existing source polynomial convention. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
namespace Zeta7Annulus
local instance AnnularPolynomialCoefficients_prime : Fact (Nat.Prime 7) := ⟨by decide⟩
local instance AnnularPolynomialCoefficients_radius : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
namespace ClosedAnnulus

theorem padicPolynomialMap_coefficients (f : Polynomial ℚ_[7]) :
    (padicPolynomialMap (r := 1) (R := 1) f).coeffs = Zeta7AnnularSource.coeffInt f := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg =>
      funext k
      simp only [map_add, coeffs_add, Pi.add_apply, hf, hg, Zeta7AnnularSource.coeffInt,
        Polynomial.coeff_add]
      split_ifs <;> simp
  | monomial n a =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial, padicPolynomialMap_C_mul_X_pow]
      funext k
      simp only [monomial_coeffs, bilateralMonomial, Zeta7AnnularSource.coeffInt,
        Polynomial.coeff_monomial]
      split_ifs <;> simp_all <;> omega

theorem padicPolynomialMap_injective :
    Function.Injective (padicPolynomialMap (r := 1) (R := 1)) := by
  intro f g h
  apply Polynomial.ext
  intro n
  have hc := congrArg (fun a : ClosedAnnulus 1 1 => a.coeffs (n : ℤ)) h
  simpa only [padicPolynomialMap_coefficients, Zeta7AnnularSource.coeffInt,
    Int.natCast_nonneg, ite_true, Int.toNat_natCast] using hc

def SupportedAbove (a : ClosedAnnulus 1 1) (n : ℤ) : Prop :=
  ∀ k : ℤ, n < k → a.coeffs k = 0

theorem SupportedAbove.add {a b : ClosedAnnulus 1 1} {n : ℤ}
    (ha : SupportedAbove a n) (hb : SupportedAbove b n) : SupportedAbove (a + b) n := by
  intro k hk
  simp only [coeffs_add, Pi.add_apply, ha k hk, hb k hk, add_zero]

theorem SupportedAbove.neg {a : ClosedAnnulus 1 1} {n : ℤ}
    (ha : SupportedAbove a n) : SupportedAbove (-a) n := by
  intro k hk
  simp only [coeffs_neg, Pi.neg_apply, ha k hk, neg_zero]

theorem SupportedAbove.mono {a : ClosedAnnulus 1 1} {m n : ℤ}
    (ha : SupportedAbove a m) (hmn : m ≤ n) : SupportedAbove a n :=
  fun k hk => ha k (hmn.trans_lt hk)

theorem SupportedAbove.mul {a b : ClosedAnnulus 1 1} {m n : ℤ}
    (ha : SupportedAbove a m) (hb : SupportedAbove b n) : SupportedAbove (a * b) (m + n) := by
  intro k hk
  rw [coeffs_mul]
  unfold bilateralConvolution
  have hz (i : ℤ) : a.coeffs i * b.coeffs (k - i) = 0 := by
    by_cases hi : m < i
    · rw [ha i hi, zero_mul]
    · rw [hb (k - i) (by omega), mul_zero]
  simp only [hz, tsum_zero]

theorem SupportedAbove.euler {a : ClosedAnnulus 1 1} {n : ℤ}
    (ha : SupportedAbove a n) : SupportedAbove (euler a) n := by
  intro k hk
  change (k : ℚ_[7]) * a.coeffs k = 0
  rw [ha k hk, mul_zero]

theorem monomial_supported (n : ℤ) (z : ℚ_[7]) :
    SupportedAbove (monomial (r := 1) (R := 1) n z) n := by
  intro k hk
  simp only [monomial_coeffs, bilateralMonomial, if_neg (ne_of_gt hk)]

theorem polynomial_supported (f : Polynomial ℚ_[7]) (n : ℕ) (hf : f.natDegree ≤ n) :
    SupportedAbove (padicPolynomialMap f) (n : ℤ) := by
  intro k hk
  rw [padicPolynomialMap_coefficients]
  simp only [Zeta7AnnularSource.coeffInt, if_pos (by omega : 0 ≤ k)]
  exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)

theorem actualAnnularSix_supported (j : Fin 6) : SupportedAbove (actualAnnularSix j) 6 := by
  have hq : SupportedAbove reflectedQ 2 := by
    apply polynomial_supported reflectedQPolynomial 2
    unfold reflectedQPolynomial
    compute_degree!
  have hq2 : SupportedAbove (reflectedQ ^ 2) 4 := by
    simpa only [pow_two, Int.reduceAdd] using hq.mul hq
  have hv : SupportedAbove reflectedCorrectedSolution 2 := fun _ hk => reflectedCorrectedSolution_above hk
  have hf : SupportedAbove reflectedPotentialNumerator 3 :=
    ((monomial_supported 1 _).mono (by norm_num)).add
      ((monomial_supported 2 _).mono (by norm_num)) |>.add (monomial_supported 3 _)
  have hh : SupportedAbove (padicPolynomialMap annularForcingQuadratic) 2 :=
    polynomial_supported _ _ annularForcingQuadratic_degree
  have hh1 : SupportedAbove (padicPolynomialMap annularForcingQuadratic.derivative) 2 :=
    polynomial_supported _ _ ((Polynomial.natDegree_derivative_le _).trans
      ((Nat.sub_le _ _).trans annularForcingQuadratic_degree))
  have hh2 : SupportedAbove (padicPolynomialMap annularForcingQuadratic.derivative.derivative) 2 :=
    polynomial_supported _ _ (by
      have h1 := Polynomial.natDegree_derivative_le annularForcingQuadratic
      have h2 := Polynomial.natDegree_derivative_le annularForcingQuadratic.derivative
      have h3 := annularForcingQuadratic_degree
      omega)
  fin_cases j <;> simp only [actualAnnularSix, Matrix.cons_val_zero', Matrix.cons_val_succ',
    Matrix.head_cons]
  · exact (hq2.mul hv.euler.euler).neg.add ((hf.mul hv).mono (by norm_num))
  · exact hq2.mul hv.euler
  · exact (hq2.mul hv).neg
  · exact hq2.mul hh
  · exact (((monomial_supported 0 49).mul hq2).mul hh1).neg
  · exact ((monomial_supported 0 (49 ^ 2)).mul hq2).mul hh2

end ClosedAnnulus

theorem actualAnnularCoefficients_above (j : Fin 6) (k : ℤ) (hk : 6 < k) :
    actualAnnularCoefficients j k = 0 := ClosedAnnulus.actualAnnularSix_supported j k hk

end Zeta7Annulus

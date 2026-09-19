import Zeta7Proof.N4ConnectionFour

/-! Exact polynomial denominators and degree bounds for the actual N4
connection entries. The quadratic primitive multiplier costs two degrees. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
open scoped RatFunc
open Polynomial
namespace Zeta7Germ

theorem R_cleared_polynomial : P * R = (polynomialS : RatFunc ℂ) := by
  simp only [R, polynomialS, RatFunc.coePolynomial_eq_algebraMap, map_mul,
    map_add, map_one, map_ofNat, RatFunc.algebraMap_X]
  field_simp [P_ne_zero]

def clearedR : Polynomial ℂ := polynomialP ^ 2 * polynomialS
def clearedV : Polynomial ℂ := polynomialP * polynomialW
def clearedHalfDV : Polynomial ℂ := -polynomialT
def clearedPrimitive (a : Fin 3 → ℂ) : Polynomial ℂ :=
  clearedR * constantPrimitivePolynomial a

theorem clearedR_cast : (clearedR : RatFunc ℂ) = P ^ 3 * R := by
  simp only [clearedR, RatFunc.coePolynomial_eq_algebraMap, map_mul, map_pow]
  simp only [← RatFunc.coePolynomial_eq_algebraMap, polynomialP_cast]
  rw [← R_cleared_polynomial]
  ring

theorem clearedV_cast : (clearedV : RatFunc ℂ) = P ^ 3 * V := by
  simp only [clearedV, RatFunc.coePolynomial_eq_algebraMap, map_mul]
  simp only [← RatFunc.coePolynomial_eq_algebraMap, polynomialP_cast]
  rw [← V_cleared_polynomial]
  ring

theorem clearedHalfDV_cast : (clearedHalfDV : RatFunc ℂ) = P ^ 3 * (rationalD V / 2) := by
  have hd := DV_cleared_polynomial
  simp only [clearedHalfDV, polynomialT, RatFunc.coePolynomial_eq_algebraMap,
    map_neg, map_sub, map_mul, RatFunc.algebraMap_C, map_div₀, map_one, map_ofNat]
  simp only [← RatFunc.coePolynomial_eq_algebraMap, polynomialP_cast]
  linear_combination -hd / 2

theorem clearedPrimitive_cast (a : Fin 3 → ℂ) :
    (clearedPrimitive a : RatFunc ℂ) =
      P ^ 3 * (primitiveMultiplier (fun i => RatFunc.C (a i)) * R) := by
  simp only [clearedPrimitive, RatFunc.coePolynomial_eq_algebraMap, map_mul]
  simp only [← RatFunc.coePolynomial_eq_algebraMap, clearedR_cast, constantPrimitivePolynomial_cast]
  ring

theorem polynomialP_cube_degree : (polynomialP ^ 3).natDegree ≤ 6 := by
  simpa [polynomialP_degree] using natDegree_pow_le (p := polynomialP) (n := 3)

theorem clearedR_degree : clearedR.natDegree ≤ 6 := by
  have hp : (polynomialP ^ 2).natDegree ≤ 4 := by
    simpa [polynomialP_degree] using natDegree_pow_le (p := polynomialP) (n := 2)
  exact natDegree_mul_le.trans (add_le_add hp polynomialS_degree)

theorem clearedV_degree : clearedV.natDegree ≤ 5 := by
  exact natDegree_mul_le.trans (add_le_add polynomialP_degree.le polynomialW_degree)

theorem clearedHalfDV_degree : clearedHalfDV.natDegree ≤ 5 := by
  simpa [clearedHalfDV] using polynomialT_degree

theorem clearedPrimitive_degree (a : Fin 3 → ℂ) :
    (clearedPrimitive a).natDegree ≤ 8 :=
  natDegree_mul_le.trans (add_le_add clearedR_degree (constantPrimitivePolynomial_degree a))

/-- Every actual scalar entry in the constant-primitive frame clears with
P cubed and costs at most eight degrees. This is not a zero estimate. -/
theorem actual_connection_entries_clear (a : Fin 3 → ℂ) :
    ∃ (p₀ pR pV pDV ph : Polynomial ℂ),
      (p₀ : RatFunc ℂ) = P ^ 3 ∧
      (pR : RatFunc ℂ) = P ^ 3 * R ∧
      (pV : RatFunc ℂ) = P ^ 3 * V ∧
      (pDV : RatFunc ℂ) = P ^ 3 * (rationalD V / 2) ∧
      (ph : RatFunc ℂ) = P ^ 3 *
        (primitiveMultiplier (fun i => RatFunc.C (a i)) * R) ∧
      p₀.natDegree ≤ 8 ∧ pR.natDegree ≤ 8 ∧ pV.natDegree ≤ 8 ∧
      pDV.natDegree ≤ 8 ∧ ph.natDegree ≤ 8 := by
  refine ⟨polynomialP ^ 3, clearedR, clearedV, clearedHalfDV, clearedPrimitive a,
    ?_, clearedR_cast, clearedV_cast, clearedHalfDV_cast, clearedPrimitive_cast a,
    polynomialP_cube_degree.trans (by omega), clearedR_degree.trans (by omega),
    clearedV_degree.trans (by omega), clearedHalfDV_degree.trans (by omega),
    clearedPrimitive_degree a⟩
  simp only [RatFunc.coePolynomial_eq_algebraMap, map_pow]
  simp only [← RatFunc.coePolynomial_eq_algebraMap, polynomialP_cast]

/-- The scalar correction incurred by clearing the kth derivative row. -/
def clearingCorrection (k : ℕ) : Polynomial ℂ :=
  C (3 * (k : ℂ)) * polynomialP ^ 2 * polynomialD polynomialP

theorem clearingCorrection_degree (k : ℕ) : (clearingCorrection k).natDegree ≤ 6 := by
  have hp : (polynomialP ^ 2).natDegree ≤ 4 := by
    simpa [polynomialP_degree] using natDegree_pow_le (p := polynomialP) (n := 2)
  have hc : (C (3 * (k : ℂ)) * polynomialP ^ 2).natDegree ≤ 4 :=
    (natDegree_C_mul_le _ _).trans hp
  exact natDegree_mul_le.trans (add_le_add hc
    ((polynomialD_degree_le _).trans polynomialP_degree.le))

theorem clearing_derivative_degree (p : Polynomial ℂ) :
    (polynomialP ^ 3 * polynomialD p).natDegree ≤ p.natDegree + 6 := by
  exact natDegree_mul_le.trans (by
    have := polynomialP_cube_degree
    have := polynomialD_degree_le p
    omega)

end Zeta7Germ

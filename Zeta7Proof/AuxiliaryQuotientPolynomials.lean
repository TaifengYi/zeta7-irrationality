import Zeta7Proof.RiccatiRationalAlgebra
import Mathlib

/-! Exact clearing polynomials for every weighted E4/E6 monomial. -/
noncomputable section
set_option autoImplicit false
namespace Zeta7Auxiliary
open Polynomial Zeta7Riccati

theorem quotient_P_degree : P.natDegree = 2 := by
  unfold P Zeta7Stage2B.p
  compute_degree!
theorem quotient_N_degree : N.natDegree = 2 := by unfold N; compute_degree!
theorem quotient_T_degree : T.natDegree = 4 := by unfold T; compute_degree!
theorem quotient_P_lead : P.leadingCoeff = 49 := by
  rw [Polynomial.leadingCoeff, quotient_P_degree]
  norm_num [P, Zeta7Stage2B.p, coeff_add, coeff_mul, coeff_one, coeff_X]
theorem quotient_N_lead : N.leadingCoeff = 2401 := by
  rw [Polynomial.leadingCoeff, quotient_N_degree]
  norm_num [N, coeff_add, coeff_mul, coeff_one, coeff_X]
theorem quotient_T_lead : T.leadingCoeff = -823543 := by
  rw [Polynomial.leadingCoeff, quotient_T_degree]
  norm_num [T, coeff_sub, coeff_mul, coeff_one, coeff_X]
theorem quotient_P_ne_zero : P ≠ 0 := by
  intro h; have := quotient_P_degree; simp [h] at this
theorem quotient_N_ne_zero : N ≠ 0 := by
  intro h; have := quotient_N_degree; simp [h] at this
theorem quotient_T_ne_zero : T ≠ 0 := by
  intro h; have := quotient_T_degree; simp [h] at this

def quotientMonomial (s a b : ℕ) : Polynomial ℚ := P ^ (s - a - 2*b) * N^a * T^b

theorem quotientMonomial_constant (s a b : ℕ) : (quotientMonomial s a b).coeff 0 = 1 := by
  change constantCoeff (quotientMonomial s a b) = 1
  simp only [quotientMonomial, map_mul, map_pow]
  norm_num [P, Zeta7Stage2B.p, N, T]

theorem monomial_denominator_bound {n a b : ℕ} (h : 2*a + 3*b = n) :
    a + 2*b ≤ 2*n/3 := by omega

theorem quotientMonomial_degree (s a b : ℕ) (h : a + 2*b ≤ s) :
    (quotientMonomial s a b).natDegree = 2*s := by
  simp only [quotientMonomial, natDegree_mul
    (mul_ne_zero (pow_ne_zero _ quotient_P_ne_zero) (pow_ne_zero _ quotient_N_ne_zero))
    (pow_ne_zero _ quotient_T_ne_zero),
    natDegree_mul (pow_ne_zero _ quotient_P_ne_zero) (pow_ne_zero _ quotient_N_ne_zero),
    natDegree_pow, quotient_P_degree, quotient_N_degree, quotient_T_degree]
  omega

theorem quotientMonomial_lead (s a b : ℕ) (h : a + 2*b ≤ s) :
    (quotientMonomial s a b).leadingCoeff = 49^s * (-7:ℚ)^(2*a+3*b) := by
  simp only [quotientMonomial, leadingCoeff_mul, leadingCoeff_pow,
    quotient_P_lead, quotient_N_lead, quotient_T_lead]
  have hs : s = (s-a-2*b) + a + 2*b := by omega
  rw [show (2401:ℚ)=49^2 by norm_num,
    show (-823543:ℚ)=49^2 * (-7)^3 by norm_num]
  conv_rhs => rw [hs]
  simp only [pow_add, mul_pow, ← pow_mul]
  have h7 : (-7:ℚ)^(2*a) = 49^a := by rw [pow_mul]; norm_num
  rw [h7]
  ring

theorem quotientMonomial_top (s a b : ℕ) (h : a + 2*b ≤ s) :
    (quotientMonomial s a b).coeff (2*s) = 49^s * (-7:ℚ)^(2*a+3*b) := by
  rw [← quotientMonomial_degree s a b h]
  exact quotientMonomial_lead s a b h

end Zeta7Auxiliary

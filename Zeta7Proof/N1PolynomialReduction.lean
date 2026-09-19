import Zeta7Proof.ActualFinitePoleExclusion
import Zeta7Proof.GermLPObstruction

/-! The degree comparison at infinity, using a denominator-cleared polynomial identity. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
open scoped RatFunc LaurentSeries
open Polynomial
namespace Zeta7Germ

def polynomialD (p : Polynomial ℂ) : Polynomial ℂ := X * p.derivative
def polynomialP : Polynomial ℂ := 1 + 13 * X + 49 * X ^ 2
def polynomialW : Polynomial ℂ := 8 * X * (1 + 16 * X + 49 * X ^ 2)
def polynomialS : Polynomial ℂ := X * (1 + 10 * X)
def polynomialT : Polynomial ℂ :=
  polynomialW * polynomialD polynomialP - C (1 / 2) * polynomialP * polynomialD polynomialW

theorem polynomialD_coeff (p : Polynomial ℂ) (n : ℕ) :
    (polynomialD p).coeff n = (n : ℂ) * p.coeff n := by
  cases n with
  | zero => simp [polynomialD]
  | succ n => simp [polynomialD, coeff_X_mul, coeff_derivative, mul_comm]

theorem polynomialD_degree_le (p : Polynomial ℂ) : (polynomialD p).natDegree ≤ p.natDegree := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  rw [polynomialD_coeff, coeff_eq_zero_of_natDegree_lt hn, mul_zero]

theorem polynomialP_cast : (polynomialP : RatFunc ℂ) = P := by
  simp [polynomialP, P, RatFunc.coePolynomial_eq_algebraMap, map_ofNat]

theorem V_cleared_polynomial : P ^ 2 * V = (polynomialW : RatFunc ℂ) := by
  simp only [V, polynomialW, RatFunc.coePolynomial_eq_algebraMap,
    map_mul, map_add, map_one, map_pow, map_ofNat, RatFunc.algebraMap_X]
  field_simp [P_ne_zero]

theorem DV_cleared_polynomial :
    P ^ 3 * rationalD V = P * (polynomialD polynomialW : RatFunc ℂ) -
      2 * (polynomialW : RatFunc ℂ) * (polynomialD polynomialP : RatFunc ℂ) := by
  have he := congrArg rationalD V_cleared_polynomial
  have hdP : rationalD P = (polynomialD polynomialP : RatFunc ℂ) := by
    rw [← polynomialP_cast, rationalD_polynomial]
    rfl
  rw [rationalD_polynomial] at he
  change rationalD (P ^ 2 * V) = (polynomialD polynomialW : RatFunc ℂ) at he
  simp only [Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, hdP] at he
  linear_combination P * he - 2 * (polynomialD polynomialP : RatFunc ℂ) *
    V_cleared_polynomial

theorem polynomial_solution_cleared (p h : Polynomial ℂ)
    (he : L (p : RatFunc ℂ) = (h : RatFunc ℂ) * R) :
    polynomialP ^ 3 * polynomialD (polynomialD (polynomialD p)) -
      polynomialP * polynomialW * polynomialD p + polynomialT * p =
      polynomialS * polynomialP ^ 2 * h := by
  have hd (q : Polynomial ℂ) : rationalD (q : RatFunc ℂ) = (polynomialD q : RatFunc ℂ) :=
    rationalD_polynomial q
  have hr : P * R = (polynomialS : RatFunc ℂ) := by
    simp only [R, polynomialS, RatFunc.coePolynomial_eq_algebraMap, map_mul,
      map_add, map_one, map_ofNat, RatFunc.algebraMap_X]
    field_simp [P_ne_zero]
  simp only [L, hd] at he
  apply IsFractionRing.injective (Polynomial ℂ) (RatFunc ℂ)
  simp only [polynomialT, map_add, map_sub, map_mul, map_pow, map_div₀,
    RatFunc.algebraMap_C, map_ofNat, map_one,
    ← RatFunc.coePolynomial_eq_algebraMap, polynomialP_cast]
  simp only [RatFunc.coePolynomial_eq_algebraMap] at he hr ⊢
  have hv := V_cleared_polynomial
  have hdv := DV_cleared_polynomial
  simp only [RatFunc.coePolynomial_eq_algebraMap] at hv hdv
  simp only [RatFunc.algebraMap_C, map_div₀, map_one, map_ofNat]
  linear_combination P ^ 3 * he + P ^ 2 * (algebraMap (Polynomial ℂ) (RatFunc ℂ) h) * hr +
    P * (algebraMap (Polynomial ℂ) (RatFunc ℂ) (polynomialD p)) * hv +
    (algebraMap (Polynomial ℂ) (RatFunc ℂ) p) / 2 * hdv

theorem polynomialP_degree : polynomialP.natDegree = 2 := by
  unfold polynomialP
  compute_degree!

theorem polynomialW_degree : polynomialW.natDegree ≤ 3 := by
  unfold polynomialW
  compute_degree!

theorem polynomialS_degree : polynomialS.natDegree ≤ 2 := by
  unfold polynomialS
  compute_degree!

theorem polynomialT_degree : polynomialT.natDegree ≤ 5 := by
  apply (natDegree_sub_le _ _).trans
  apply max_le
  · exact (natDegree_mul_le).trans (by
      have := polynomialD_degree_le polynomialP
      have := polynomialW_degree
      rw [polynomialP_degree] at *
      omega)
  · apply natDegree_mul_le.trans
    have hleft : (C (1 / 2 : ℂ) * polynomialP).natDegree ≤ 2 := by
      simpa [polynomialP_degree] using natDegree_C_mul_le (1 / 2 : ℂ) polynomialP
    have := polynomialD_degree_le polynomialW
    have := polynomialW_degree
    omega

theorem polynomial_solution_degree_le_two (p h : Polynomial ℂ) (hh : h.natDegree ≤ 2)
    (he : L (p : RatFunc ℂ) = (h : RatFunc ℂ) * R) : p.natDegree ≤ 2 := by
  by_contra hdeg
  have hm : 2 < p.natDegree := by omega
  have heq := polynomial_solution_cleared p h he
  have hD := polynomialD_degree_le p
  have hD2 := (polynomialD_degree_le (polynomialD p)).trans hD
  have hD3 := (polynomialD_degree_le (polynomialD (polynomialD p))).trans hD2
  have hP3 : (polynomialP ^ 3).natDegree ≤ 6 := by
    simpa [polynomialP_degree] using natDegree_pow_le (p := polynomialP) (n := 3)
  have hP2 : (polynomialP ^ 2).natDegree ≤ 4 := by
    simpa [polynomialP_degree] using natDegree_pow_le (p := polynomialP) (n := 2)
  have hPW : (polynomialP * polynomialW).natDegree ≤ 5 :=
    natDegree_mul_le.trans (by have := polynomialW_degree; rw [polynomialP_degree]; omega)
  have hterm1 : (polynomialP * polynomialW * polynomialD p).natDegree < 6 + p.natDegree :=
    lt_of_le_of_lt (natDegree_mul_le.trans (add_le_add hPW hD)) (by omega)
  have hterm2 : (polynomialT * p).natDegree < 6 + p.natDegree :=
    lt_of_le_of_lt ((natDegree_mul_le (p := polynomialT) (q := p)).trans
      (add_le_add polynomialT_degree (le_refl p.natDegree))) (by omega)
  have hrhs : (polynomialS * polynomialP ^ 2 * h).natDegree < 6 + p.natDegree := by
    have hsp : (polynomialS * polynomialP ^ 2).natDegree ≤ 6 :=
      natDegree_mul_le.trans (add_le_add polynomialS_degree hP2)
    exact lt_of_le_of_lt (natDegree_mul_le.trans (add_le_add hsp hh)) (by omega)
  have hc := congrArg (fun q : Polynomial ℂ => q.coeff (6 + p.natDegree)) heq
  rw [coeff_add, coeff_sub, coeff_eq_zero_of_natDegree_lt hterm1,
    coeff_eq_zero_of_natDegree_lt hterm2, coeff_eq_zero_of_natDegree_lt hrhs,
    sub_zero, add_zero, coeff_mul_add_eq_of_natDegree_le hP3 hD3,
    polynomialD_coeff, polynomialD_coeff, polynomialD_coeff] at hc
  have hpc : (polynomialP ^ 3).coeff 6 = 117649 := by
    norm_num [polynomialP, pow_succ, coeff_mul, Finset.Nat.antidiagonal_succ,
      Finset.Nat.antidiagonal_zero, coeff_add, coeff_C, coeff_X, coeff_X_pow, coeff_one]
  rw [hpc] at hc
  have hp : p ≠ 0 := fun hz => by simp [hz] at hm
  have hlc : p.coeff p.natDegree ≠ 0 := by simpa [coeff_natDegree] using leadingCoeff_ne_zero.mpr hp
  have hm0 : (p.natDegree : ℂ) ≠ 0 := by exact_mod_cast (show p.natDegree ≠ 0 by omega)
  exact (mul_ne_zero (by norm_num) (mul_ne_zero hm0 (mul_ne_zero hm0
    (mul_ne_zero hm0 hlc)))) hc

end Zeta7Germ

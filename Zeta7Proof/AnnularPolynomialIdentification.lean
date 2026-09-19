import Zeta7Proof.AnnularSubstitution

/-! Exact identification of the annular P, N, T with the existing rational
polynomials used by the actual modular calculation. These are polynomial
equalities under a ring homomorphism, not finite coefficient comparisons. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
namespace Zeta7Annulus.ClosedAnnulus
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩
variable {r R : ℝ} [Fact (0 < r)] [Fact (0 < R)]

def rationalPolynomialMap : Polynomial ℚ →+* ClosedAnnulus r R :=
  Polynomial.eval₂RingHom (constant.comp (algebraMap ℚ ℚ_[7])) (monomial 1 1)

theorem rationalPolynomialMap_X : rationalPolynomialMap (r := r) (R := R) Polynomial.X =
    monomial 1 1 := Polynomial.eval₂_X _ _

theorem monomial_Y_pow (n : ℕ) : (monomial (r := r) (R := R) 1 1) ^ n = monomial n 1 := by
  induction n with
  | zero => exact monomial_zero_one.symm
  | succ n ih =>
      rw [pow_succ, ih, monomial_mul]
      simp only [Nat.cast_add, Nat.cast_one, one_mul]

theorem constant_mul_Y_pow (q : ℚ_[7]) (n : ℕ) :
    constant (r := r) (R := R) q * (monomial 1 1) ^ n = monomial n q := by
  rw [monomial_Y_pow]
  change monomial (r := r) (R := R) 0 q * monomial n 1 = monomial n q
  rw [monomial_mul, zero_add, mul_one]

theorem rationalPolynomialMap_nat_mul_X_pow (n k : ℕ) :
    rationalPolynomialMap (r := r) (R := R) ((n : Polynomial ℚ) * Polynomial.X ^ k) =
      monomial k (n : ℚ_[7]) := by
  rw [map_mul, map_natCast, map_pow, rationalPolynomialMap_X,
    ← map_natCast (constant (r := r) (R := R))]
  exact constant_mul_Y_pow _ _

theorem rationalPolynomialMap_nat_mul_X (n : ℕ) :
    rationalPolynomialMap (r := r) (R := R) ((n : Polynomial ℚ) * Polynomial.X) =
      monomial 1 (n : ℚ_[7]) := by
  simpa only [pow_one, Nat.cast_one] using rationalPolynomialMap_nat_mul_X_pow (r := r) (R := R) n 1

theorem monomial_neg (n : ℤ) (z : ℚ_[7]) :
    monomial (r := r) (R := R) n (-z) = -monomial n z := by
  ext k
  simp only [monomial_coeffs, coeffs_neg, Pi.neg_apply, bilateralMonomial]
  split_ifs <;> simp

theorem annularP_polynomial : annularP (r := r) (R := R) =
    rationalPolynomialMap Zeta7Riccati.P := by
  simp only [Zeta7Riccati.P, Zeta7Stage2B.p, map_add, map_one,
    ← Nat.cast_ofNat (R := Polynomial ℚ), rationalPolynomialMap_nat_mul_X,
    rationalPolynomialMap_nat_mul_X_pow, annularP]
  norm_num only [Nat.cast_ofNat]

theorem annularN_polynomial : annularN (r := r) (R := R) =
    rationalPolynomialMap Zeta7Riccati.N := by
  simp only [Zeta7Riccati.N, map_add, map_one,
    ← Nat.cast_ofNat (R := Polynomial ℚ), rationalPolynomialMap_nat_mul_X,
    rationalPolynomialMap_nat_mul_X_pow, annularN]
  norm_num only [Nat.cast_ofNat]

theorem annularT_polynomial : annularT (r := r) (R := R) =
    rationalPolynomialMap Zeta7Riccati.T := by
  simp only [Zeta7Riccati.T, map_sub, map_add, map_neg, map_one,
    ← Nat.cast_ofNat (R := Polynomial ℚ), rationalPolynomialMap_nat_mul_X,
    rationalPolynomialMap_nat_mul_X_pow, annularT,
    monomial_neg, sub_eq_add_neg]
  norm_num only [Nat.cast_ofNat]

end Zeta7Annulus.ClosedAnnulus

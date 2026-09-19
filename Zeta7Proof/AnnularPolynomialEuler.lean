import Zeta7Proof.AnnularEulerRules

/-! Euler differentiation of the actual polynomial evaluation and its P/N units. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
namespace Zeta7Annulus.ClosedAnnulus
local instance AnnularPolynomialEuler_local1 : Fact (Nat.Prime 7) := ⟨by decide⟩
variable {r R : ℝ} [Fact (0 < r)] [Fact (0 < R)]

theorem rationalPolynomialMap_C (a : ℚ) :
    rationalPolynomialMap (r := r) (R := R) (Polynomial.C a) = constant (a : ℚ_[7]) :=
  Polynomial.eval₂_C _ _

theorem euler_polynomial (f : Polynomial ℚ) :
    euler (rationalPolynomialMap (r := r) (R := R) f) =
      rationalPolynomialMap (Zeta7Riccati.theta f) := by
  induction f using Polynomial.induction_on with
  | C a => simp [rationalPolynomialMap_C, Zeta7Riccati.theta]
  | add f g hf hg =>
      simp only [map_add, euler_add, hf, hg, Zeta7Riccati.theta,
        Polynomial.derivative_add, mul_add]
  | monomial n a _ =>
      simp only [map_mul, map_pow, rationalPolynomialMap_C, rationalPolynomialMap_X,
        euler_constant_mul, euler_pow_succ, euler_monomial, Int.cast_one, one_mul,
        Zeta7Riccati.theta, Polynomial.derivative_mul, Polynomial.derivative_C,
        zero_mul, zero_add, Polynomial.derivative_pow, Polynomial.derivative_X,
        mul_one, rationalPolynomialMap_C]
      push_cast
      simp only [map_add, map_one, map_natCast]
      ring

theorem euler_pInverse (hr : 1 < r) (hR : R < 49) (hrR : r ≤ R) :
    euler (pInverse (r := r) (R := R)) =
      -(pInverse ^ 2 * rationalPolynomialMap (Zeta7Riccati.theta Zeta7Riccati.P)) := by
  rw [euler_inverse _ _ (annularP_mul_inverse hr hR hrR), annularP_polynomial,
    euler_polynomial]

theorem euler_nInverse (hr : 1 < r) (hR : R < 49) (hrR : r ≤ R) :
    euler (nInverse (r := r) (R := R)) =
      -(nInverse ^ 2 * rationalPolynomialMap (Zeta7Riccati.theta Zeta7Riccati.N)) := by
  rw [euler_inverse _ _ (annularN_mul_inverse hr hR hrR), annularN_polynomial,
    euler_polynomial]

end Zeta7Annulus.ClosedAnnulus

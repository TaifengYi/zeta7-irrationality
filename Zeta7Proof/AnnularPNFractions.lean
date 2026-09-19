import Zeta7Proof.AnnularPolynomialEuler

/-! Only P/N fractions are evaluated. The clearing and differentiation rules
use the previously constructed units on the actual annulus. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
namespace Zeta7Annulus.ClosedAnnulus
local instance AnnularPNFractions_local1 : Fact (Nat.Prime 7) := ⟨by decide⟩
variable {r R : ℝ} [Fact (0 < r)] [Fact (0 < R)]

def pnDenominator (a b : ℕ) : ClosedAnnulus r R := annularP ^ a * annularN ^ b

def pnFraction (f : Polynomial ℚ) (a b : ℕ) : ClosedAnnulus r R :=
  rationalPolynomialMap f * pInverse ^ a * nInverse ^ b

theorem pnDenominator_isUnit (hr : 1 < r) (hR : R < 49) (hrR : r ≤ R) (a b : ℕ) :
    IsUnit (pnDenominator (r := r) (R := R) a b) :=
  ((annularP_isUnit hr hR hrR).pow a).mul ((annularN_isUnit hr hR hrR).pow b)

theorem pnFraction_clear (hr : 1 < r) (hR : R < 49) (hrR : r ≤ R)
    (f : Polynomial ℚ) (a b : ℕ) :
    pnDenominator a b * pnFraction (r := r) (R := R) f a b = rationalPolynomialMap f := by
  unfold pnDenominator pnFraction
  calc
    _ = rationalPolynomialMap f * (annularP * pInverse) ^ a * (annularN * nInverse) ^ b := by
      simp only [mul_pow]; ring
    _ = _ := by rw [annularP_mul_inverse hr hR hrR, annularN_mul_inverse hr hR hrR]; simp

theorem euler_pow_mul (f : ClosedAnnulus r R) (n : ℕ) :
    euler (f ^ n) * f = (n : ClosedAnnulus r R) * f ^ n * euler f := by
  cases n with
  | zero => simp
  | succ n => rw [euler_pow_succ, pow_succ]; push_cast; ring

theorem pnDenominator_euler (a b : ℕ) :
    euler (pnDenominator (r := r) (R := R) a b) * annularP * annularN =
      pnDenominator a b *
        ((a : ClosedAnnulus r R) * euler annularP * annularN +
          (b : ClosedAnnulus r R) * annularP * euler annularN) := by
  have hp := euler_pow_mul (annularP (r := r) (R := R)) a
  have hn := euler_pow_mul (annularN (r := r) (R := R)) b
  simp only [pnDenominator, euler_mul]
  linear_combination (annularN ^ b * annularN) * hp + (annularP ^ a * annularP) * hn

theorem pnFraction_euler_clear (hr : 1 < r) (hR : R < 49) (hrR : r ≤ R)
    (f : Polynomial ℚ) (a b : ℕ) :
    pnDenominator a b * annularP * annularN * euler (pnFraction (r := r) (R := R) f a b) =
      rationalPolynomialMap (Zeta7Riccati.theta f * Zeta7Riccati.P * Zeta7Riccati.N -
        f * ((a : Polynomial ℚ) * Zeta7Riccati.theta Zeta7Riccati.P * Zeta7Riccati.N +
          (b : Polynomial ℚ) * Zeta7Riccati.P * Zeta7Riccati.theta Zeta7Riccati.N)) := by
  have hc := pnFraction_clear hr hR hrR f a b
  have hd := congrArg euler hc
  rw [euler_mul, euler_polynomial] at hd
  have hden := pnDenominator_euler (r := r) (R := R) a b
  have hp : euler (annularP (r := r) (R := R)) =
      rationalPolynomialMap (Zeta7Riccati.theta Zeta7Riccati.P) := by
    rw [annularP_polynomial, euler_polynomial]
  have hn : euler (annularN (r := r) (R := R)) =
      rationalPolynomialMap (Zeta7Riccati.theta Zeta7Riccati.N) := by
    rw [annularN_polynomial, euler_polynomial]
  simp only [map_sub, map_add, map_mul, map_natCast, ← annularP_polynomial,
    ← annularN_polynomial, ← hp, ← hn]
  linear_combination (annularP * annularN) * hd - (pnFraction f a b) * hden -
    ((a : ClosedAnnulus r R) * euler annularP * annularN +
      (b : ClosedAnnulus r R) * annularP * euler annularN) * hc

end Zeta7Annulus.ClosedAnnulus

import Zeta7Proof.AnnularRowBaseIdentities

noncomputable section
set_option autoImplicit false
namespace Zeta7AnnularBand
open Polynomial
open Zeta7Riccati

def b₃ : Polynomial ℚ := 1 + 26 * X + 267 * X ^ 2 + 1274 * X ^ 3 + 2401 * X ^ 4
def b₂ : Polynomial ℚ := 39 * X + 801 * X ^ 2 + 5733 * X ^ 3 + 14406 * X ^ 4
def b₁ : Polynomial ℚ := 31 * X + 967 * X ^ 2 + 9163 * X ^ 3 + 28812 * X ^ 4
def b₀ : Polynomial ℚ := 9 * X + 433 * X ^ 2 + 5145 * X ^ 3 + 19208 * X ^ 4

theorem band_polynomial_3 : P ^ 2 = b₃ := by
  simp only [P, Zeta7Stage2B.p, b₃]; ring
theorem band_polynomial_2 : 3 * P * theta P = b₂ := by
  simp [P, Zeta7Stage2B.p, b₂, theta, Polynomial.derivative_pow, map_ofNat]; ring
theorem band_polynomial_1 : 3 * P * theta (theta P) - Zeta7AnnularRows.raw_V = b₁ := by
  simp [P, Zeta7Stage2B.p, b₁, theta, Zeta7AnnularRows.raw_V,
    Polynomial.derivative_pow, Polynomial.derivative_mul, map_ofNat]; ring
theorem band_polynomial_0 : P ^ 2 * theta (theta (theta P)) -
    Zeta7AnnularRows.raw_V * theta P - C (1 / 2 : ℚ) * Zeta7AnnularRows.raw_dV = P * b₀ := by
  simp [P, Zeta7Stage2B.p, b₀, theta, Zeta7AnnularRows.raw_V, Zeta7AnnularRows.raw_dV,
    Polynomial.derivative_pow, Polynomial.derivative_mul, map_ofNat]
  polynomial

end Zeta7AnnularBand

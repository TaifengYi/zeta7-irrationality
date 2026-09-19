import Stage2B

/-! The denominator-cleared rational algebra in Section 1.1, equation (2).
This establishes the asserted calculation of V from s0 and a0. It does not
identify E2/A or E4/A^2 with the displayed rational functions. -/
set_option autoImplicit false
noncomputable section
namespace Zeta7Riccati
open Polynomial
abbrev P : Polynomial ℚ := Zeta7Stage2B.p
def N : Polynomial ℚ := 1 + 245 * X + 2401 * X ^ 2
def T : Polynomial ℚ :=
  1 - 490 * X - 21609 * X ^ 2 - 235298 * X ^ 3 - 823543 * X ^ 4

def theta (f : Polynomial ℚ) : Polynomial ℚ := X * f.derivative

/-- Numerator of s0=3Dlog(N/P)+T/(PN), with denominator PN. -/
def sNumerator : Polynomial ℚ := 3 * (theta N * P - theta P * N) + T

/-- Complete polynomial identity, so no finite jet comparison is being used. -/
theorem riccati_cleared :
    sNumerator ^ 2 - P * N ^ 3 -
      12 * (theta sNumerator * (P * N) - sNumerator * theta (P * N)) =
      288 * X * (1 + 16 * X + 49 * X ^ 2) * N ^ 2 := by
  simp [sNumerator, theta, P, Zeta7Stage2B.p, N, T,
    Polynomial.derivative_mul, Polynomial.derivative_pow, map_ofNat]
  ring

/-- The numerator difference in E4/A²-E4(7τ)/A² is exactly 240x(1+10x). -/
theorem forcing_numerator :
    N - (1 + 5 * X + X ^ 2) = 240 * X * (1 + 10 * X) := by
  unfold N
  ring

end Zeta7Riccati

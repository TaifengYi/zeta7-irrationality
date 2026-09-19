import Zeta7Proof.AnnularRowPolynomials
import Mathlib.Tactic.Polynomial.Basic

/-! Kernel-checked complete polynomial identities, not finite jet tests. -/

noncomputable section
set_option autoImplicit false
set_option maxRecDepth 8192

namespace Zeta7AnnularRows
open Polynomial

set_option maxHeartbeats 4000000 in
-- The expanded identities contain degree-thirty polynomials with large exact coefficients.
theorem recurrence_2_0 :
    ell3_0 * P ^ 2 * N ^ 4 =
      derivativeNumerator ell2_0 * P * N ^ 3 + (C (5/144 : ℚ) * mu2_1 * P ^ 2 * N ^ 4 + C (77/144 : ℚ) * mu2_2 * P ^ 2 * N ^ 4) := by
  norm_num [ell2_0, ell2_1, ell2_2, ell2_3, ell3_0, mu2_1, mu2_2, mu2_3, raw_ds, raw_s, raw_ell2_0, raw_ell2_1, raw_ell2_2, raw_ell2_3, raw_ell3_0, raw_mu2_1, raw_mu2_2, raw_mu2_3, P, N, T, theta, derivativeNumerator, Zeta7Riccati.P, Zeta7Stage2B.p, Zeta7Riccati.N, Zeta7Riccati.T, Zeta7Riccati.theta, Polynomial.derivative_add, Polynomial.derivative_mul, Polynomial.derivative_pow, map_ofNat]
  <;> polynomial

set_option maxHeartbeats 4000000 in
-- The expanded identities contain degree-thirty polynomials with large exact coefficients.
theorem recurrence_2_1 :
    ell3_1 * P ^ 2 * N ^ 4 =
      derivativeNumerator ell2_1 * P * N ^ 3 + (ell2_0 * raw_ds + C (1/2 : ℚ) * mu2_1 * (3 * raw_s - P * N ^ 3) * P * N + C (77/144 : ℚ) * mu2_3 * P ^ 2 * N ^ 4) := by
  norm_num [ell2_0, ell2_1, ell2_2, ell2_3, ell3_1, mu2_1, mu2_2, mu2_3, raw_ds, raw_s, raw_ell2_0, raw_ell2_1, raw_ell2_2, raw_ell2_3, raw_ell3_1, raw_mu2_1, raw_mu2_2, raw_mu2_3, P, N, T, theta, derivativeNumerator, Zeta7Riccati.P, Zeta7Stage2B.p, Zeta7Riccati.N, Zeta7Riccati.T, Zeta7Riccati.theta, Polynomial.derivative_add, Polynomial.derivative_mul, Polynomial.derivative_pow, map_ofNat]
  <;> polynomial

set_option maxHeartbeats 4000000 in
-- The expanded identities contain degree-thirty polynomials with large exact coefficients.
theorem recurrence_2_2 :
    ell3_2 * P ^ 2 * N ^ 4 =
      derivativeNumerator ell2_2 * P * N ^ 3 + (ell2_0 * raw_ds + C (1/2 : ℚ) * mu2_2 * (5 * raw_s - 3 * P * N ^ 3) * P * N + C (5/144 : ℚ) * mu2_3 * P ^ 2 * N ^ 4) := by
  norm_num [ell2_0, ell2_1, ell2_2, ell2_3, ell3_2, mu2_1, mu2_2, mu2_3, raw_ds, raw_s, raw_ell2_0, raw_ell2_1, raw_ell2_2, raw_ell2_3, raw_ell3_2, raw_mu2_1, raw_mu2_2, raw_mu2_3, P, N, T, theta, derivativeNumerator, Zeta7Riccati.P, Zeta7Stage2B.p, Zeta7Riccati.N, Zeta7Riccati.T, Zeta7Riccati.theta, Polynomial.derivative_add, Polynomial.derivative_mul, Polynomial.derivative_pow, map_ofNat]
  <;> polynomial

set_option maxHeartbeats 4000000 in
-- The expanded identities contain degree-thirty polynomials with large exact coefficients.
theorem recurrence_2_3 :
    ell3_3 * P ^ 2 * N ^ 4 =
      derivativeNumerator ell2_3 * P * N ^ 3 + ((ell2_1 + ell2_2) * raw_ds + mu2_3 * (4 * raw_s - 2 * P * N ^ 3) * P * N) := by
  norm_num [ell2_0, ell2_1, ell2_2, ell2_3, ell3_3, mu2_1, mu2_2, mu2_3, raw_ds, raw_s, raw_ell2_0, raw_ell2_1, raw_ell2_2, raw_ell2_3, raw_ell3_3, raw_mu2_1, raw_mu2_2, raw_mu2_3, P, N, T, theta, derivativeNumerator, Zeta7Riccati.P, Zeta7Stage2B.p, Zeta7Riccati.N, Zeta7Riccati.T, Zeta7Riccati.theta, Polynomial.derivative_add, Polynomial.derivative_mul, Polynomial.derivative_pow, map_ofNat]
  <;> polynomial

end Zeta7AnnularRows

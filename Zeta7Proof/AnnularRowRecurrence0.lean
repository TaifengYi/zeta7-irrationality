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
theorem recurrence_0_0 :
    ell1_0 * P ^ 2 * N ^ 4 =
      derivativeNumerator ell0_0 * P * N ^ 3 + (C (5/144 : ℚ) * mu0_1 * P ^ 2 * N ^ 4 + C (77/144 : ℚ) * mu0_2 * P ^ 2 * N ^ 4) := by
  norm_num [ell0_0, ell0_1, ell0_2, ell0_3, ell1_0, mu0_1, mu0_2, mu0_3, raw_ds, raw_s, raw_ell0_0, raw_ell0_1, raw_ell0_2, raw_ell0_3, raw_ell1_0, raw_mu0_1, raw_mu0_2, raw_mu0_3, P, N, T, theta, derivativeNumerator, Zeta7Riccati.P, Zeta7Stage2B.p, Zeta7Riccati.N, Zeta7Riccati.T, Zeta7Riccati.theta, Polynomial.derivative_add, Polynomial.derivative_mul, Polynomial.derivative_pow, map_ofNat]
  <;> polynomial

set_option maxHeartbeats 4000000 in
-- The expanded identities contain degree-thirty polynomials with large exact coefficients.
theorem recurrence_0_1 :
    ell1_1 * P ^ 2 * N ^ 4 =
      derivativeNumerator ell0_1 * P * N ^ 3 + (ell0_0 * raw_ds + C (1/2 : ℚ) * mu0_1 * (3 * raw_s - P * N ^ 3) * P * N + C (77/144 : ℚ) * mu0_3 * P ^ 2 * N ^ 4) := by
  norm_num [ell0_0, ell0_1, ell0_2, ell0_3, ell1_1, mu0_1, mu0_2, mu0_3, raw_ds, raw_s, raw_ell0_0, raw_ell0_1, raw_ell0_2, raw_ell0_3, raw_ell1_1, raw_mu0_1, raw_mu0_2, raw_mu0_3, P, N, T, theta, derivativeNumerator, Zeta7Riccati.P, Zeta7Stage2B.p, Zeta7Riccati.N, Zeta7Riccati.T, Zeta7Riccati.theta, Polynomial.derivative_add, Polynomial.derivative_mul, Polynomial.derivative_pow, map_ofNat]
  <;> polynomial

set_option maxHeartbeats 4000000 in
-- The expanded identities contain degree-thirty polynomials with large exact coefficients.
theorem recurrence_0_2 :
    ell1_2 * P ^ 2 * N ^ 4 =
      derivativeNumerator ell0_2 * P * N ^ 3 + (ell0_0 * raw_ds + C (1/2 : ℚ) * mu0_2 * (5 * raw_s - 3 * P * N ^ 3) * P * N + C (5/144 : ℚ) * mu0_3 * P ^ 2 * N ^ 4) := by
  norm_num [ell0_0, ell0_1, ell0_2, ell0_3, ell1_2, mu0_1, mu0_2, mu0_3, raw_ds, raw_s, raw_ell0_0, raw_ell0_1, raw_ell0_2, raw_ell0_3, raw_ell1_2, raw_mu0_1, raw_mu0_2, raw_mu0_3, P, N, T, theta, derivativeNumerator, Zeta7Riccati.P, Zeta7Stage2B.p, Zeta7Riccati.N, Zeta7Riccati.T, Zeta7Riccati.theta, Polynomial.derivative_add, Polynomial.derivative_mul, Polynomial.derivative_pow, map_ofNat]
  <;> polynomial

set_option maxHeartbeats 4000000 in
-- The expanded identities contain degree-thirty polynomials with large exact coefficients.
theorem recurrence_0_3 :
    ell1_3 * P ^ 2 * N ^ 4 =
      derivativeNumerator ell0_3 * P * N ^ 3 + ((ell0_1 + ell0_2) * raw_ds + mu0_3 * (4 * raw_s - 2 * P * N ^ 3) * P * N) := by
  norm_num [ell0_0, ell0_1, ell0_2, ell0_3, ell1_3, mu0_1, mu0_2, mu0_3, raw_ds, raw_s, raw_ell0_0, raw_ell0_1, raw_ell0_2, raw_ell0_3, raw_ell1_3, raw_mu0_1, raw_mu0_2, raw_mu0_3, P, N, T, theta, derivativeNumerator, Zeta7Riccati.P, Zeta7Stage2B.p, Zeta7Riccati.N, Zeta7Riccati.T, Zeta7Riccati.theta, Polynomial.derivative_add, Polynomial.derivative_mul, Polynomial.derivative_pow, map_ofNat]
  <;> polynomial

end Zeta7AnnularRows

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
theorem residual_0 :
    P ^ 3 * ell3_0 - P * raw_V * ell1_0 - C (1/2 : ℚ) * raw_dV * ell0_0 = 0 := by
  norm_num [ell3_0, ell1_0, ell0_0, raw_ell3_0, raw_ell1_0, raw_ell0_0, raw_V, raw_dV, P, N, T, theta, derivativeNumerator, Zeta7Riccati.P, Zeta7Stage2B.p, Zeta7Riccati.N, Zeta7Riccati.T, Zeta7Riccati.theta, Polynomial.derivative_add, Polynomial.derivative_mul, Polynomial.derivative_pow, map_ofNat]
  <;> polynomial

set_option maxHeartbeats 4000000 in
-- The expanded identities contain degree-thirty polynomials with large exact coefficients.
theorem residual_1 :
    P ^ 3 * ell3_1 - P * raw_V * ell1_1 - C (1/2 : ℚ) * raw_dV * ell0_1 = 0 := by
  norm_num [ell3_1, ell1_1, ell0_1, raw_ell3_1, raw_ell1_1, raw_ell0_1, raw_V, raw_dV, P, N, T, theta, derivativeNumerator, Zeta7Riccati.P, Zeta7Stage2B.p, Zeta7Riccati.N, Zeta7Riccati.T, Zeta7Riccati.theta, Polynomial.derivative_add, Polynomial.derivative_mul, Polynomial.derivative_pow, map_ofNat]
  <;> polynomial

set_option maxHeartbeats 4000000 in
-- The expanded identities contain degree-thirty polynomials with large exact coefficients.
theorem residual_2 :
    P ^ 3 * ell3_2 - P * raw_V * ell1_2 - C (1/2 : ℚ) * raw_dV * ell0_2 = 0 := by
  norm_num [ell3_2, ell1_2, ell0_2, raw_ell3_2, raw_ell1_2, raw_ell0_2, raw_V, raw_dV, P, N, T, theta, derivativeNumerator, Zeta7Riccati.P, Zeta7Stage2B.p, Zeta7Riccati.N, Zeta7Riccati.T, Zeta7Riccati.theta, Polynomial.derivative_add, Polynomial.derivative_mul, Polynomial.derivative_pow, map_ofNat]
  <;> polynomial

set_option maxHeartbeats 4000000 in
-- The expanded identities contain degree-thirty polynomials with large exact coefficients.
theorem residual_3 :
    P ^ 3 * ell3_3 - P * raw_V * ell1_3 - C (1/2 : ℚ) * raw_dV * ell0_3 = 0 := by
  norm_num [ell3_3, ell1_3, ell0_3, raw_ell3_3, raw_ell1_3, raw_ell0_3, raw_V, raw_dV, P, N, T, theta, derivativeNumerator, Zeta7Riccati.P, Zeta7Stage2B.p, Zeta7Riccati.N, Zeta7Riccati.T, Zeta7Riccati.theta, Polynomial.derivative_add, Polynomial.derivative_mul, Polynomial.derivative_pow, map_ofNat]
  <;> polynomial

end Zeta7AnnularRows

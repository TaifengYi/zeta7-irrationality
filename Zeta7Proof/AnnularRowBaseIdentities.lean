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
theorem s_numerator :
    raw_s = T ^ 2 := by
  norm_num [raw_s, P, N, T, theta, derivativeNumerator, Zeta7Riccati.P, Zeta7Stage2B.p, Zeta7Riccati.N, Zeta7Riccati.T, Zeta7Riccati.theta, Polynomial.derivative_add, Polynomial.derivative_mul, Polynomial.derivative_pow, map_ofNat]
  <;> polynomial

set_option maxHeartbeats 4000000 in
-- The expanded identities contain degree-thirty polynomials with large exact coefficients.
theorem q_numerator :
    raw_q = T ^ 2 * (P * N ^ 3 - T ^ 2) := by
  norm_num [raw_q, P, N, T, theta, derivativeNumerator, Zeta7Riccati.P, Zeta7Stage2B.p, Zeta7Riccati.N, Zeta7Riccati.T, Zeta7Riccati.theta, Polynomial.derivative_add, Polynomial.derivative_mul, Polynomial.derivative_pow, map_ofNat]
  <;> polynomial

set_option maxHeartbeats 4000000 in
-- The expanded identities contain degree-thirty polynomials with large exact coefficients.
theorem ds_numerator :
    raw_ds = theta raw_s * P * N - raw_s * (theta P * N + 3 * P * theta N) := by
  norm_num [raw_ds, raw_s, P, N, T, theta, derivativeNumerator, Zeta7Riccati.P, Zeta7Stage2B.p, Zeta7Riccati.N, Zeta7Riccati.T, Zeta7Riccati.theta, Polynomial.derivative_add, Polynomial.derivative_mul, Polynomial.derivative_pow, map_ofNat]
  <;> polynomial

set_option maxHeartbeats 4000000 in
-- The expanded identities contain degree-thirty polynomials with large exact coefficients.
theorem V_numerator :
    raw_V = 8 * X * (1 + 16 * X + 49 * X ^ 2) := by
  norm_num [raw_V, P, N, T, theta, derivativeNumerator, Zeta7Riccati.P, Zeta7Stage2B.p, Zeta7Riccati.N, Zeta7Riccati.T, Zeta7Riccati.theta, Polynomial.derivative_add, Polynomial.derivative_mul, Polynomial.derivative_pow, map_ofNat]
  <;> polynomial

set_option maxHeartbeats 4000000 in
-- The expanded identities contain degree-thirty polynomials with large exact coefficients.
theorem dV_numerator :
    raw_dV = theta raw_V * P - 2 * raw_V * theta P := by
  norm_num [raw_dV, raw_V, P, N, T, theta, derivativeNumerator, Zeta7Riccati.P, Zeta7Stage2B.p, Zeta7Riccati.N, Zeta7Riccati.T, Zeta7Riccati.theta, Polynomial.derivative_add, Polynomial.derivative_mul, Polynomial.derivative_pow, map_ofNat]
  <;> polynomial

end Zeta7AnnularRows

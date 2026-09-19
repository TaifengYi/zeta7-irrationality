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
theorem reduction_2_1 :
    raw_q * mu2_1 = ell2_1 * raw_ds * N ^ 2 := by
  norm_num [mu2_1, raw_mu2_1, ell2_1, raw_ell2_1, raw_q, raw_ds, P, N, T, theta, derivativeNumerator, Zeta7Riccati.P, Zeta7Stage2B.p, Zeta7Riccati.N, Zeta7Riccati.T, Zeta7Riccati.theta, Polynomial.derivative_add, Polynomial.derivative_mul, Polynomial.derivative_pow, map_ofNat]
  <;> polynomial

set_option maxHeartbeats 4000000 in
-- The expanded identities contain degree-thirty polynomials with large exact coefficients.
theorem reduction_2_2 :
    raw_q * mu2_2 = ell2_2 * raw_ds * N ^ 2 := by
  norm_num [mu2_2, raw_mu2_2, ell2_2, raw_ell2_2, raw_q, raw_ds, P, N, T, theta, derivativeNumerator, Zeta7Riccati.P, Zeta7Stage2B.p, Zeta7Riccati.N, Zeta7Riccati.T, Zeta7Riccati.theta, Polynomial.derivative_add, Polynomial.derivative_mul, Polynomial.derivative_pow, map_ofNat]
  <;> polynomial

set_option maxHeartbeats 4000000 in
-- The expanded identities contain degree-thirty polynomials with large exact coefficients.
theorem reduction_2_3 :
    raw_q * mu2_3 = ell2_3 * raw_ds * N ^ 2 := by
  norm_num [mu2_3, raw_mu2_3, ell2_3, raw_ell2_3, raw_q, raw_ds, P, N, T, theta, derivativeNumerator, Zeta7Riccati.P, Zeta7Stage2B.p, Zeta7Riccati.N, Zeta7Riccati.T, Zeta7Riccati.theta, Polynomial.derivative_add, Polynomial.derivative_mul, Polynomial.derivative_pow, map_ofNat]
  <;> polynomial

end Zeta7AnnularRows

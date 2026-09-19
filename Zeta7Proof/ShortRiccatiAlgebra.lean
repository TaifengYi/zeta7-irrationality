import Zeta7Proof.RiccatiRationalAlgebra
import Zeta7Proof.ActualAEisenstein

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace Zeta7Riccati
open Polynomial

def Q : Polynomial ℚ := 1 - 39 * X - 343 * X ^ 2

theorem theta_mul (f g : Polynomial ℚ) : theta (f * g) = theta f * g + f * theta g := by
  simp only [theta, derivative_mul]
  ring

theorem sNumerator_eq_NQ : sNumerator = N * Q := by
  simp [sNumerator, theta, N, P, Zeta7Stage2B.p, Q, T, map_ofNat]
  ring

/-- Obtained from the previously compiled Riccati calculation by cancelling N². -/
theorem short_riccati_cleared :
    Q ^ 2 - P * N - 12 * (theta Q * P - Q * theta P) =
      288 * X * (1 + 16 * X + 49 * X ^ 2) := by
  have hn : N ≠ 0 := by
    intro h
    have hc := congrArg (fun f : Polynomial ℚ => f.coeff 0) h
    norm_num [N] at hc
  apply mul_right_cancel₀ (b := N ^ 2) (pow_ne_zero 2 hn)
  calc
    _ = sNumerator ^ 2 - P * N ^ 3 -
        12 * (theta sNumerator * (P * N) - sNumerator * theta (P * N)) := by
      rw [sNumerator_eq_NQ, theta_mul, theta_mul]
      ring
    _ = _ := riccati_cleared

theorem Q_linear_combination : 12 * Q = -36 * P - N + 49 * (1 + 5 * X + X ^ 2) := by
  simp only [Q, P, Zeta7Stage2B.p, N]
  ring

end Zeta7Riccati

namespace Zeta7Common
open PowerSeries

def shortP : ℚ⟦X⟧ := (Zeta7Riccati.P : Polynomial ℚ)
def shortN : ℚ⟦X⟧ := (Zeta7Riccati.N : Polynomial ℚ)
def shortQ : ℚ⟦X⟧ := (Zeta7Riccati.Q : Polynomial ℚ)
def shortS : ℚ⟦X⟧ := shortQ * shortP⁻¹
def shortA : ℚ⟦X⟧ := shortN * shortP⁻¹

theorem shortP_value : shortP = 1 + 13 * X + 49 * X ^ 2 := by
  change Polynomial.coeToPowerSeries.ringHom Zeta7Riccati.P = _
  simp only [Zeta7Riccati.P, Zeta7Stage2B.p, map_add, map_mul, map_pow, map_one,
    map_ofNat, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X]

theorem shortN_value : shortN = 1 + 245 * X + 2401 * X ^ 2 := by
  change Polynomial.coeToPowerSeries.ringHom Zeta7Riccati.N = _
  simp only [Zeta7Riccati.N, map_add, map_mul, map_pow, map_one,
    map_ofNat, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X]

theorem shortQ_value : shortQ = 1 - 39 * X - 343 * X ^ 2 := by
  change Polynomial.coeToPowerSeries.ringHom Zeta7Riccati.Q = _
  simp only [Zeta7Riccati.Q, map_sub, map_mul, map_pow, map_one,
    map_ofNat, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X]

theorem shortP_constant : constantCoeff shortP = 1 := by simp [shortP_value]

theorem shortP_ne_zero : shortP ≠ 0 := by
  intro h
  have hc := congrArg constantCoeff h
  rw [shortP_constant, map_zero] at hc
  exact one_ne_zero hc

theorem shortP_mul_inv : shortP * shortP⁻¹ = 1 :=
  PowerSeries.mul_inv_cancel _ (by rw [shortP_constant]; norm_num)

theorem shortP_mul_shortS : shortP * shortS = shortQ := by
  rw [shortS]
  calc
    _ = shortQ * (shortP * shortP⁻¹) := by ring
    _ = _ := by rw [shortP_mul_inv, mul_one]

theorem shortP_mul_shortA : shortP * shortA = shortN := by
  rw [shortA]
  calc
    _ = shortN * (shortP * shortP⁻¹) := by ring
    _ = _ := by rw [shortP_mul_inv, mul_one]

theorem shortP_sq_euler_shortS : shortP ^ 2 * euler shortS =
    euler shortQ * shortP - shortQ * euler shortP := by
  have hd := congrArg euler shortP_mul_shortS
  rw [euler_mul] at hd
  linear_combination shortP * hd - euler shortP * shortP_mul_shortS

theorem polynomial_euler (p : Polynomial ℚ) :
    euler (p : ℚ⟦X⟧) = (Zeta7Riccati.theta p : Polynomial ℚ) := by
  simp [euler, Zeta7Riccati.theta, derivative_coe, Polynomial.coe_mul, Polynomial.coe_X]

theorem short_riccati_series :
    shortQ ^ 2 - shortP * shortN -
      12 * (euler shortQ * shortP - shortQ * euler shortP) =
        288 * X * (1 + 16 * X + 49 * X ^ 2) := by
  have h := congrArg Polynomial.coeToPowerSeries.ringHom Zeta7Riccati.short_riccati_cleared
  simpa only [map_sub, map_mul, map_pow, map_add, map_one, map_ofNat,
    Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X,
    shortQ, shortP, shortN, polynomial_euler] using h

theorem rationalPotential_cleared : shortP ^ 2 * rationalPotential =
    8 * X * (1 + 16 * X + 49 * X ^ 2) := by
  have hi : shortP ^ 2 * (shortP ^ 2)⁻¹ = 1 :=
    PowerSeries.mul_inv_cancel _ (by simp [shortP_constant])
  rw [rationalPotential, ← shortP_value]
  calc
    _ = 8 * X * (1 + 16 * X + 49 * X ^ 2) * (shortP ^ 2 * (shortP ^ 2)⁻¹) := by ring
    _ = _ := by rw [hi, mul_one]

/-- The shorter rational identity, derived from the existing polynomial certificate. -/
theorem shortS_riccati : shortS ^ 2 - shortA - 12 * euler shortS = 36 * rationalPotential := by
  apply mul_left_cancel₀ (a := shortP ^ 2) (pow_ne_zero 2 shortP_ne_zero)
  have hs : shortP ^ 2 * shortS ^ 2 = shortQ ^ 2 := by
    rw [← mul_pow, shortP_mul_shortS]
  linear_combination hs - shortP * shortP_mul_shortA - 12 * shortP_sq_euler_shortS +
    short_riccati_series - 36 * rationalPotential_cleared

end Zeta7Common

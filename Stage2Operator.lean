import Stage2B
import Zeta7Proof.DifferentialOperator

/-!
# The exact local operator identity

This file only uses the internally defined polynomials and formal series.
It makes no assertion identifying them with modular forms or zeta values.
Stage2B is preserved verbatim as the preceding compiling checkpoint.
-/

set_option autoImplicit false
noncomputable section

namespace Zeta7Stage2B

open Polynomial

@[simp] theorem polynomial_coe_ofNat (n : ℕ) [n.AtLeastTwo] :
    ((ofNat(n) : Polynomial ℚ) : PowerSeries ℚ) = ofNat(n) :=
  map_ofNat Polynomial.coeToPowerSeries.ringHom n

/-- The numerator of the already defined potential. -/
def potentialNumerator : Polynomial ℚ := 8 * X * (1 + 16 * X + 49 * X ^ 2)

theorem p_constantCoeff : PowerSeries.constantCoeff (p : PowerSeries ℚ) = 1 := by
  simp [p]

/-- The actual inverse exists because the constant term is one. -/
def pUnit : (PowerSeries ℚ)ˣ where
  val := p
  inv := (p : PowerSeries ℚ)⁻¹
  val_inv := PowerSeries.mul_inv_cancel _ (by rw [p_constantCoeff]; norm_num)
  inv_val := by
    rw [mul_comm]
    exact PowerSeries.mul_inv_cancel _ (by rw [p_constantCoeff]; norm_num)

def eulerHom : PowerSeries ℚ →+ PowerSeries ℚ where
  toFun := euler
  map_zero' := by simp [euler]
  map_add' f g := by simp [euler, mul_add]

theorem euler_mul (f g : PowerSeries ℚ) :
    euler (f * g) = euler f * g + f * euler g := by
  simp only [euler, Derivation.leibniz, smul_eq_mul]
  ring

theorem potential_eq_unit :
    potential = (potentialNumerator : PowerSeries ℚ) * (↑pUnit⁻¹ : PowerSeries ℚ) ^ 2 := by
  simp [potential, potentialNumerator, pUnit, pow_two]

theorem c₁_eq_potentialNumerator :
    (c₁ : PowerSeries ℚ) =
      -(potentialNumerator : PowerSeries ℚ) * (p : PowerSeries ℚ) := by
  simp [c₁, potentialNumerator]

theorem c₀_eq_potentialNumerator_derivative :
    (c₀ : PowerSeries ℚ) = PowerSeries.C (1 / 2 : ℚ) *
      (2 * (potentialNumerator : PowerSeries ℚ) * euler (p : PowerSeries ℚ) -
        (p : PowerSeries ℚ) * euler (potentialNumerator : PowerSeries ℚ)) := by
  have hpoly : c₀ = C (1 / 2 : ℚ) *
      (2 * potentialNumerator * (X * p.derivative) -
        p * (X * potentialNumerator.derivative)) := by
    have h : 2 * c₀ = 2 * potentialNumerator * (X * p.derivative) -
        p * (X * potentialNumerator.derivative) := cleared_potential_derivative
    have hhalf : 2 * C (1 / 2 : ℚ) = (1 : Polynomial ℚ) := by
      rw [show (2 : Polynomial ℚ) = C 2 by simp only [map_ofNat], ← map_mul]
      norm_num
    linear_combination C (1 / 2 : ℚ) * h - c₀ * hhalf
  have h := congrArg (fun a : Polynomial ℚ => (a : PowerSeries ℚ)) hpoly
  simpa [euler, PowerSeries.derivative_coe] using h

/-- For every formal series, with no equation, coefficient or modular hypothesis. -/
theorem clearedOperator_identity (f : PowerSeries ℚ) :
    clearedOperator f = (p : PowerSeries ℚ) ^ 3 *
      (euler (euler (euler f)) - potential * euler f -
        PowerSeries.C (1 / 2 : ℚ) * euler potential * f) := by
  have h := Zeta7Differential.cleared_operator eulerHom euler_mul pUnit
    (potentialNumerator : PowerSeries ℚ) (PowerSeries.C (1 / 2 : ℚ)) f
  change (p : PowerSeries ℚ) ^ 3 * euler (euler (euler f)) -
    (potentialNumerator : PowerSeries ℚ) * (p : PowerSeries ℚ) * euler f +
    PowerSeries.C (1 / 2 : ℚ) *
      (2 * (potentialNumerator : PowerSeries ℚ) * euler (p : PowerSeries ℚ) -
        (p : PowerSeries ℚ) * euler (potentialNumerator : PowerSeries ℚ)) * f = _ at h
  rw [← potential_eq_unit] at h
  rw [clearedOperator, Polynomial.coe_pow, c₁_eq_potentialNumerator,
    c₀_eq_potentialNumerator_derivative]
  change _ = (p : PowerSeries ℚ) ^ 3 *
    (euler (euler (euler f)) - potential * euler f -
      PowerSeries.C (1 / 2 : ℚ) * euler potential * f) at h
  convert h using 1
  ring

#print axioms p_constantCoeff
#print axioms euler_mul
#print axioms potential_eq_unit
#print axioms c₁_eq_potentialNumerator
#print axioms c₀_eq_potentialNumerator_derivative
#print axioms clearedOperator_identity

end Zeta7Stage2B

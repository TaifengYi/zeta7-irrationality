import Zeta7Proof.ActualLH

/-! The genuine seven-adic target satisfies the formal differential equations,
without a rationality hypothesis or the published analytic radius input. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
open PowerSeries
namespace Zeta7Common
open Zeta7Main
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

def eulerLinear {K : Type*} [CommRing K] : K⟦X⟧ →ₗ[K] K⟦X⟧ where
  toFun := euler
  map_add' f g := by simp [euler, mul_add]
  map_smul' a f := by simp [euler, mul_smul_comm]

def differentialOperator {K : Type*} [Field K] (V : K⟦X⟧) : K⟦X⟧ →ₗ[K] K⟦X⟧ :=
  eulerLinear.comp (eulerLinear.comp eulerLinear) -
    ((LinearMap.mulLeft K⟦X⟧ V).restrictScalars K).comp eulerLinear -
    (LinearMap.mulLeft K⟦X⟧ (C (1 / 2 : K) * euler V)).restrictScalars K

theorem differentialOperator_apply {K : Type*} [Field K] (V f : K⟦X⟧) :
    differentialOperator V f = euler (euler (euler f)) - V * euler f -
      C (1 / 2 : K) * euler V * f := rfl

theorem differentialOperator_rational (f : ℚ⟦X⟧) :
    differentialOperator rationalPotential f = modularL f := rfl

theorem map_differentialOperator {K L : Type*} [Field K] [Field L] (φ : K →+* L)
    (V f : K⟦X⟧) :
    (differentialOperator V f).map φ = differentialOperator (V.map φ) (f.map φ) := by
  simp [differentialOperator_apply, map_euler, map_ofNat]

theorem BSeries_homogeneous : modularL BSeries = 0 := by
  have he : BSeries = rationalH 1 - rationalH 0 := by
    simp [rationalH]
    ring
  change differentialOperator rationalPotential BSeries = 0
  rw [he, map_sub, differentialOperator_rational, differentialOperator_rational,
    rationalH_modularL, rationalH_modularL, sub_self]

theorem HSeries_affine : HSeries = (rationalH 0).map (algebraMap ℚ ℚ_[7]) +
    eta • BSeries.map (algebraMap ℚ ℚ_[7]) := by
  unfold HSeries rationalH
  rw [map_zero, add_zero, map_mul]
  rw [smul_eq_C_mul]
  simp only [PowerSeries.map]
  ring

theorem HSeries_differential_equation :
    differentialOperator (rationalPotential.map (algebraMap ℚ ℚ_[7])) HSeries =
      rationalForcing.map (algebraMap ℚ ℚ_[7]) := by
  rw [HSeries_affine, map_add, map_smul, ← map_differentialOperator,
    ← map_differentialOperator, differentialOperator_rational,
    differentialOperator_rational, rationalH_modularL, BSeries_homogeneous]
  simp

theorem euler_quadratic_general {K : Type*} [Field K] [CharZero K] (V f : K⟦X⟧) :
    euler (quadratic V f) = f * differentialOperator V f := by
  have hmul (a b : K⟦X⟧) : euler (a * b) = euler a * b + a * euler b := by
    simp only [euler, Derivation.leibniz, smul_eq_mul]
    ring
  have hsub (a b : K⟦X⟧) : euler (a - b) = euler a - euler b :=
    eulerLinear.map_sub a b
  have hc (a : K) : euler (C a) = 0 := by simp [euler]
  unfold quadratic
  rw [differentialOperator_apply]
  simp only [hsub, hmul, pow_two, hc, zero_mul, zero_add]
  have hh : (C (1 / 2 : K) : K⟦X⟧) + C (1 / 2 : K) = 1 := by
    rw [← map_add]
    norm_num
  linear_combination -(euler f * euler (euler f) + V * f * euler f) * hh

theorem targetK_derivative : euler (targetGerms 3) =
    rationalForcing.map (algebraMap ℚ ℚ_[7]) * HSeries := by
  change euler (quadratic _ HSeries) = _
  rw [euler_quadratic_general, HSeries_differential_equation, mul_comm]

theorem targetK_constant : constantCoeff (targetGerms 3) = 0 := by
  simp [targetGerms, germs, quadratic, euler, rationalPotential]

theorem targetK_coeff (n : ℕ) :
    coeff (n + 1) (targetGerms 3) =
      coeff (n + 1) (rationalForcing.map (algebraMap ℚ ℚ_[7]) * HSeries) / (n + 1 : ℚ_[7]) := by
  have he := congrArg (coeff (n + 1)) targetK_derivative
  rw [euler_coeff] at he
  apply (eq_div_iff (by exact_mod_cast Nat.succ_ne_zero n)).mpr
  simpa only [Nat.cast_add, Nat.cast_one, mul_comm] using he

end Zeta7Common

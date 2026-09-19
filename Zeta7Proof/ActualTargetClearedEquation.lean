import Zeta7Proof.ActualTargetDifferential

/-! The denominator-cleared equation for the original seven-adic target. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
open PowerSeries
namespace Zeta7Common
open Zeta7Main
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

def targetP : ℚ_[7]⟦X⟧ := 1 + 13 * X + 49 * X ^ 2
def targetW : ℚ_[7]⟦X⟧ := 8 * X * (1 + 16 * X + 49 * X ^ 2)
def targetS : ℚ_[7]⟦X⟧ := X * (1 + 10 * X)

theorem shortP_map_seven : shortP.map (algebraMap ℚ ℚ_[7]) = targetP := by
  rw [shortP_value]
  simp [targetP, map_ofNat]

theorem targetPotential_cleared :
    targetP ^ 2 * rationalPotential.map (algebraMap ℚ ℚ_[7]) = targetW := by
  have h := congrArg (PowerSeries.map (algebraMap ℚ ℚ_[7])) rationalPotential_cleared
  simpa [map_ofNat, shortP_map_seven, targetW] using h

theorem targetForcing_cleared :
    targetP * rationalForcing.map (algebraMap ℚ ℚ_[7]) = targetS := by
  have h := congrArg (PowerSeries.map (algebraMap ℚ ℚ_[7])) rationalForcing_cleared
  simpa [map_ofNat, shortP_map_seven, targetS] using h

theorem euler_mul_general {K : Type*} [CommRing K] (f g : K⟦X⟧) :
    euler (f * g) = euler f * g + f * euler g := by
  simp only [euler, Derivation.leibniz, smul_eq_mul]
  ring

theorem targetPotential_derivative_cleared :
    targetP ^ 3 * euler (rationalPotential.map (algebraMap ℚ ℚ_[7])) =
      targetP * euler targetW - 2 * targetW * euler targetP := by
  have h := congrArg euler targetPotential_cleared
  simp only [pow_two, euler_mul_general] at h
  linear_combination targetP * h - 2 * euler targetP * targetPotential_cleared

theorem targetOperator_cleared (f : ℚ_[7]⟦X⟧) :
    targetP ^ 3 * differentialOperator (rationalPotential.map (algebraMap ℚ ℚ_[7])) f =
      targetP ^ 3 * euler (euler (euler f)) - targetP * targetW * euler f +
        (targetW * euler targetP - C (1 / 2 : ℚ_[7]) * targetP * euler targetW) * f := by
  rw [differentialOperator_apply]
  calc
    _ = targetP ^ 3 * euler (euler (euler f)) -
      targetP * (targetP ^ 2 * rationalPotential.map (algebraMap ℚ ℚ_[7])) * euler f -
      C (1 / 2 : ℚ_[7]) * (targetP ^ 3 * euler (rationalPotential.map (algebraMap ℚ ℚ_[7]))) * f := by ring
    _ = _ := by
      rw [targetPotential_cleared, targetPotential_derivative_cleared]
      have hh : (C (1 / 2 : ℚ_[7]) : ℚ_[7]⟦X⟧) * 2 = 1 := by
        rw [← map_ofNat C 2, ← map_mul]
        norm_num
      linear_combination targetW * euler targetP * f * hh

theorem HSeries_cleared_differential_equation :
    targetP ^ 3 * euler (euler (euler HSeries)) - targetP * targetW * euler HSeries +
      (targetW * euler targetP - C (1 / 2 : ℚ_[7]) * targetP * euler targetW) * HSeries =
        targetP ^ 2 * targetS := by
  rw [← targetOperator_cleared, HSeries_differential_equation]
  linear_combination targetP ^ 2 * targetForcing_cleared

end Zeta7Common

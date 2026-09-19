import Zeta7Proof.CommonRationalGerms

/-! Formal differentiation of the actual modular coordinate and germs.
All inverses here are formal units at the cusp. No global analytic division
by A or B is asserted. The modular potential identity is not assumed. -/
set_option autoImplicit false
noncomputable section
open PowerSeries
namespace Zeta7Common
open Zeta7Main

theorem euler_add (f g : ℚ⟦X⟧) : euler (f + g) = euler f + euler g := by
  simp [euler, mul_add]

theorem euler_sub (f g : ℚ⟦X⟧) : euler (f - g) = euler f - euler g := by
  simp [euler, mul_sub]

theorem euler_mul (f g : ℚ⟦X⟧) : euler (f * g) = euler f * g + f * euler g := by
  simp only [euler, Derivation.leibniz, smul_eq_mul]
  ring

@[simp] theorem euler_C (c : ℚ) : euler (C c) = 0 := by simp [euler]
@[simp] theorem euler_one : euler (1 : ℚ⟦X⟧) = 0 := by simp [euler]
@[simp] theorem euler_zero : euler (0 : ℚ⟦X⟧) = 0 := by simp [euler]

theorem x_hasSubst : HasSubst xSeries := HasSubst.of_constantCoeff_zero' xSeries_constant
theorem q_hasSubst : HasSubst qSeries := HasSubst.of_constantCoeff_zero' qSeries_constant

theorem subst_x_injective : Function.Injective (fun f : ℚ⟦X⟧ => f.subst xSeries) := by
  intro f g h
  have h' := congrArg (fun s : ℚ⟦X⟧ => s.subst qSeries) h
  simpa only [subst_comp_subst_apply x_hasSubst q_hasSubst, x_subst_q, X_subst] using h'

theorem subst_q_injective : Function.Injective (fun f : ℚ⟦X⟧ => f.subst qSeries) := by
  intro f g h
  have h' := congrArg (fun s : ℚ⟦X⟧ => s.subst xSeries) h
  simpa only [subst_comp_subst_apply q_hasSubst x_hasSubst, q_subst_x, X_subst] using h'

theorem BSeries_subst_x : BSeries.subst xSeries = ASeries := by
  rw [BSeries, subst_comp_subst_apply q_hasSubst x_hasSubst, q_subst_x, X_subst]

theorem ASeries_constant : constantCoeff ASeries = 1 := by simp [ASeries]

theorem BSeries_constant : constantCoeff BSeries = 1 := by
  have h := constantCoeff_subst_eq_zero qSeries_constant
    (X * derivative ℚ xUnit * xUnit⁻¹) (by simp)
  have hone : (1 : ℚ⟦X⟧).subst qSeries = 1 := by
    simpa only [map_one] using (subst_C (a := qSeries) (1 : ℚ))
  simpa [BSeries, ASeries, subst_add q_hasSubst, hone, PowerSeries.constantCoeff] using h

theorem BSeries_mul_inv : BSeries * BSeries⁻¹ = 1 := by
  apply PowerSeries.mul_inv_cancel
  rw [BSeries_constant]
  norm_num

/-- The exact Euler chain rule θ(f(x(q))) = A(q) (Df)(x(q)). -/
theorem euler_subst_x (f : ℚ⟦X⟧) :
    euler (f.subst xSeries) = ASeries * (euler f).subst xSeries := by
  rw [euler, derivative_subst x_hasSubst, euler, subst_mul x_hasSubst, subst_X x_hasSubst]
  have h := ASeries_mul_xSeries
  calc
    _ = (X * derivative ℚ xSeries) * (derivative ℚ f).subst xSeries := by ring
    _ = _ := by rw [← h]; ring

/-- θ in the x coordinate, defined using the actual B. -/
def thetaX (f : ℚ⟦X⟧) : ℚ⟦X⟧ := BSeries * euler f

theorem thetaX_subst_q (f : ℚ⟦X⟧) : thetaX (f.subst qSeries) = (euler f).subst qSeries := by
  apply subst_x_injective
  dsimp only
  rw [thetaX, subst_mul x_hasSubst, BSeries_subst_x, ← euler_subst_x,
    subst_comp_subst_apply q_hasSubst x_hasSubst, q_subst_x, X_subst,
    subst_comp_subst_apply q_hasSubst x_hasSubst, q_subst_x, X_subst]

theorem thetaX_three_subst_q (f : ℚ⟦X⟧) :
    thetaX (thetaX (thetaX (f.subst qSeries))) =
      (euler (euler (euler f))).subst qSeries := by
  rw [thetaX_subst_q, thetaX_subst_q, thetaX_subst_q]

theorem rationalH_subst_x (c : ℚ) :
    (rationalH c).subst xSeries = ASeries * (GSeries + C c) := by
  rw [rationalH, subst_mul x_hasSubst, BSeries_subst_x, subst_add x_hasSubst,
    subst_comp_subst_apply q_hasSubst x_hasSubst, q_subst_x, X_subst, subst_C]
  rfl

/-- The operator L in the manuscript, on complete formal series. -/
def modularL (f : ℚ⟦X⟧) : ℚ⟦X⟧ :=
  euler (euler (euler f)) - rationalPotential * euler f -
    C (1 / 2 : ℚ) * euler rationalPotential * f

def rationalForcing : ℚ⟦X⟧ := X * (1 + 10 * X) * (1 + 13 * X + 49 * X ^ 2)⁻¹

def logarithmicB : ℚ⟦X⟧ := euler BSeries * BSeries⁻¹

/-- The potential constructed from the actual B, before its modular identification. -/
def coordinatePotential : ℚ⟦X⟧ := 2 * euler logarithmicB + logarithmicB ^ 2

def modularDefect : ℚ⟦X⟧ := coordinatePotential - rationalPotential

theorem euler_B : euler BSeries = BSeries * logarithmicB := by
  rw [logarithmicB]
  calc
    _ = (BSeries * BSeries⁻¹) * euler BSeries := by rw [BSeries_mul_inv, one_mul]
    _ = _ := by ring

theorem euler_two : euler (2 : ℚ⟦X⟧) = 0 := by
  simpa only [map_ofNat] using euler_C 2

theorem half_twice : (C (1 / 2 : ℚ) : ℚ⟦X⟧) * 2 = 1 := by
  rw [← map_ofNat C 2, ← map_mul]
  norm_num

/-- Exact conjugation for the potential actually constructed from B.
The difference from the manuscript's V is retained explicitly. -/
theorem coordinate_conjugation (Y : ℚ⟦X⟧) :
    BSeries ^ 2 * (modularL (BSeries * Y) -
      modularDefect * euler (BSeries * Y) -
      C (1 / 2 : ℚ) * euler modularDefect * (BSeries * Y)) =
      thetaX (thetaX (thetaX Y)) := by
  unfold modularL modularDefect coordinatePotential thetaX
  simp only [euler_sub, euler_add, euler_mul, pow_two, euler_B, euler_two,
    zero_mul, zero_add]
  linear_combination -BSeries ^ 3 * Y *
    (euler (euler logarithmicB) + logarithmicB * euler logarithmicB) * half_twice

/-- All-degree differential transport for the actual H, with its exact modular defect.
No equation identifying that defect with zero is presumed. -/
theorem rationalH_differential_transport (c : ℚ) :
    BSeries ^ 2 * (modularL (rationalH c) -
      modularDefect * euler (rationalH c) -
      C (1 / 2 : ℚ) * euler modularDefect * rationalH c) =
      (euler (euler (euler GSeries))).subst qSeries := by
  rw [rationalH]
  rw [coordinate_conjugation]
  have heq : GSeries.subst qSeries + C c = (GSeries + C c).subst qSeries := by
    rw [subst_add q_hasSubst, subst_C]
    rfl
  rw [heq, thetaX_three_subst_q]
  simp only [euler_add, euler_C, add_zero]

/-- An unconditional identity: DK = H LH, before identifying LH with R. -/
theorem euler_quadratic (f : ℚ⟦X⟧) :
    euler (quadratic rationalPotential f) = f * modularL f := by
  unfold quadratic modularL
  simp only [euler_sub, euler_mul, pow_two, euler_C, zero_mul, zero_add]
  have hh : (C (1 / 2 : ℚ) : ℚ⟦X⟧) + C (1 / 2 : ℚ) = 1 := by
    rw [← map_add]; norm_num
  linear_combination -(euler f * euler (euler f) + rationalPotential * f * euler f) * hh

/-- Exact quadratic conjugation, retaining the same concrete potential defect. -/
theorem quadratic_coordinate_identity (Y : ℚ⟦X⟧) :
    quadratic rationalPotential (BSeries * Y) =
      Y * thetaX (thetaX Y) - C (1 / 2 : ℚ) * (thetaX Y) ^ 2 +
        C (1 / 2 : ℚ) * modularDefect * (BSeries * Y) ^ 2 := by
  unfold quadratic thetaX modularDefect coordinatePotential
  simp only [euler_mul, euler_add, euler_B, pow_two]
  linear_combination -BSeries ^ 2 *
    (Y ^ 2 * (euler logarithmicB + logarithmicB ^ 2) + Y * logarithmicB * euler Y) * half_twice

/-- The manuscript's quadratic q-expression, plus its explicit modular residual term. -/
theorem rationalH_quadratic_transport (c : ℚ) :
    quadratic rationalPotential (rationalH c) =
      ((GSeries + C c) * euler (euler GSeries) -
        C (1 / 2 : ℚ) * (euler GSeries) ^ 2).subst qSeries +
      C (1 / 2 : ℚ) * modularDefect * rationalH c ^ 2 := by
  have heq : GSeries.subst qSeries + C c = (GSeries + C c).subst qSeries := by
    rw [subst_add q_hasSubst, subst_C]
    rfl
  rw [rationalH, quadratic_coordinate_identity, heq,
    thetaX_subst_q, thetaX_subst_q]
  simp only [euler_add, euler_C, add_zero]
  rw [subst_sub q_hasSubst, subst_mul q_hasSubst, subst_mul q_hasSubst,
    subst_pow q_hasSubst, subst_C]
  rfl

end Zeta7Common

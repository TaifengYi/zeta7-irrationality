import Zeta7Proof.ActualE4Quotients
import Zeta7Proof.ShortRiccatiAlgebra
import Zeta7Proof.ActualATheta

/-! The actual Riccati identity, with θ transported to B D. All reciprocals
are reciprocals of formal units at the cusp. -/
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open PowerSeries Zeta7Main
namespace Zeta7Common

def qTransport : ℚ⟦X⟧ →ₐ[ℚ] ℚ⟦X⟧ := substAlgHom q_hasSubst

theorem qTransport_apply (f : ℚ⟦X⟧) : qTransport f = f.subst qSeries :=
  congrFun (coe_substAlgHom q_hasSubst) f

theorem qTransport_x : qTransport xSeries = X := by rw [qTransport_apply, x_subst_q]
theorem qTransport_A : qTransport ASeries = BSeries := qTransport_apply ASeries

theorem qTransport_euler (f : ℚ⟦X⟧) :
    qTransport (euler f) = BSeries * euler (qTransport f) := by
  simp only [qTransport_apply]
  exact (thetaX_subst_q f).symm

def pulledE2 : ℚ⟦X⟧ := qTransport eisensteinTwoQ
def pulledE4 : ℚ⟦X⟧ := qTransport eisensteinFourQ
def pulledE4Seven : ℚ⟦X⟧ := qTransport (expand 7 (by decide) eisensteinFourQ)
def actualW : ℚ⟦X⟧ := pulledE2 * BSeries⁻¹

theorem BSeries_ne_zero : BSeries ≠ 0 := by
  intro h
  have hc := congrArg constantCoeff h
  rw [BSeries_constant, map_zero] at hc
  exact one_ne_zero hc

theorem B_mul_actualW : BSeries * actualW = pulledE2 := by
  rw [actualW]
  calc
    _ = pulledE2 * (BSeries * BSeries⁻¹) := by ring
    _ = _ := by rw [BSeries_mul_inv, mul_one]

theorem pulledE4_cleared : shortP * pulledE4 = BSeries ^ 2 * shortN := by
  have h := congrArg qTransport Zeta7LevelSeven.actual_E4_quotient
  simpa only [map_mul, map_add, map_pow, map_one, map_ofNat, qTransport_x, qTransport_A,
    shortP_value, shortN_value, pulledE4] using h

theorem pulledE4Seven_cleared : shortP * pulledE4Seven =
    BSeries ^ 2 * (1 + 5 * X + X ^ 2) := by
  have h := congrArg qTransport Zeta7LevelSeven.actual_E4_seven_quotient
  simpa only [map_mul, map_add, map_pow, map_one, map_ofNat, qTransport_x, qTransport_A,
    shortP_value, pulledE4Seven] using h

theorem pulledE4_eq : pulledE4 = BSeries ^ 2 * shortA := by
  apply mul_left_cancel₀ shortP_ne_zero
  calc
    _ = BSeries ^ 2 * shortN := pulledE4_cleared
    _ = shortP * (BSeries ^ 2 * shortA) := by rw [← shortP_mul_shortA]; ring

theorem A_theta_transported :
    72 * BSeries ^ 2 * logarithmicB = 36 * BSeries ^ 2 +
      12 * BSeries * pulledE2 + pulledE4 - 49 * pulledE4Seven := by
  have h := ASeries_theta_eisenstein
  simp only [map_ofNat] at h
  have ht := congrArg qTransport h
  simp only [map_mul, map_pow, map_add, map_sub, map_ofNat, qTransport_A,
    qTransport_euler, euler_B] at ht
  change 72 * (BSeries * (BSeries * logarithmicB)) =
    36 * BSeries ^ 2 + 12 * BSeries * pulledE2 + pulledE4 - 49 * pulledE4Seven at ht
  linear_combination ht

theorem shortQ_linear_combination :
    12 * shortQ = -36 * shortP - shortN + 49 * (1 + 5 * X + X ^ 2) := by
  have h := congrArg Polynomial.coeToPowerSeries.ringHom Zeta7Riccati.Q_linear_combination
  simpa only [map_mul, map_add, map_sub, map_neg, map_ofNat, map_one, map_pow,
    Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X, shortQ, shortP, shortN] using h

theorem actualW_eq : actualW = 6 * logarithmicB + shortS := by
  have hbig : (12 * BSeries ^ 2) *
      (shortP * actualW - 6 * shortP * logarithmicB - shortQ) = 0 := by
    linear_combination -shortP * A_theta_transported - pulledE4_cleared +
      49 * pulledE4Seven_cleared + 12 * shortP * BSeries * B_mul_actualW -
        BSeries ^ 2 * shortQ_linear_combination
  have h12 : (12 : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have hc := congrArg constantCoeff h
    norm_num [map_ofNat] at hc
  have hs := (mul_eq_zero.mp hbig).resolve_left
    (mul_ne_zero h12 (pow_ne_zero 2 BSeries_ne_zero))
  apply mul_left_cancel₀ shortP_ne_zero
  linear_combination hs - shortP_mul_shortS

theorem E2_ramanujan_transported :
    12 * BSeries * euler pulledE2 = pulledE2 ^ 2 - pulledE4 := by
  have h := Zeta7Classical.eisensteinTwoQ_ramanujan
  simp only [map_ofNat] at h
  have ht := congrArg qTransport h
  simp only [map_mul, map_pow, map_sub, map_ofNat, qTransport_euler] at ht
  change 12 * (BSeries * euler pulledE2) = pulledE2 ^ 2 - pulledE4 at ht
  linear_combination ht

theorem actualW_ramanujan :
    12 * (euler actualW + logarithmicB * actualW) = actualW ^ 2 - shortA := by
  have h := E2_ramanujan_transported
  rw [← B_mul_actualW, euler_mul, euler_B, pulledE4_eq] at h
  apply mul_left_cancel₀ (pow_ne_zero 2 BSeries_ne_zero)
  linear_combination h

/-- The actual differential potential, independent of every analytic radius input. -/
theorem coordinatePotential_eq_rationalPotential : coordinatePotential = rationalPotential := by
  have h := actualW_ramanujan
  have h6 : euler (6 : ℚ⟦X⟧) = 0 := by simpa only [map_ofNat] using euler_C 6
  rw [actualW_eq, euler_add, euler_mul, h6, zero_mul, zero_add] at h
  have h36 : (36 : ℚ⟦X⟧) ≠ 0 := by
    intro hz
    have hc := congrArg constantCoeff hz
    norm_num [map_ofNat] at hc
  apply mul_left_cancel₀ h36
  unfold coordinatePotential
  linear_combination h + shortS_riccati

end Zeta7Common

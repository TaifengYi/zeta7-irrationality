import Zeta7Proof.QParameterLift

/-! Identification with the original coordinate, using the actual Euler products. -/
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open Complex hiding eta
open UpperHalfPlane Function Filter ModularForm
open scoped Real Manifold Topology
namespace Zeta7LevelSeven

theorem etaCoordinate_euler (τ : ℍ) :
    etaCoordinate τ = Periodic.qParam 1 τ *
      (analyticEuler (Periodic.qParam 1 τ) ^ (-4 : ℤ) *
        analyticEuler (Periodic.qParam 1 τ ^ 7) ^ (4 : ℤ)) := by
  have h := eta_product_expansion τ (-4) 4 1 (by norm_num)
  rw [pow_one] at h
  rw [← h, etaCoordinate_value]
  norm_num only [zpow_neg, zpow_ofNat, div_eq_mul_inv]
  ring

theorem etaCoordinate_tendsto : Tendsto etaCoordinate atImInfty (𝓝 0) := by
  have hU := analyticEuler_analyticAt_zero.continuousAt
  have hU7 : ContinuousAt (fun z : ℂ => analyticEuler (z ^ 7)) 0 :=
    hU.comp_of_eq (continuousAt_id.pow 7) (by simp)
  have h := qLift_tendsto ((continuousAt_id : ContinuousAt (fun z : ℂ => z) 0).mul
    ((hU.zpow₀ (-4) (Or.inl (by simp [analyticEuler_zero]))).mul (hU7.pow 4)))
  change Tendsto (fun τ : ℍ => Periodic.qParam 1 τ *
    (analyticEuler (Periodic.qParam 1 τ) ^ (-4 : ℤ) *
      analyticEuler (Periodic.qParam 1 τ ^ 7) ^ 4)) atImInfty (𝓝 (0 * _)) at h
  have he : etaCoordinate = fun τ : ℍ => Periodic.qParam 1 τ *
      (analyticEuler (Periodic.qParam 1 τ) ^ (-4 : ℤ) *
        analyticEuler (Periodic.qParam 1 τ ^ 7) ^ 4) := by
    funext τ
    exact etaCoordinate_euler τ
  rw [he]
  simpa only [zero_mul] using h

theorem etaCoordinate_cusp_analytic : AnalyticAt ℂ (cuspFunction 1 etaCoordinate) 0 :=
  analyticAt_cuspFunction_zero (by norm_num) etaCoordinate_periodic etaCoordinate_holo
    (etaCoordinate_tendsto.isBigO_one ℝ)

theorem etaCoordinate_euler_cleared :
    etaCoordinate * qLift analyticEuler ^ 4 =
      qLift id * qLift (fun z => analyticEuler (z ^ 7)) ^ 4 := by
  funext τ
  have hU : analyticEuler (Periodic.qParam 1 τ) ≠ 0 := by
    exact eta_tprod_ne_zero τ.im_pos
  simp only [Pi.mul_apply, Pi.pow_apply, qLift, id_eq, etaCoordinate_euler,
    zpow_neg, zpow_natCast]
  field_simp

theorem qLift_id_qExpansion : qExpansion 1 (qLift id) = PowerSeries.X := by
  apply qLift_qExpansion (by fun_prop)
  intro z _
  convert (hasSum_ite_eq 1 z) using 1 <;> try rfl
  funext n
  by_cases hn : n = 1 <;> simp [PowerSeries.coeff_X, hn]

theorem xSeries_euler_cleared :
    Zeta7Main.xSeries * Zeta7GenusSeven.euler ^ 4 =
      PowerSeries.X * (PowerSeries.expand 7 (by decide) Zeta7GenusSeven.euler) ^ 4 := by
  rw [← Zeta7GenusSeven.d7_eq_xSeries, Zeta7GenusSeven.d7]
  have hU := PowerSeries.inv_mul_cancel Zeta7GenusSeven.euler
    (by rw [Zeta7GenusSeven.euler_constant]; norm_num)
  calc
    _ = PowerSeries.X * (PowerSeries.expand 7 (by decide) Zeta7GenusSeven.euler) ^ 4 *
        (Zeta7GenusSeven.euler⁻¹ * Zeta7GenusSeven.euler) ^ 4 := by ring
    _ = _ := by rw [hU]; simp

/-- Complete q-expansion of the actual eta coordinate in the original normalization. -/
theorem etaCoordinate_qExpansion :
    qExpansion 1 etaCoordinate = Zeta7Main.xSeries.map (algebraMap ℚ ℂ) := by
  have hU := qLift_cusp_analytic
    (F := analyticEuler) differentiableOn_tprod_one_sub_pow
  have hU7 := qLift_cusp_analytic euler_seven_differentiable
  have hx := congrArg (qExpansion 1) etaCoordinate_euler_cleared
  rw [qExpansion_mul etaCoordinate_cusp_analytic (cuspFunction_pow_analytic hU 4),
    qExpansion_mul (qLift_cusp_analytic (by fun_prop)) (cuspFunction_pow_analytic hU7 4),
    qExpansion_pow hU, qExpansion_pow hU7, euler_qExpansion, euler_seven_qExpansion,
    qLift_id_qExpansion] at hx
  have hf := congrArg (PowerSeries.map (algebraMap ℚ ℂ)) xSeries_euler_cleared
  simp only [map_mul, map_pow, PowerSeries.map_X, PowerSeries.map_expand] at hf
  apply mul_right_cancel₀ (b := (Zeta7GenusSeven.euler.map (algebraMap ℚ ℂ)) ^ 4) ?_
  · exact hx.trans hf.symm
  · apply pow_ne_zero
    intro he
    have hc := congrArg PowerSeries.constantCoeff he
    rw [← PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff, Zeta7GenusSeven.euler_constant, map_one] at hc
    exact one_ne_zero hc

end Zeta7LevelSeven

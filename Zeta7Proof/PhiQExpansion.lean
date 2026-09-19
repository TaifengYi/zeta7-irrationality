import Zeta7Proof.EtaCoordinateQExpansion

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open Complex hiding eta
open UpperHalfPlane Function
open scoped Real Manifold
namespace Zeta7LevelSeven

def phiZeroSeries : PowerSeries ℚ := PowerSeries.X ^ 2 *
  (Zeta7GenusSeven.euler ^ 6 *
    (PowerSeries.expand 7 (by decide) Zeta7GenusSeven.euler) ^ 6)

theorem phi_zero_euler : phi 0 = qLift id ^ 2 *
    (qLift analyticEuler ^ 6 * qLift (fun z => analyticEuler (z ^ 7)) ^ 6) := by
  funext τ
  have h := phi_q_expansion 0 τ
  simpa [phiUnit, qLift, zpow_ofNat] using h

theorem phi_zero_qExpansion :
    qExpansion 1 (phi 0) = phiZeroSeries.map (algebraMap ℚ ℂ) := by
  have he := qLift_cusp_analytic
    (F := analyticEuler) ModularForm.differentiableOn_tprod_one_sub_pow
  have he7 := qLift_cusp_analytic euler_seven_differentiable
  have hi := qLift_cusp_analytic (F := id) (by fun_prop)
  have he6 := cuspFunction_pow_analytic he 6
  have he76 := cuspFunction_pow_analytic he7 6
  have hp : AnalyticAt ℂ (cuspFunction 1
      (qLift analyticEuler ^ 6 * qLift (fun z => analyticEuler (z ^ 7)) ^ 6)) 0 := by
    rw [cuspFunction_mul he6.continuousAt he76.continuousAt]
    exact he6.mul he76
  rw [phi_zero_euler, qExpansion_mul (cuspFunction_pow_analytic hi 2) hp,
    qExpansion_mul he6 he76, qExpansion_pow hi, qExpansion_pow he, qExpansion_pow he7,
    qLift_id_qExpansion, euler_qExpansion, euler_seven_qExpansion]
  simp only [phiZeroSeries, map_mul, map_pow, PowerSeries.map_X, PowerSeries.map_expand]

/-- All three auxiliary forms have complete expansions in the original coordinate. -/
theorem phi_qExpansion (i : Fin 3) :
    qExpansion 1 (phi i) =
      (phiZeroSeries * Zeta7Main.xSeries ^ i.val).map (algebraMap ℚ ℂ) := by
  have h : phi i = phi 0 * etaCoordinate ^ i.val := by
    funext τ
    exact phi_eq_phi_zero_mul_coordinate i τ
  rw [h, qExpansion_mul (phi_cusp_analytic 0)
    (cuspFunction_pow_analytic etaCoordinate_cusp_analytic i.val),
    qExpansion_pow etaCoordinate_cusp_analytic, etaCoordinate_qExpansion, phi_zero_qExpansion]
  simp only [map_mul, map_pow]

theorem phiZeroSeries_order : phiZeroSeries.order = 2 := by
  rw [phiZeroSeries, PowerSeries.order_mul, PowerSeries.order_X_pow]
  have hu : PowerSeries.constantCoeff
      (Zeta7GenusSeven.euler ^ 6 *
        (PowerSeries.expand 7 (by decide) Zeta7GenusSeven.euler) ^ 6) = 1 := by
    simp [Zeta7GenusSeven.euler_constant]
  rw [PowerSeries.order_zero_of_unit (by
    rw [PowerSeries.isUnit_iff_constantCoeff, hu]; exact isUnit_one)]
  simp

end Zeta7LevelSeven

import Zeta7Proof.AnalyticEulerBridge
import Zeta7Proof.WidthSevenQExpansion

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open Complex hiding eta
open UpperHalfPlane Function Filter
open scoped Real Manifold Topology
namespace Zeta7LevelSeven

def qLift (F : ℂ → ℂ) (τ : ℍ) : ℂ := F (Periodic.qParam 1 τ)

theorem qLift_periodic (F : ℂ → ℂ) : Periodic (qLift F ∘ ofComplex) 1 := by
  intro z
  by_cases hz : 0 < z.im
  · have hz' : 0 < (z + 1).im := by simpa using hz
    simp only [Function.comp_apply, ofComplex_apply_of_im_pos hz,
      ofComplex_apply_of_im_pos hz', qLift]
    congr 1
    simp only [Periodic.qParam, ofReal_one, div_one, mul_add, mul_one]
    exact exp_periodic _
  · have hz' : (z + 1).im ≤ 0 := by simpa using le_of_not_gt hz
    simp [ofComplex_apply_of_im_nonpos hz',
      ofComplex_apply_of_im_nonpos (le_of_not_gt hz)]

theorem qLift_holo {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F (Metric.ball 0 1)) : MDiff (qLift F) := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  refine DifferentiableOn.congr (f := F ∘ Periodic.qParam 1) ?_ ?_
  · intro z hz
    have hq : Periodic.qParam 1 z ∈ Metric.ball (0 : ℂ) 1 := by
      simpa using Periodic.norm_qParam_lt_one (by norm_num : (0 : ℝ) < 1) hz
    exact ((hF.differentiableAt (Metric.isOpen_ball.mem_nhds hq)).comp z
      (Periodic.differentiable_qParam.differentiableAt)).differentiableWithinAt
  · intro z hz
    simp [qLift, ofComplex_apply_of_im_pos hz]

theorem qLift_tendsto {F : ℂ → ℂ} (hF : ContinuousAt F 0) :
    Tendsto (qLift F) atImInfty (𝓝 (F 0)) :=
  hF.tendsto.comp (qParam_tendsto_atImInfty (by norm_num : (0 : ℝ) < 1))

theorem qLift_cusp_analytic {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F (Metric.ball 0 1)) :
    AnalyticAt ℂ (cuspFunction 1 (qLift F)) 0 :=
  analyticAt_cuspFunction_zero (by norm_num) (qLift_periodic F) (qLift_holo hF)
    ((qLift_tendsto (hF.differentiableAt
      (Metric.ball_mem_nhds _ zero_lt_one)).continuousAt).isBigO_one ℝ)

theorem qLift_qExpansion {F : ℂ → ℂ} {S : PowerSeries ℂ}
    (hF : DifferentiableOn ℂ F (Metric.ball 0 1))
    (hS : ∀ z : ℂ, ‖z‖ < 1 → HasSum (fun n => S.coeff n * z ^ n) (F z)) :
    qExpansion 1 (qLift F) = S := by
  let fc : C(ℍ, ℂ) := ⟨qLift F, (qLift_holo hF).continuous⟩
  ext n
  apply (qExpansion_coeff_unique fc (by norm_num : (0 : ℝ) < 1)
    (qLift_cusp_analytic hF) (fun τ => ?_) n).symm
  change HasSum (fun n => S.coeff n • Periodic.qParam 1 τ ^ n)
    (F (Periodic.qParam 1 τ))
  simpa only [smul_eq_mul, Nat.cast_one] using hS _ (norm_qParam_lt_one 1 τ)

theorem euler_qExpansion :
    qExpansion 1 (qLift analyticEuler) =
      Zeta7GenusSeven.euler.map (algebraMap ℚ ℂ) := by
  apply qLift_qExpansion (F := analyticEuler)
    ModularForm.differentiableOn_tprod_one_sub_pow
  intro z hz
  simpa only [PowerSeries.coeff_map] using analyticEuler_hasSum hz

theorem pow_seven_ball {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    z ^ 7 ∈ Metric.ball (0 : ℂ) 1 := by
  simp only [Metric.mem_ball, dist_zero_right, norm_pow] at *
  exact pow_lt_one₀ (norm_nonneg _) hz (by decide)

theorem euler_seven_differentiable :
    DifferentiableOn ℂ (fun z => analyticEuler (z ^ 7)) (Metric.ball 0 1) := by
  exact ModularForm.differentiableOn_tprod_one_sub_pow.comp
    (by fun_prop) (fun _ hz => pow_seven_ball hz)

theorem euler_seven_qExpansion :
    qExpansion 1 (qLift (fun z => analyticEuler (z ^ 7))) =
      PowerSeries.expand 7 (by decide) (Zeta7GenusSeven.euler.map (algebraMap ℚ ℂ)) := by
  apply qLift_qExpansion euler_seven_differentiable
  intro z hz
  apply hasSum_expand_seven
  simpa only [PowerSeries.coeff_map] using
    analyticEuler_hasSum (by simpa using pow_seven_ball (by simpa using hz))

theorem cuspFunction_pow_analytic {f : ℍ → ℂ}
    (hf : AnalyticAt ℂ (cuspFunction 1 f) 0) (n : ℕ) :
    AnalyticAt ℂ (cuspFunction 1 (f ^ n)) 0 := by
  induction n with
  | zero =>
    have h : cuspFunction 1 (1 : ℍ → ℂ) = 1 := by
      simpa [cuspFunction, Periodic.cuspFunction] using!
        (tendsto_const_nhds.mono_left nhdsWithin_le_nhds).limUnder_eq
    rw [pow_zero, h]
    change AnalyticAt ℂ (fun _ : ℂ => (1 : ℂ)) 0
    exact analyticAt_const
  | succ n ih =>
    rw [pow_succ, cuspFunction_mul ih.continuousAt hf.continuousAt]
    exact ih.mul hf

theorem qExpansion_pow {f : ℍ → ℂ}
    (hf : AnalyticAt ℂ (cuspFunction 1 f) 0) (n : ℕ) :
    qExpansion 1 (f ^ n) = qExpansion 1 f ^ n := by
  induction n with
  | zero => simp [qExpansion_one]
  | succ n ih =>
    rw [pow_succ, qExpansion_mul (cuspFunction_pow_analytic hf n) hf, ih, pow_succ]

end Zeta7LevelSeven

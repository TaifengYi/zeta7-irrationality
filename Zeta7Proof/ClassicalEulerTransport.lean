/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca

Adapted from the archived ANR-FALSE PadicModForms/ForMathlib/QExpansionDeriv.lean
to the pinned Mathlib and the project's existing Euler operator. No dependency
pins are changed, and the source's mathematical proofs are checked locally.
-/
import Zeta7Proof.ModularDifferentialTransport
import Mathlib.NumberTheory.ModularForms.Derivative

noncomputable section
open UpperHalfPlane hiding I
open Complex Filter Function Derivative PowerSeries Function.Periodic
open scoped Real Topology ModularForm Manifold

namespace Zeta7Classical

theorem hasDerivAt_qParam (h : ℝ) (z : ℂ) :
    HasDerivAt (qParam h) (2 * π * I / h * qParam h z) z :=
  (((hasDerivAt_id z).const_mul _).div_const h).cexp.congr_deriv (by grind [qParam])

theorem iteratedDeriv_id_mul_zero {n : ℕ} {g : ℂ → ℂ} (hg : ContDiffAt ℂ n g 0) :
    iteratedDeriv n (fun w ↦ w * g w) 0 = n * iteratedDeriv (n - 1) g 0 := by
  rw [show (fun w : ℂ ↦ w * g w) = id * g from rfl,
    iteratedDeriv_mul contDiffAt_id hg, Finset.sum_eq_single 1]
  · simp [iteratedDeriv_id]
  · intro i _ hi
    simp [iteratedDeriv_id, hi]
  · intro hn
    simp [show n = 0 by grind [not_lt], iteratedDeriv_id]

variable {h : ℝ} {f : ℍ → ℂ}

theorem comp_eq_cuspFunction (hh : h ≠ 0) (hfper : Periodic (f ∘ ofComplex) h) :
    (f ∘ ofComplex) = cuspFunction h f ∘ qParam h :=
  funext fun z ↦ (Periodic.eq_cuspFunction hh hfper z).symm

section
variable (hh : 0 < h) (hfper : Periodic (f ∘ ofComplex) h) (hfhol : MDiff f)
  (hfbdd : IsBoundedAtImInfty f)
include hh hfper hfhol hfbdd

theorem normalizedDeriv_eq (τ : ℍ) : normalizedDerivOfComplex f τ =
    (h : ℂ)⁻¹ * (qParam h τ * deriv (cuspFunction h f) (qParam h τ)) := by
  rw [normalizedDerivOfComplex, comp_eq_cuspFunction hh.ne' hfper,
    ((differentiableAt_cuspFunction hh hfper hfhol hfbdd
    (Periodic.norm_qParam_lt_one hh τ.im_pos)).hasDerivAt.comp _ (hasDerivAt_qParam h τ)).deriv]
  field_simp

theorem analyticAt_deriv_cuspFunction : AnalyticAt ℂ (deriv (cuspFunction h f)) 0 :=
  (analyticAt_cuspFunction_zero hh hfper hfhol hfbdd).deriv

theorem cuspFunction_deriv_of_ne_zero {w : ℂ} (hw : ‖w‖ < 1) (hw0 : w ≠ 0) :
    cuspFunction h (normalizedDerivOfComplex f) w =
      (h : ℂ)⁻¹ * (w * deriv (cuspFunction h f) w) := by
  have him := im_invQParam_pos_of_norm_lt_one hh hw hw0
  rw [UpperHalfPlane.cuspFunction, cuspFunction_eq_of_nonzero _ _ hw0, comp_apply,
    ofComplex_apply_of_im_pos him]
  simpa [qParam_right_inv hh.ne' hw0]
    using normalizedDeriv_eq hh hfper hfhol hfbdd ⟨_, him⟩

theorem cuspFunction_deriv_zero : cuspFunction h (normalizedDerivOfComplex f) 0 = 0 := by
  have hev : cuspFunction h (normalizedDerivOfComplex f) =ᶠ[𝓝[≠] 0]
      fun w ↦ (h : ℂ)⁻¹ * (w * deriv (cuspFunction h f) w) := by
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds
      (Metric.ball_mem_nhds 0 one_pos), self_mem_nhdsWithin] with w hw hw0
    exact cuspFunction_deriv_of_ne_zero hh hfper hfhol hfbdd (mem_ball_zero_iff.mp hw) hw0
  rw [UpperHalfPlane.cuspFunction, cuspFunction_zero_eq_limUnder_nhds_ne,
    ← UpperHalfPlane.cuspFunction]
  refine Tendsto.limUnder_eq ?_
  have hc : ContinuousAt (fun w ↦ (h : ℂ)⁻¹ * (w * deriv (cuspFunction h f) w)) 0 :=
    continuousAt_const.mul <|
      continuousAt_id.mul (analyticAt_deriv_cuspFunction hh hfper hfhol hfbdd).continuousAt
  have ht : Tendsto (fun w ↦ (h : ℂ)⁻¹ * (w * deriv (cuspFunction h f) w)) (𝓝 0) (𝓝 0) :=
    by simpa using hc.tendsto
  simpa [tendsto_congr' hev] using ht.mono_left nhdsWithin_le_nhds

theorem cuspFunction_deriv {w : ℂ} (hw : ‖w‖ < 1) :
    cuspFunction h (normalizedDerivOfComplex f) w =
      (h : ℂ)⁻¹ * (w * deriv (cuspFunction h f) w) := by
  rcases eq_or_ne w 0 with rfl | hw0
  · simpa using cuspFunction_deriv_zero hh hfper hfhol hfbdd
  · exact cuspFunction_deriv_of_ne_zero hh hfper hfhol hfbdd hw hw0

/-- Exact transport of the analytic normalized derivative to the formal Euler
operator. Here the series variable is q, so this is θ, not x d/dx. -/
theorem qExpansion_normalizedDeriv :
    qExpansion h (normalizedDerivOfComplex f) =
      (h : ℂ)⁻¹ • Zeta7Common.euler (qExpansion h f) := by
  ext n
  have heq : cuspFunction h (normalizedDerivOfComplex f) =ᶠ[𝓝 0]
      fun w ↦ (h : ℂ)⁻¹ * (w * deriv (cuspFunction h f) w) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) one_pos] with w hw
    exact cuspFunction_deriv hh hfper hfhol hfbdd (mem_ball_zero_iff.mp hw)
  rw [qExpansion_coeff, heq.iteratedDeriv_eq n, iteratedDeriv_const_mul_field,
    iteratedDeriv_id_mul_zero (analyticAt_deriv_cuspFunction hh hfper hfhol hfbdd).contDiffAt]
  rcases n with _ | m
  · simp [qExpansion_coeff, Zeta7Common.euler_coeff]
  · rw [Nat.add_sub_cancel, ← iteratedDeriv_succ']
    simp only [coeff_smul, Zeta7Common.euler_coeff, qExpansion_coeff, smul_eq_mul]
    ring

theorem normalizedDeriv_zero_at_infty : IsZeroAtImInfty (normalizedDerivOfComplex f) := by
  have hc : ContinuousAt (fun w : ℂ ↦ (h : ℂ)⁻¹ * (w * deriv (cuspFunction h f) w)) 0 :=
    continuousAt_const.mul <|
      continuousAt_id.mul (analyticAt_deriv_cuspFunction hh hfper hfhol hfbdd).continuousAt
  have ht := hc.tendsto.comp (qParam_tendsto_atImInfty hh)
  change Tendsto (normalizedDerivOfComplex f) atImInfty (𝓝 0)
  have he : normalizedDerivOfComplex f = fun τ : ℍ =>
      (h : ℂ)⁻¹ * (qParam h τ * deriv (cuspFunction h f) (qParam h τ)) :=
    funext (normalizedDeriv_eq hh hfper hfhol hfbdd)
  rw [he]
  simpa only [Function.comp_def, zero_mul, mul_zero] using ht

end

theorem qExpansion_normalizedDeriv_one (hfper : Periodic (f ∘ ofComplex) 1)
    (hfhol : MDiff f) (hfbdd : IsBoundedAtImInfty f) :
    qExpansion 1 (normalizedDerivOfComplex f) = Zeta7Common.euler (qExpansion 1 f) := by
  simpa using qExpansion_normalizedDeriv one_pos hfper hfhol hfbdd

end Zeta7Classical

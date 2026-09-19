import Zeta7Proof.ArchEmpirical

/-! The complete C1 endpoint, instantiated for the actual six-circle measure.

`potentialMeasure = Σ_i w_i μ_i`, where `μ_i` is the pushforward of normalized angular measure on
`[0, 2π]` under `θ ↦ x(r_i e^{iθ})`, `x = evalQ xC` the actual coordinate `q ∏_{7∤m}(1-q^m)^{-4}`,
and `r_i = e^{-2π y_i}` with the C5 heights and weights. -/
noncomputable section
set_option autoImplicit false
namespace Zeta7Arch
open MeasureTheory Set Real Filter Topology

/-- The measures are exactly the pushforwards of angular measure under the actual map. -/
theorem circleMeasure_def (i : Fin 6) :
    circleMeasure i = angularMeasure.map fun θ : ℝ =>
      evalQ xC ((Real.exp (-(2 * π * circleY i)) : ℂ) * Complex.exp (θ * Complex.I)) := rfl

theorem potentialMeasure_def :
    potentialMeasure = ∑ i, ENNReal.ofReal (circleW i) • circleMeasure i := rfl

/-- **C1.** -/
theorem c1_endpoint :
    IsProbabilityMeasure potentialMeasure ∧
    (∀ i, IsProbabilityMeasure (circleMeasure i)) ∧
    (∑ i, circleW i = 1) ∧ (∀ i, 0 < circleW i) ∧
    IsCompact supportSet ∧ potentialMeasure supportSetᶜ = 0 ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∃ α : ℝ, 0 < α ∧ ∀ z : ℂ, ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
      potentialMeasure (Metric.ball z ρ) ≤ ENNReal.ofReal (C * ρ ^ α)) ∧
    (∀ M : ℝ, 0 ≤ M → ∀ z : ℂ, ∫⁻ w, (Metric.ball z (exp (-M))).indicator
        (fun w => ENNReal.ofReal (-Real.log ‖z - w‖)) w ∂potentialMeasure ≤
      ENNReal.ofReal (tailBound M)) ∧
    Tendsto tailBound atTop (𝓝 0) ∧
    (∀ M : ℝ, 0 ≤ M → Continuous (potentialUM M)) ∧
    TendstoUniformly potentialUM potentialU atTop ∧
    (∀ z : ℂ, Integrable (fun w => Real.log ‖z - w‖) potentialMeasure) ∧
    Continuous potentialU ∧
    (∀ z ∈ supportSet, |potentialU z| ≤ 2 * supR + tailBound 0) ∧
    Integrable potentialU potentialMeasure ∧
    Integrable (fun p : ℂ × ℂ => Real.log ‖p.1 - p.2‖) (potentialMeasure.prod potentialMeasure) ∧
    energyI = ∫ p, Real.log ‖p.1 - p.2‖ ∂(potentialMeasure.prod potentialMeasure) ∧
    energyI = ∫ w, ∫ z, Real.log ‖z - w‖ ∂potentialMeasure ∂potentialMeasure :=
  ⟨inferInstance, fun _ => inferInstance, circleW_sum, circleW_pos, isCompact_supportSet,
    potentialMeasure_compl_support, potentialMeasure_small_ball,
    fun _ hM z => tail_lintegral_le z hM, tailBound_tendsto,
    fun _ hM => potentialUM_continuous hM, potentialUM_tendstoUniformly, integrable_log,
    potentialU_continuous, potentialU_bounded_on_support, integrable_potentialU,
    integrable_log_prod, energyI_eq_prod, energyI_eq_iterated_symm⟩

end Zeta7Arch

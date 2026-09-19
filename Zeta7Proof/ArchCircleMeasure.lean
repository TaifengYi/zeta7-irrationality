import Zeta7Proof.ArchCircleSmallBall

/-! C1, step 4: the actual six-circle measure and its small-ball estimate (38).

The six heights and weights are those fixed in C5:

`(y_i) = (1/2, 1/5, 19/200, 11/200, 7/200, 23/1000)`,
`(w_i) = (1/25, 2/25, 7/50, 17/100, 6/25, 33/100)`,

with radii `r_i = e^{-2π y_i} ∈ (0, 1)`. `angularMeasure` is normalized Lebesgue measure on
`[0, 2π]`; `circleMeasure i` is its pushforward under the actual map `θ ↦ x(r_i e^{iθ})`; and
`potentialMeasure = Σ w_i μ_i`. We prove that these are probability measures, that `μ` is carried
by the compact union of the six image curves, the integration formulas against `μ_i` and `μ`,
and the uniform small-ball estimate

`μ(B(z, ρ)) ≤ C ρ^α`   for all `z ∈ ℂ`, `0 < ρ ≤ 1`,

with `C ≥ 0`, `α > 0` independent of `z` and `ρ` (`potentialMeasure_small_ball`). -/
noncomputable section
set_option autoImplicit false
namespace Zeta7Arch
open MeasureTheory Set Real

/-- The C5 heights `y_i`. -/
def circleY : Fin 6 → ℝ := ![1/2, 1/5, 19/200, 11/200, 7/200, 23/1000]

/-- The C5 weights `w_i`. -/
def circleW : Fin 6 → ℝ := ![1/25, 2/25, 7/50, 17/100, 6/25, 33/100]

/-- The radii `r_i = e^{-2π y_i}`. -/
def circleR (i : Fin 6) : ℝ := Real.exp (-(2 * π * circleY i))

theorem circleY_pos (i : Fin 6) : 0 < circleY i := by
  fin_cases i <;> norm_num [circleY]

theorem circleW_pos (i : Fin 6) : 0 < circleW i := by
  fin_cases i <;> norm_num [circleW]

theorem circleW_sum : ∑ i, circleW i = 1 := by
  simp [circleW, Fin.sum_univ_succ]
  norm_num

theorem circleR_pos (i : Fin 6) : 0 < circleR i := Real.exp_pos _

theorem circleR_lt_one (i : Fin 6) : circleR i < 1 := by
  rw [circleR, Real.exp_lt_one_iff]
  have := circleY_pos i
  have := Real.pi_pos
  simp only [Left.neg_neg_iff]
  positivity

/-! ### Normalized angular measure -/

/-- Normalized Lebesgue measure on `[0, 2π]`. -/
def angularMeasure : Measure ℝ := (ENNReal.ofReal (2 * π))⁻¹ • volume.restrict (Icc 0 (2 * π))

theorem two_pi_ofReal_ne_zero : ENNReal.ofReal (2 * π) ≠ 0 := by
  rw [Ne, ENNReal.ofReal_eq_zero, not_le]
  positivity

instance angularMeasure_isProbability : IsProbabilityMeasure angularMeasure := by
  constructor
  rw [angularMeasure, Measure.smul_apply, Measure.restrict_apply_univ, Real.volume_Icc, sub_zero,
    smul_eq_mul]
  exact ENNReal.inv_mul_cancel two_pi_ofReal_ne_zero ENNReal.ofReal_ne_top

theorem integral_angularMeasure (g : ℝ → ℝ) :
    ∫ θ, g θ ∂angularMeasure = (2 * π)⁻¹ * ∫ θ in Icc 0 (2 * π), g θ := by
  rw [angularMeasure, integral_smul_measure, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (by positivity), smul_eq_mul]

/-! ### The six circle measures -/

theorem circFun_measurable (i : Fin 6) : Measurable (circFun (circleR i)) :=
  (circFun_continuous (circleR_pos i).le (circleR_lt_one i)).measurable

/-- `μ_i`: the pushforward of normalized angular measure under `θ ↦ x(r_i e^{iθ})`. -/
def circleMeasure (i : Fin 6) : Measure ℂ := angularMeasure.map (circFun (circleR i))

instance circleMeasure_isProbability (i : Fin 6) : IsProbabilityMeasure (circleMeasure i) :=
  Measure.isProbabilityMeasure_map (circFun_measurable i).aemeasurable

/-- `μ = Σ w_i μ_i`. -/
def potentialMeasure : Measure ℂ := ∑ i, ENNReal.ofReal (circleW i) • circleMeasure i

theorem potentialMeasure_univ : potentialMeasure univ = 1 := by
  simp only [potentialMeasure, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => (circleW_pos i).le), circleW_sum,
    ENNReal.ofReal_one]

instance potentialMeasure_isProbability : IsProbabilityMeasure potentialMeasure :=
  ⟨potentialMeasure_univ⟩

/-! ### Integration formulas -/

/-- Integration against `μ_i` is normalized angular integration. -/
theorem integral_circleMeasure (i : Fin 6) {f : ℂ → ℝ}
    (hf : AEStronglyMeasurable f (circleMeasure i)) :
    ∫ w, f w ∂circleMeasure i =
      (2 * π)⁻¹ * ∫ θ in Icc 0 (2 * π), f (circFun (circleR i) θ) := by
  rw [circleMeasure, integral_map (circFun_measurable i).aemeasurable hf, integral_angularMeasure]

/-- Integration against `μ` is the weighted sum of the six angular integrals. -/
theorem integral_potentialMeasure {f : ℂ → ℝ} (hf : ∀ i, Integrable f (circleMeasure i)) :
    ∫ w, f w ∂potentialMeasure = ∑ i, circleW i * ∫ w, f w ∂circleMeasure i := by
  rw [potentialMeasure,
    integral_finsetSum_measure (fun i _ => (hf i).smul_measure ENNReal.ofReal_ne_top)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_smul_measure, ENNReal.toReal_ofReal (circleW_pos i).le, smul_eq_mul]

theorem integral_potentialMeasure_angular {f : ℂ → ℝ} (hf : ∀ i, Integrable f (circleMeasure i)) :
    ∫ w, f w ∂potentialMeasure =
      ∑ i, circleW i * ((2 * π)⁻¹ * ∫ θ in Icc 0 (2 * π), f (circFun (circleR i) θ)) := by
  rw [integral_potentialMeasure hf]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_circleMeasure i (hf i).aestronglyMeasurable]

/-! ### Support -/

/-- The image of the `i`-th circle under `x`. -/
def circleImage (i : Fin 6) : Set ℂ := circFun (circleR i) '' Icc 0 (2 * π)

theorem isCompact_circleImage (i : Fin 6) : IsCompact (circleImage i) :=
  isCompact_Icc.image (circFun_continuous (circleR_pos i).le (circleR_lt_one i))

/-- The compact union of the six image curves. -/
def supportSet : Set ℂ := ⋃ i, circleImage i

theorem isCompact_supportSet : IsCompact supportSet := isCompact_iUnion isCompact_circleImage

theorem circleMeasure_compl_image (i : Fin 6) : circleMeasure i (circleImage i)ᶜ = 0 := by
  have hmeas : MeasurableSet (circleImage i)ᶜ :=
    (isCompact_circleImage i).isClosed.measurableSet.compl
  rw [circleMeasure, Measure.map_apply (circFun_measurable i) hmeas, angularMeasure,
    Measure.smul_apply, Measure.restrict_apply (circFun_measurable i hmeas)]
  have he : circFun (circleR i) ⁻¹' (circleImage i)ᶜ ∩ Icc 0 (2 * π) = ∅ := by
    ext θ
    simp only [mem_inter_iff, mem_preimage, mem_compl_iff, mem_empty_iff_false, iff_false,
      not_and]
    intro hθ hI
    exact hθ ⟨θ, hI, rfl⟩
  rw [he, measure_empty, smul_zero]

theorem circleMeasure_compl_support (i : Fin 6) : circleMeasure i supportSetᶜ = 0 :=
  measure_mono_null (compl_subset_compl.mpr (subset_iUnion circleImage i))
    (circleMeasure_compl_image i)

/-- `μ` is carried by the compact set `supportSet`. -/
theorem potentialMeasure_compl_support : potentialMeasure supportSetᶜ = 0 := by
  simp only [potentialMeasure, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
    circleMeasure_compl_support, smul_zero, Finset.sum_const_zero]

theorem ae_mem_supportSet : ∀ᵐ w ∂potentialMeasure, w ∈ supportSet :=
  measure_eq_zero_iff_ae_notMem.mp potentialMeasure_compl_support |>.mono fun _ h => not_not.mp h

/-! ### The small-ball estimate (38) -/

theorem circleMeasure_ball (i : Fin 6) (z : ℂ) (ρ : ℝ) :
    circleMeasure i (Metric.ball z ρ) = (ENNReal.ofReal (2 * π))⁻¹ *
      volume {θ ∈ Icc (0 : ℝ) (2 * π) | ‖circFun (circleR i) θ - z‖ < ρ} := by
  rw [circleMeasure, Measure.map_apply (circFun_measurable i) Metric.isOpen_ball.measurableSet,
    angularMeasure, Measure.smul_apply,
    Measure.restrict_apply (circFun_measurable i Metric.isOpen_ball.measurableSet), smul_eq_mul]
  congr 2
  ext θ
  simp only [mem_inter_iff, mem_preimage, Metric.mem_ball, dist_eq_norm, mem_ofPred_eq]
  exact and_comm

/-- **The small-ball estimate (38)** for the actual six-circle measure. -/
theorem potentialMeasure_small_ball :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ α : ℝ, 0 < α ∧ ∀ z : ℂ, ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
      potentialMeasure (Metric.ball z ρ) ≤ ENNReal.ofReal (C * ρ ^ α) := by
  choose C α hC hα hball using fun i : Fin 6 => arc_small_ball (circleR_pos i) (circleR_lt_one i)
  set a : ℝ := Finset.univ.inf' Finset.univ_nonempty α with ha
  have ha0 : 0 < a := (Finset.lt_inf'_iff _).mpr fun i _ => hα i
  have hai : ∀ i, a ≤ α i := fun i => Finset.inf'_le _ (Finset.mem_univ i)
  set K : ℝ := ∑ i, circleW i * ((2 * π)⁻¹ * C i) with hK
  have hterm0 : ∀ i, 0 ≤ circleW i * ((2 * π)⁻¹ * C i) := fun i =>
    mul_nonneg (circleW_pos i).le (mul_nonneg (by positivity) (hC i))
  refine ⟨K, Finset.sum_nonneg fun i _ => hterm0 i, a, ha0, fun z ρ hρ hρ1 => ?_⟩
  have hpiece : ∀ i, ENNReal.ofReal (circleW i) * circleMeasure i (Metric.ball z ρ) ≤
      ENNReal.ofReal (circleW i * ((2 * π)⁻¹ * C i) * ρ ^ a) := by
    intro i
    rw [circleMeasure_ball]
    have hv := hball i z ρ hρ hρ1
    have hpow : ρ ^ α i ≤ ρ ^ a := Real.rpow_le_rpow_of_exponent_ge hρ hρ1 (hai i)
    calc ENNReal.ofReal (circleW i) * ((ENNReal.ofReal (2 * π))⁻¹ *
          volume {θ ∈ Icc (0 : ℝ) (2 * π) | ‖circFun (circleR i) θ - z‖ < ρ})
        ≤ ENNReal.ofReal (circleW i) * ((ENNReal.ofReal (2 * π))⁻¹ *
            ENNReal.ofReal (C i * ρ ^ α i)) := by gcongr
      _ = ENNReal.ofReal (circleW i * ((2 * π)⁻¹ * (C i * ρ ^ α i))) := by
          rw [← ENNReal.ofReal_inv_of_pos (by positivity),
            ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (circleW_pos i).le]
      _ ≤ ENNReal.ofReal (circleW i * ((2 * π)⁻¹ * C i) * ρ ^ a) := by
          apply ENNReal.ofReal_le_ofReal
          have h1 : 0 ≤ circleW i * ((2 * π)⁻¹ * C i) := hterm0 i
          calc circleW i * ((2 * π)⁻¹ * (C i * ρ ^ α i))
              = circleW i * ((2 * π)⁻¹ * C i) * ρ ^ α i := by ring
            _ ≤ circleW i * ((2 * π)⁻¹ * C i) * ρ ^ a := mul_le_mul_of_nonneg_left hpow h1
  calc potentialMeasure (Metric.ball z ρ)
      = ∑ i, ENNReal.ofReal (circleW i) * circleMeasure i (Metric.ball z ρ) := by
        simp only [potentialMeasure, Measure.coe_finsetSum, Finset.sum_apply,
          Measure.smul_apply, smul_eq_mul]
    _ ≤ ∑ i, ENNReal.ofReal (circleW i * ((2 * π)⁻¹ * C i) * ρ ^ a) :=
        Finset.sum_le_sum fun i _ => hpiece i
    _ = ENNReal.ofReal (K * ρ ^ a) := by
        rw [hK, Finset.sum_mul, ENNReal.ofReal_sum_of_nonneg]
        intro i _
        exact mul_nonneg (hterm0 i) (Real.rpow_nonneg hρ.le _)

/-- `μ` has no atoms. -/
theorem potentialMeasure_singleton (z : ℂ) : potentialMeasure {z} = 0 := by
  obtain ⟨C, hC, α, hα, hball⟩ := potentialMeasure_small_ball
  have h1 : Filter.Tendsto (fun ρ : ℝ => ρ ^ α) (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0) := by
    have h := (Real.continuousAt_rpow_const (0 : ℝ) α (Or.inr hα.le)).tendsto
    rw [Real.zero_rpow hα.ne'] at h
    exact h.mono_left nhdsWithin_le_nhds
  have h2 := h1.const_mul C
  rw [mul_zero] at h2
  have hlim := ENNReal.tendsto_ofReal h2
  rw [ENNReal.ofReal_zero] at hlim
  have hev : ∀ᶠ ρ in nhdsWithin (0 : ℝ) (Ioi 0),
      potentialMeasure {z} ≤ ENNReal.ofReal (C * ρ ^ α) := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds one_pos)] with ρ h1 h2
    exact (measure_mono (singleton_subset_iff.mpr (Metric.mem_ball_self h1))).trans
      (hball z ρ h1 (le_of_lt h2))
  exact le_antisymm (ge_of_tendsto hlim hev) zero_le

end Zeta7Arch

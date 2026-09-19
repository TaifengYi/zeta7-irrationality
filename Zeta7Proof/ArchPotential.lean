import Zeta7Proof.ArchPotentialTail

/-! C1, step 6: the logarithmic potential of the actual measure is finite and continuous, and the
logarithmic energy is finite.

* `truncLog M z w = log (max |z-w| e^{-M}) = max (log|z-w|, -M)` is continuous on `ℂ × ℂ`
  (no `log 0` is evaluated), with `-M ≤ truncLog ≤ |z-w|` for `M ≥ 0`.
* `potentialUM M z = ∫ truncLog M z w dμ(w)` is continuous (dominated convergence with a bound
  uniform on a neighbourhood of each centre, using the compact support of `μ`).
* For every `z`, `w ↦ log|z-w|` is `μ`-integrable, and `|U(z) - U_M(z)| ≤ tailBound M` for all
  `z` and `M ≥ 0`; hence `U_M → U` uniformly and `U = ∫ log|z-w| dμ(w)` is continuous.
* `|U(z)| ≤ |z| + R + tailBound 0`, with `R` a bound for the support, so `U` is bounded on the
  support and the energy `I = ∫ U dμ = ∬ log|z-w| dμ(z) dμ(w)` is finite; the product integral
  exists and equals both iterated integrals. -/
noncomputable section
set_option autoImplicit false
namespace Zeta7Arch
open MeasureTheory Set Real Filter Topology

/-! ### The support bound -/

theorem exists_support_bound : ∃ R : ℝ, 0 ≤ R ∧ ∀ w ∈ supportSet, ‖w‖ ≤ R := by
  obtain ⟨R, hR⟩ := isCompact_supportSet.isBounded.exists_norm_le
  exact ⟨max R 0, le_max_right _ _, fun w hw => (hR w hw).trans (le_max_left _ _)⟩

/-- A bound for the support of `μ`. -/
def supR : ℝ := exists_support_bound.choose

theorem supR_nonneg : 0 ≤ supR := exists_support_bound.choose_spec.1

theorem norm_le_supR {w : ℂ} (hw : w ∈ supportSet) : ‖w‖ ≤ supR :=
  exists_support_bound.choose_spec.2 w hw

theorem ae_norm_le_supR : ∀ᵐ w ∂potentialMeasure, ‖w‖ ≤ supR :=
  ae_mem_supportSet.mono fun _ hw => norm_le_supR hw

theorem ae_ne (z : ℂ) : ∀ᵐ w ∂potentialMeasure, w ≠ z :=
  (measure_eq_zero_iff_ae_notMem.mp (potentialMeasure_singleton z)).mono fun _ h => h

/-! ### The truncated kernel -/

/-- `max(log|z-w|, -M)`, written as `log(max(|z-w|, e^{-M}))`. -/
def truncLog (M : ℝ) (z w : ℂ) : ℝ := Real.log (max ‖z - w‖ (exp (-M)))

theorem truncLog_arg_pos (M : ℝ) (z w : ℂ) : 0 < max ‖z - w‖ (exp (-M)) :=
  lt_of_lt_of_le (exp_pos (-M)) (le_max_right _ _)

theorem truncLog_continuous (M : ℝ) : Continuous fun p : ℂ × ℂ => truncLog M p.1 p.2 := by
  unfold truncLog
  exact Continuous.log (by fun_prop) fun p => (truncLog_arg_pos M p.1 p.2).ne'

theorem truncLog_ge (M : ℝ) (z w : ℂ) : -M ≤ truncLog M z w := by
  unfold truncLog
  calc -M = Real.log (exp (-M)) := (Real.log_exp _).symm
    _ ≤ _ := Real.log_le_log (exp_pos _) (le_max_right _ _)

theorem truncLog_le {M : ℝ} (hM : 0 ≤ M) (z w : ℂ) : truncLog M z w ≤ ‖z - w‖ := by
  unfold truncLog
  have he : exp (-M) ≤ 1 := exp_le_one_iff.mpr (by linarith)
  have h1 : max ‖z - w‖ (exp (-M)) ≤ ‖z - w‖ + 1 :=
    max_le (by linarith [norm_nonneg (z - w)]) (by linarith [norm_nonneg (z - w)])
  have h2 := Real.log_le_sub_one_of_pos (truncLog_arg_pos M z w)
  linarith

theorem abs_truncLog_le {M : ℝ} (hM : 0 ≤ M) (z w : ℂ) : |truncLog M z w| ≤ M + ‖z - w‖ :=
  abs_le.mpr ⟨by linarith [truncLog_ge M z w, norm_nonneg (z - w)],
    by linarith [truncLog_le hM z w]⟩

theorem truncLog_measurable (M : ℝ) (z : ℂ) : Measurable (truncLog M z) :=
  ((truncLog_continuous M).comp (continuous_const.prodMk continuous_id)).measurable

/-- The kernel difference is dominated by the logarithmic tail, away from the centre. -/
theorem log_sub_truncLog_le {M : ℝ} (hM : 0 ≤ M) {z w : ℂ} (hne : w ≠ z) :
    ENNReal.ofReal |Real.log ‖z - w‖ - truncLog M z w| ≤
      (Metric.ball z (exp (-M))).indicator (fun w => ENNReal.ofReal (-Real.log ‖z - w‖)) w := by
  have hd0 : 0 < ‖z - w‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne.symm)
  by_cases hd : exp (-M) ≤ ‖z - w‖
  · have : truncLog M z w = Real.log ‖z - w‖ := by rw [truncLog, max_eq_left hd]
    rw [this, sub_self, abs_zero, ENNReal.ofReal_zero]
    exact zero_le
  · push Not at hd
    have hmem : w ∈ Metric.ball z (exp (-M)) := by
      rw [Metric.mem_ball, dist_eq_norm, ← norm_neg, neg_sub]; exact hd
    rw [indicator_of_mem hmem]
    have ht : truncLog M z w = -M := by rw [truncLog, max_eq_right hd.le, Real.log_exp]
    have hlog : Real.log ‖z - w‖ < -M := by
      rw [← Real.log_exp (-M)]; exact Real.log_lt_log hd0 hd
    rw [ht]
    apply ENNReal.ofReal_le_ofReal
    rw [abs_of_neg (by linarith)]
    linarith

/-! ### Integrability -/

theorem integrable_truncLog {M : ℝ} (hM : 0 ≤ M) (z : ℂ) :
    Integrable (truncLog M z) potentialMeasure := by
  refine Integrable.of_bound (truncLog_measurable M z).aestronglyMeasurable (M + ‖z‖ + supR) ?_
  filter_upwards [ae_norm_le_supR] with w hw
  rw [Real.norm_eq_abs]
  calc |truncLog M z w| ≤ M + ‖z - w‖ := abs_truncLog_le hM z w
    _ ≤ M + (‖z‖ + ‖w‖) := by gcongr; exact norm_sub_le _ _
    _ ≤ M + ‖z‖ + supR := by linarith

theorem lintegral_log_sub_truncLog_le {M : ℝ} (hM : 0 ≤ M) (z : ℂ) :
    ∫⁻ w, ‖Real.log ‖z - w‖ - truncLog M z w‖ₑ ∂potentialMeasure ≤
      ENNReal.ofReal (tailBound M) := by
  refine le_trans (lintegral_mono_ae ?_) (tail_lintegral_le z hM)
  filter_upwards [ae_ne z] with w hw
  rw [Real.enorm_eq_ofReal_abs]
  exact log_sub_truncLog_le hM hw

theorem integrable_log_sub_truncLog {M : ℝ} (hM : 0 ≤ M) (z : ℂ) :
    Integrable (fun w => Real.log ‖z - w‖ - truncLog M z w) potentialMeasure :=
  ⟨((measurable_log_dist z).sub (truncLog_measurable M z)).aestronglyMeasurable,
    lt_of_le_of_lt (lintegral_log_sub_truncLog_le hM z) ENNReal.ofReal_lt_top⟩

/-- **The potential is finite at every point**: `w ↦ log|z-w|` is `μ`-integrable. -/
theorem integrable_log (z : ℂ) : Integrable (fun w => Real.log ‖z - w‖) potentialMeasure := by
  have h := (integrable_log_sub_truncLog le_rfl z).add (integrable_truncLog le_rfl z)
  exact h.congr (Eventually.of_forall fun w => by simp)

/-! ### The potentials -/

/-- The logarithmic potential `U(z) = ∫ log|z-w| dμ(w)` of the actual measure. -/
def potentialU (z : ℂ) : ℝ := ∫ w, Real.log ‖z - w‖ ∂potentialMeasure

/-- The truncated potentials `U_M(z) = ∫ max(log|z-w|, -M) dμ(w)`. -/
def potentialUM (M : ℝ) (z : ℂ) : ℝ := ∫ w, truncLog M z w ∂potentialMeasure

/-- The truncation error is bounded uniformly in the centre. -/
theorem abs_potentialU_sub_le {M : ℝ} (hM : 0 ≤ M) (z : ℂ) :
    |potentialU z - potentialUM M z| ≤ tailBound M := by
  rw [potentialU, potentialUM, ← integral_sub (integrable_log z) (integrable_truncLog hM z)]
  have hmeas : AEStronglyMeasurable (fun w => Real.log ‖z - w‖ - truncLog M z w)
      potentialMeasure :=
    ((measurable_log_dist z).sub (truncLog_measurable M z)).aestronglyMeasurable
  calc |∫ w, (Real.log ‖z - w‖ - truncLog M z w) ∂potentialMeasure|
      = ‖∫ w, (Real.log ‖z - w‖ - truncLog M z w) ∂potentialMeasure‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ w, ‖Real.log ‖z - w‖ - truncLog M z w‖ ∂potentialMeasure :=
        norm_integral_le_integral_norm _
    _ = (∫⁻ w, ‖Real.log ‖z - w‖ - truncLog M z w‖ₑ ∂potentialMeasure).toReal :=
        integral_norm_eq_lintegral_enorm hmeas
    _ ≤ tailBound M :=
        ENNReal.toReal_le_of_le_ofReal (tailBound_nonneg hM) (lintegral_log_sub_truncLog_le hM z)

/-- Each truncated potential is continuous. -/
theorem potentialUM_continuous {M : ℝ} (hM : 0 ≤ M) : Continuous (potentialUM M) := by
  rw [continuous_iff_continuousAt]
  intro z₀
  refine continuousAt_of_dominated (bound := fun _ => M + (‖z₀‖ + 1) + supR) ?_ ?_
    (integrable_const _) ?_
  · exact Eventually.of_forall fun z => (truncLog_measurable M z).aestronglyMeasurable
  · filter_upwards [Metric.ball_mem_nhds z₀ one_pos] with z hz
    filter_upwards [ae_norm_le_supR] with w hw
    have hz' : ‖z‖ ≤ ‖z₀‖ + 1 := by
      have h := norm_le_norm_add_norm_sub' z z₀
      rw [Metric.mem_ball, dist_eq_norm] at hz
      linarith
    rw [Real.norm_eq_abs]
    calc |truncLog M z w| ≤ M + ‖z - w‖ := abs_truncLog_le hM z w
      _ ≤ M + (‖z‖ + ‖w‖) := by gcongr; exact norm_sub_le _ _
      _ ≤ M + (‖z₀‖ + 1) + supR := by linarith
  · exact Eventually.of_forall fun w =>
      ((truncLog_continuous M).comp (continuous_id.prodMk continuous_const)).continuousAt

/-- **Uniform convergence** `U_M → U`. -/
theorem potentialUM_tendstoUniformly : TendstoUniformly potentialUM potentialU atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  filter_upwards [tailBound_tendsto.eventually (gt_mem_nhds hε), eventually_ge_atTop 0]
    with M hMε hM0 z
  rw [Real.dist_eq]
  exact lt_of_le_of_lt (abs_potentialU_sub_le hM0 z) hMε

/-- **The potential `U` is continuous.** -/
theorem potentialU_continuous : Continuous potentialU :=
  potentialUM_tendstoUniformly.continuous
    ((eventually_ge_atTop 0).mono fun _ hM => potentialUM_continuous hM).frequently

theorem abs_potentialUM_le {M : ℝ} (hM : 0 ≤ M) (z : ℂ) :
    |potentialUM M z| ≤ M + ‖z‖ + supR := by
  rw [potentialUM, ← Real.norm_eq_abs]
  have h := norm_integral_le_of_norm_le_const (μ := potentialMeasure) (C := M + ‖z‖ + supR)
    (f := truncLog M z) (by
      filter_upwards [ae_norm_le_supR] with w hw
      rw [Real.norm_eq_abs]
      calc |truncLog M z w| ≤ M + ‖z - w‖ := abs_truncLog_le hM z w
        _ ≤ M + (‖z‖ + ‖w‖) := by gcongr; exact norm_sub_le _ _
        _ ≤ M + ‖z‖ + supR := by linarith)
  simpa [probReal_univ] using h

/-- **The potential is bounded**: `|U(z)| ≤ |z| + R + tailBound 0`. -/
theorem abs_potentialU_le (z : ℂ) : |potentialU z| ≤ ‖z‖ + supR + tailBound 0 := by
  have h1 := abs_potentialU_sub_le le_rfl z
  have h2 := abs_potentialUM_le le_rfl z
  have h3 : |potentialU z| ≤ |potentialU z - potentialUM 0 z| + |potentialUM 0 z| := by
    have := abs_add_le (potentialU z - potentialUM 0 z) (potentialUM 0 z)
    simpa using this
  linarith

theorem potentialU_bounded_on_support : ∀ z ∈ supportSet, |potentialU z| ≤ 2 * supR + tailBound 0 :=
  fun z hz => by linarith [abs_potentialU_le z, norm_le_supR hz]

/-! ### Finite logarithmic energy -/

/-- The logarithmic energy `I = ∫ U dμ`. -/
def energyI : ℝ := ∫ z, potentialU z ∂potentialMeasure

theorem integrable_potentialU : Integrable potentialU potentialMeasure := by
  refine Integrable.of_bound potentialU_continuous.aestronglyMeasurable (2 * supR + tailBound 0) ?_
  filter_upwards [ae_mem_supportSet] with z hz
  rw [Real.norm_eq_abs]
  exact potentialU_bounded_on_support z hz

theorem measurable_log_prod : Measurable fun p : ℂ × ℂ => Real.log ‖p.1 - p.2‖ :=
  (measurable_fst.sub measurable_snd).norm.log

/-- The absolute kernel integral is bounded: `∫ |log|z-w|| dμ(w) ≤ |z| + R + tailBound 0`. -/
theorem integral_abs_log_le (z : ℂ) :
    ∫ w, ‖Real.log ‖z - w‖‖ ∂potentialMeasure ≤ ‖z‖ + supR + tailBound 0 := by
  have hA := integrable_truncLog le_rfl z
  have hB := integrable_log_sub_truncLog le_rfl z
  have hpt : ∀ w, ‖Real.log ‖z - w‖‖ ≤
      ‖truncLog 0 z w‖ + ‖Real.log ‖z - w‖ - truncLog 0 z w‖ := fun w => by
    have := norm_add_le (truncLog 0 z w) (Real.log ‖z - w‖ - truncLog 0 z w)
    simpa using this
  have hmeas : AEStronglyMeasurable (fun w => Real.log ‖z - w‖ - truncLog 0 z w)
      potentialMeasure :=
    ((measurable_log_dist z).sub (truncLog_measurable 0 z)).aestronglyMeasurable
  calc ∫ w, ‖Real.log ‖z - w‖‖ ∂potentialMeasure
      ≤ ∫ w, (‖truncLog 0 z w‖ + ‖Real.log ‖z - w‖ - truncLog 0 z w‖) ∂potentialMeasure :=
        integral_mono (integrable_log z).norm (hA.norm.add hB.norm) hpt
    _ = ∫ w, ‖truncLog 0 z w‖ ∂potentialMeasure +
          ∫ w, ‖Real.log ‖z - w‖ - truncLog 0 z w‖ ∂potentialMeasure :=
        integral_add hA.norm hB.norm
    _ ≤ (0 + ‖z‖ + supR) + tailBound 0 := by
        gcongr
        · have h := norm_integral_le_of_norm_le_const (μ := potentialMeasure)
            (C := 0 + ‖z‖ + supR) (f := fun w => ‖truncLog 0 z w‖) (by
              filter_upwards [ae_norm_le_supR] with w hw
              rw [norm_norm, Real.norm_eq_abs]
              calc |truncLog 0 z w| ≤ 0 + ‖z - w‖ := abs_truncLog_le le_rfl z w
                _ ≤ 0 + (‖z‖ + ‖w‖) := by gcongr; exact norm_sub_le _ _
                _ ≤ 0 + ‖z‖ + supR := by linarith)
          have hnn : 0 ≤ ∫ w, ‖truncLog 0 z w‖ ∂potentialMeasure :=
            integral_nonneg fun _ => norm_nonneg _
          have h' : ‖∫ w, ‖truncLog 0 z w‖ ∂potentialMeasure‖ ≤ 0 + ‖z‖ + supR := by
            simpa [probReal_univ] using h
          rwa [Real.norm_eq_abs, abs_of_nonneg hnn] at h'
        · rw [integral_norm_eq_lintegral_enorm hmeas]
          exact ENNReal.toReal_le_of_le_ofReal (tailBound_nonneg le_rfl)
            (lintegral_log_sub_truncLog_le le_rfl z)
    _ = ‖z‖ + supR + tailBound 0 := by ring

/-- **The logarithmic kernel is integrable on `μ × μ`.** -/
theorem integrable_log_prod :
    Integrable (fun p : ℂ × ℂ => Real.log ‖p.1 - p.2‖)
      (potentialMeasure.prod potentialMeasure) := by
  have hmeas := measurable_log_prod.aestronglyMeasurable
    (μ := potentialMeasure.prod potentialMeasure)
  rw [integrable_prod_iff hmeas]
  refine ⟨Eventually.of_forall fun z => integrable_log z, ?_⟩
  refine Integrable.of_bound hmeas.norm.integral_prod_right' (2 * supR + tailBound 0) ?_
  filter_upwards [ae_mem_supportSet] with z hz
  have hnn : 0 ≤ ∫ w, ‖Real.log ‖z - w‖‖ ∂potentialMeasure :=
    integral_nonneg fun _ => norm_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  have h := integral_abs_log_le z
  linarith [norm_le_supR hz]

/-- **Finite logarithmic energy**, and agreement of the product integral with both iterated
integrals: `I = ∬ log|z-w| d(μ×μ) = ∫∫ log|z-w| dμ(w) dμ(z) = ∫∫ log|z-w| dμ(z) dμ(w)`. -/
theorem energyI_eq_prod :
    energyI = ∫ p, Real.log ‖p.1 - p.2‖ ∂(potentialMeasure.prod potentialMeasure) := by
  rw [energyI, integral_prod _ integrable_log_prod]
  rfl

theorem energyI_eq_iterated_symm :
    energyI = ∫ w, ∫ z, Real.log ‖z - w‖ ∂potentialMeasure ∂potentialMeasure := by
  rw [energyI_eq_prod, integral_prod_symm _ integrable_log_prod]

theorem abs_energyI_le : |energyI| ≤ 2 * supR + tailBound 0 := by
  rw [energyI, ← Real.norm_eq_abs]
  have h := norm_integral_le_of_norm_le_const (μ := potentialMeasure)
    (C := 2 * supR + tailBound 0) (f := potentialU) (by
      filter_upwards [ae_mem_supportSet] with z hz
      rw [Real.norm_eq_abs]
      exact potentialU_bounded_on_support z hz)
  simpa [probReal_univ] using h

end Zeta7Arch

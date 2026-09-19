import Zeta7Proof.ArchCircleMeasure

/-! C1, step 5: the uniform logarithmic tail bound.

With `C, α` from the small-ball estimate (38) for the actual measure `μ`, for every `M ≥ 0` and
every centre `z`,

`∫_{|z-w| < e^{-M}} -log|z-w| dμ(w) ≤ C e^{-αM} (M + (1 - e^{-α})⁻¹) =: tailBound M`,

and `tailBound M → 0`. The proof is a dyadic decomposition, done pointwise: on the ball
`B_0 = B(z, e^{-M})`, for `w ≠ z`,

`-log|z-w| ≤ M + #{n ≥ 0 : |z-w| < e^{-M-n}} = M·1_{B_0}(w) + Σ_n 1_{B(z, e^{-M-n})}(w)`,

(the count is `⌈-log|z-w| - M⌉`), and integrating term by term (monotone convergence for the
nonnegative series) gives `M μ(B_0) + Σ_n μ(B(z,e^{-M-n})) ≤ tailBound M` by (38) and the
geometric series. At `w = z` the left side is `-log 0 = 0` by Lean's convention; nothing about
`log 0` is used elsewhere, and `μ` has no atoms. -/
noncomputable section
set_option autoImplicit false
namespace Zeta7Arch
open MeasureTheory Set Real Filter Topology

/-! ### Fixed small-ball constants -/

/-- The constant `C` of (38). -/
def ballC : ℝ := potentialMeasure_small_ball.choose

theorem ballC_nonneg : 0 ≤ ballC := potentialMeasure_small_ball.choose_spec.1

/-- The exponent `α` of (38). -/
def ballα : ℝ := potentialMeasure_small_ball.choose_spec.2.choose

theorem ballα_pos : 0 < ballα := potentialMeasure_small_ball.choose_spec.2.choose_spec.1

theorem ball_bound (z : ℂ) {ρ : ℝ} (h0 : 0 < ρ) (h1 : ρ ≤ 1) :
    potentialMeasure (Metric.ball z ρ) ≤ ENNReal.ofReal (ballC * ρ ^ ballα) :=
  potentialMeasure_small_ball.choose_spec.2.choose_spec.2 z ρ h0 h1

theorem ball_bound_exp (z : ℂ) {t : ℝ} (ht : 0 ≤ t) :
    potentialMeasure (Metric.ball z (exp (-t))) ≤ ENNReal.ofReal (ballC * exp (-(ballα * t))) := by
  have h := ball_bound z (exp_pos (-t)) (exp_le_one_iff.mpr (by linarith))
  rwa [← Real.exp_mul, show -t * ballα = -(ballα * t) by ring] at h

/-! ### The tail bound -/

/-- `tailBound M = C e^{-αM} (M + (1 - e^{-α})⁻¹)`. -/
def tailBound (M : ℝ) : ℝ := ballC * exp (-(ballα * M)) * (M + (1 - exp (-ballα))⁻¹)

theorem exp_neg_ballα_lt_one : exp (-ballα) < 1 := by
  rw [exp_lt_one_iff]; linarith [ballα_pos]

theorem tailBound_nonneg {M : ℝ} (hM : 0 ≤ M) : 0 ≤ tailBound M := by
  have h := exp_neg_ballα_lt_one
  have : 0 < (1 - exp (-ballα))⁻¹ := inv_pos.mpr (by linarith)
  unfold tailBound
  have := ballC_nonneg
  positivity

/-- Pointwise dyadic domination of the logarithmic singularity. -/
theorem tail_pointwise (z w : ℂ) {M : ℝ} (hM : 0 ≤ M) :
    (Metric.ball z (exp (-M))).indicator (fun w => ENNReal.ofReal (-Real.log ‖z - w‖)) w ≤
      (Metric.ball z (exp (-M))).indicator (fun _ => ENNReal.ofReal M) w +
        ∑' n : ℕ, (Metric.ball z (exp (-(M + n)))).indicator (fun _ => (1 : ENNReal)) w := by
  by_cases hw : w ∈ Metric.ball z (exp (-M))
  · rw [indicator_of_mem hw, indicator_of_mem hw]
    rcases eq_or_ne w z with rfl | hne
    · simp
    · set d : ℝ := ‖z - w‖ with hd
      have hd0 : 0 < d := norm_pos_iff.mpr (sub_ne_zero.mpr hne.symm)
      have hdM : d < exp (-M) := by
        rw [Metric.mem_ball, dist_eq_norm, ← norm_neg, neg_sub] at hw; exact hw
      set s : ℝ := -Real.log d - M with hs
      have hlog : Real.log d < -M := by
        rw [← Real.log_exp (-M)]; exact Real.log_lt_log hd0 hdM
      have hs0 : 0 < s := by rw [hs]; linarith
      set N : ℕ := ⌈s⌉₊ with hN
      have hsN : s ≤ N := Nat.le_ceil s
      have hcount : ∀ n ∈ Finset.range N,
          (Metric.ball z (exp (-(M + n)))).indicator (fun _ => (1 : ENNReal)) w = 1 := by
        intro n hn
        have hnN : n < N := Finset.mem_range.mp hn
        have hns : (n : ℝ) < s := Nat.lt_ceil.mp hnN
        apply indicator_of_mem
        rw [Metric.mem_ball, dist_eq_norm, ← norm_neg, neg_sub, ← hd]
        rw [← Real.exp_log hd0]
        exact Real.exp_lt_exp.mpr (by rw [hs] at hns; linarith)
      have hsum : (N : ENNReal) ≤
          ∑' n : ℕ, (Metric.ball z (exp (-(M + n)))).indicator (fun _ => (1 : ENNReal)) w := by
        calc (N : ENNReal) = ∑ n ∈ Finset.range N,
              (Metric.ball z (exp (-(M + n)))).indicator (fun _ => (1 : ENNReal)) w := by
              rw [Finset.sum_congr rfl hcount]; simp
          _ ≤ _ := ENNReal.sum_le_tsum _
      have hsplit : -Real.log ‖z - w‖ = M + s := by rw [hs, ← hd]; ring
      rw [hsplit, ENNReal.ofReal_add hM hs0.le]
      gcongr
      calc ENNReal.ofReal s ≤ ENNReal.ofReal N := ENNReal.ofReal_le_ofReal hsN
        _ = (N : ENNReal) := ENNReal.ofReal_natCast N
        _ ≤ _ := hsum
  · rw [indicator_of_notMem hw]
    exact zero_le

theorem measurable_log_dist (z : ℂ) : Measurable fun w : ℂ => Real.log ‖z - w‖ :=
  (measurable_const.sub measurable_id).norm.log

/-- **Uniform logarithmic tail bound.** -/
theorem tail_lintegral_le (z : ℂ) {M : ℝ} (hM : 0 ≤ M) :
    ∫⁻ w, (Metric.ball z (exp (-M))).indicator
        (fun w => ENNReal.ofReal (-Real.log ‖z - w‖)) w ∂potentialMeasure ≤
      ENNReal.ofReal (tailBound M) := by
  set q : ℝ := exp (-ballα) with hq
  have hq0 : 0 ≤ q := (exp_pos _).le
  have hq1 : q < 1 := exp_neg_ballα_lt_one
  set A : ℝ := ballC * exp (-(ballα * M)) with hA
  have hA0 : 0 ≤ A := mul_nonneg ballC_nonneg (exp_pos _).le
  have hBn : ∀ n : ℕ, potentialMeasure (Metric.ball z (exp (-(M + n)))) ≤
      ENNReal.ofReal A * ENNReal.ofReal q ^ n := by
    intro n
    refine (ball_bound_exp z (by positivity)).trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_pow hq0, ← ENNReal.ofReal_mul hA0, hA, hq, ← Real.exp_nat_mul,
      mul_assoc, ← Real.exp_add]
    congr 3
    ring
  calc ∫⁻ w, (Metric.ball z (exp (-M))).indicator
          (fun w => ENNReal.ofReal (-Real.log ‖z - w‖)) w ∂potentialMeasure
      ≤ ∫⁻ w, ((Metric.ball z (exp (-M))).indicator (fun _ => ENNReal.ofReal M) w +
          ∑' n : ℕ, (Metric.ball z (exp (-(M + n)))).indicator (fun _ => (1 : ENNReal)) w)
          ∂potentialMeasure :=
        lintegral_mono fun w => tail_pointwise z w hM
    _ = ENNReal.ofReal M * potentialMeasure (Metric.ball z (exp (-M))) +
          ∑' n : ℕ, potentialMeasure (Metric.ball z (exp (-(M + n)))) := by
        rw [lintegral_add_left (measurable_const.indicator Metric.isOpen_ball.measurableSet),
          lintegral_indicator_const Metric.isOpen_ball.measurableSet,
          lintegral_tsum (fun n => (measurable_const.indicator
            Metric.isOpen_ball.measurableSet).aemeasurable)]
        congr 1
        refine tsum_congr fun n => ?_
        rw [lintegral_indicator_const Metric.isOpen_ball.measurableSet, one_mul]
    _ ≤ ENNReal.ofReal M * ENNReal.ofReal A + ∑' n : ℕ, ENNReal.ofReal A * ENNReal.ofReal q ^ n := by
        gcongr with n
        · exact ball_bound_exp z hM
        · exact hBn n
    _ = ENNReal.ofReal (tailBound M) := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric,
          ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ hq0,
          ← ENNReal.ofReal_inv_of_pos (by linarith), ← ENNReal.ofReal_mul hM,
          ← ENNReal.ofReal_mul hA0, ← ENNReal.ofReal_add (by positivity)
            (mul_nonneg hA0 (inv_pos.mpr (by linarith)).le)]
        congr 1
        rw [tailBound, ← hA, ← hq]
        ring

/-- `tailBound M → 0`. -/
theorem tailBound_tendsto : Tendsto tailBound atTop (𝓝 0) := by
  have hα := ballα_pos
  set K : ℝ := (1 - exp (-ballα))⁻¹
  -- `e^{-αM} M → 0` and `e^{-αM} → 0`
  have h1 : Tendsto (fun M : ℝ => exp (-(ballα * M))) atTop (𝓝 0) :=
    tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hα)
  have h2 : Tendsto (fun M : ℝ => (ballα * M) ^ 1 * exp (-(ballα * M))) atTop (𝓝 0) :=
    (tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp (tendsto_id.const_mul_atTop hα)
  have h3 : Tendsto (fun M : ℝ => M * exp (-(ballα * M))) atTop (𝓝 0) := by
    have := h2.const_mul ballα⁻¹
    rw [mul_zero] at this
    refine this.congr fun M => ?_
    simp only [pow_one]
    field_simp
  have h4 := (h3.add (h1.const_mul K)).const_mul ballC
  rw [mul_zero, zero_add, mul_zero] at h4
  refine h4.congr fun M => ?_
  simp only [tailBound, K]
  ring

end Zeta7Arch

import Zeta7Proof.ArchModulus
import Zeta7Proof.ArchWeightedGram

/-! C2, step 2: the area submean inequality and the weighted polynomial bound (40).

* `circle_submean`: for an entire `f`, `2π |f(z)|² ≤ ∫_0^{2π} |f(z + s e^{iθ})|² dθ`. With
  `c = f(z)`, `|g|² = |c|² + 2 Re(c̄ (g - c)) + |g - c|²` pointwise and the mean-value property
  `∫ (g - c) = 0` (Mathlib's `DiffContOnCl.circleAverage`).
* `area_submean`: `π h² |f(z)|² ≤ ∫_{B(z,h)} |f|² dA`, integrating the circle bound in polar
  coordinates (`Complex.lintegral_comp_polarCoord_symm`, Tonelli on `(0,∞) × (-π, π)`, and the
  `2π`-periodicity of the circle parametrization).
* `weighted_submean` (40): for `z` in the support, `0 < h ≤ 1` and every polynomial `P` of degree
  `< d`, `|P(z)| ≤ (π h²)^{-1/2} e^{d(U(z) + ω(h))} ‖P‖_d`, with
  `‖P‖_d² = ∫_𝒦 |P|² e^{-2dU} dA`, the Gram norm (39) of `weightedGram d 𝒦 e^{-2dU}`. -/
noncomputable section
set_option autoImplicit false
namespace Zeta7Arch
open MeasureTheory Set Real Filter Topology ComplexConjugate

/-- **Circle submean for `|f|²`.** -/
theorem circle_submean {f : ℂ → ℂ} (hf : Differentiable ℂ f) (z : ℂ) (s : ℝ) :
    2 * π * ‖f z‖ ^ 2 ≤ ∫ θ in (0 : ℝ)..2 * π, ‖f (circleMap z s θ)‖ ^ 2 := by
  set c : ℂ := f z with hc
  set g : ℝ → ℂ := fun θ => f (circleMap z s θ) with hg
  have hgc : Continuous g := hf.continuous.comp (continuous_circleMap z s)
  have hmv : ∫ θ in (0 : ℝ)..2 * π, g θ = ((2 * π : ℝ) : ℂ) * c := by
    have h := (hf.diffContOnCl (s := Metric.ball z |s|)).circleAverage
    rw [circleAverage_def] at h
    have h2 : (2 * π : ℝ) ≠ 0 := by positivity
    have h3 := congrArg (fun w : ℂ => ((2 * π : ℝ) : ℂ) * w) h
    simp only [Complex.real_smul] at h3
    rw [← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ h2, Complex.ofReal_one, one_mul] at h3
    exact h3
  have hI1 : ∫ θ in (0 : ℝ)..2 * π, (g θ - c) = 0 := by
    rw [intervalIntegral.integral_sub (hgc.intervalIntegrable _ _) intervalIntegrable_const, hmv,
      intervalIntegral.integral_const]
    simp [Complex.real_smul]
  have hI2 : ∫ θ in (0 : ℝ)..2 * π, (conj c * (g θ - c)).re = 0 := by
    have hint : IntervalIntegrable (fun θ => conj c * (g θ - c)) volume 0 (2 * π) :=
      (continuous_const.mul (hgc.sub continuous_const)).intervalIntegrable _ _
    have h := Complex.reCLM.intervalIntegral_comp_comm hint
    simp only [Complex.reCLM_apply] at h
    rw [h, intervalIntegral.integral_const_mul, hI1, mul_zero, Complex.zero_re]
  have hpt : ∀ θ, ‖g θ‖ ^ 2 = ‖c‖ ^ 2 + 2 * (conj c * (g θ - c)).re + ‖g θ - c‖ ^ 2 := by
    intro θ
    have h := norm_add_sq_real c (g θ - c)
    rw [add_sub_cancel, Complex.inner] at h
    rw [h, mul_comm (g θ - c)]
  have hre_cont : Continuous fun θ => 2 * (conj c * (g θ - c)).re :=
    continuous_const.mul
      (Complex.continuous_re.comp (continuous_const.mul (hgc.sub continuous_const)))
  have hcont1 : Continuous fun θ => ‖c‖ ^ 2 + 2 * (conj c * (g θ - c)).re :=
    continuous_const.add hre_cont
  have hsplit := intervalIntegral.integral_add (μ := volume) (a := 0) (b := 2 * π)
    (f := fun _ : ℝ => ‖c‖ ^ 2) (g := fun θ => 2 * (conj c * (g θ - c)).re)
    intervalIntegrable_const (hre_cont.intervalIntegrable _ _)
  calc 2 * π * ‖c‖ ^ 2 = ∫ θ in (0 : ℝ)..2 * π, (‖c‖ ^ 2 + 2 * (conj c * (g θ - c)).re) := by
        rw [hsplit, intervalIntegral.integral_const, intervalIntegral.integral_const_mul, hI2]
        simp
    _ ≤ ∫ θ in (0 : ℝ)..2 * π, ‖g θ‖ ^ 2 := by
        have hg2 : Continuous fun θ => ‖g θ‖ ^ 2 := by fun_prop
        apply intervalIntegral.integral_mono_on (by positivity) (hcont1.intervalIntegrable _ _)
          (hg2.intervalIntegrable _ _)
        intro θ _
        rw [hpt θ]
        nlinarith [sq_nonneg ‖g θ - c‖]

/-- The circle integral over `(-π, π)` equals the one over `(0, 2π)`. -/
theorem integral_Ioo_neg_pi_pi {F : ℝ → ℝ} (hper : Function.Periodic F (2 * π)) :
    ∫ θ in Ioo (-π) π, F θ = ∫ θ in (0 : ℝ)..2 * π, F θ := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith [pi_pos])]
  have h := hper.intervalIntegral_add_eq (-π) 0
  rw [show -π + 2 * π = π by ring, zero_add] at h
  exact h

theorem polarCoord_symm_eq (s θ : ℝ) :
    Complex.polarCoord.symm (s, θ) = (s : ℂ) * Complex.exp (θ * Complex.I) := by
  rw [Complex.polarCoord_symm_apply, Complex.exp_mul_I, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin]

theorem measurable_polarCoord_symm : Measurable fun p : ℝ × ℝ => Complex.polarCoord.symm p := by
  have h : (fun p : ℝ × ℝ => Complex.polarCoord.symm p) =
      fun p : ℝ × ℝ => (p.1 : ℂ) * (Real.cos p.2 + Real.sin p.2 * Complex.I) := by
    funext p; exact Complex.polarCoord_symm_apply p
  rw [h]
  fun_prop

/-- The inner (angular) integral in polar coordinates is at least `2π |f(z)|²` times the radius. -/
theorem polar_inner_bound {f : ℂ → ℂ} (hf : Differentiable ℂ f) (z : ℂ) {h s : ℝ}
    (hs : s ∈ Ioi (0 : ℝ)) :
    (Ioc 0 h).indicator (fun s => ENNReal.ofReal (s * (2 * π * ‖f z‖ ^ 2))) s ≤
      ∫⁻ θ in Ioo (-π) π, ENNReal.ofReal s •
        (Metric.closedBall (0 : ℂ) h).indicator (fun v => ENNReal.ofReal (‖f (z + v)‖ ^ 2))
          (Complex.polarCoord.symm (s, θ)) := by
  by_cases hsh : s ∈ Ioc 0 h
  · rw [indicator_of_mem hsh]
    have hs0 : 0 < s := hs
    have hmem : ∀ θ : ℝ, Complex.polarCoord.symm (s, θ) ∈ Metric.closedBall (0 : ℂ) h := by
      intro θ
      rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_polarCoord_symm, abs_of_pos hs0]
      exact hsh.2
    have hcm : ∀ θ : ℝ, z + Complex.polarCoord.symm (s, θ) = circleMap z s θ := by
      intro θ; rw [polarCoord_symm_eq, circleMap]
    have hcont : Continuous fun θ : ℝ => ‖f (circleMap z s θ)‖ ^ 2 :=
      ((hf.continuous.comp (continuous_circleMap z s)).norm).pow 2
    have hper : Function.Periodic (fun θ : ℝ => ‖f (circleMap z s θ)‖ ^ 2) (2 * π) := by
      intro θ; simp only [periodic_circleMap z s θ]
    calc ENNReal.ofReal (s * (2 * π * ‖f z‖ ^ 2))
        ≤ ENNReal.ofReal (s * ∫ θ in Ioo (-π) π, ‖f (circleMap z s θ)‖ ^ 2) := by
          apply ENNReal.ofReal_le_ofReal
          rw [integral_Ioo_neg_pi_pi hper]
          exact mul_le_mul_of_nonneg_left (circle_submean hf z s) hs0.le
      _ = ENNReal.ofReal s * ∫⁻ θ in Ioo (-π) π, ENNReal.ofReal (‖f (circleMap z s θ)‖ ^ 2) := by
          rw [ENNReal.ofReal_mul hs0.le, ofReal_integral_eq_lintegral_ofReal]
          · exact (hcont.integrableOn_Icc (a := -π) (b := π)).mono_set Ioo_subset_Icc_self
          · exact Filter.Eventually.of_forall fun θ => by positivity
      _ = ∫⁻ θ in Ioo (-π) π, ENNReal.ofReal s •
            (Metric.closedBall (0 : ℂ) h).indicator (fun v => ENNReal.ofReal (‖f (z + v)‖ ^ 2))
              (Complex.polarCoord.symm (s, θ)) := by
          rw [← lintegral_const_mul _ (hcont.measurable.ennreal_ofReal)]
          refine lintegral_congr fun θ => ?_
          rw [indicator_of_mem (hmem θ), hcm θ, smul_eq_mul]
  · rw [indicator_of_notMem hsh]
    exact zero_le

/-- **Area submean inequality**: `π h² |f(z)|² ≤ ∫_{B(z,h)} |f|² dA` for entire `f`. -/
theorem area_submean {f : ℂ → ℂ} (hf : Differentiable ℂ f) (z : ℂ) {h : ℝ} (hh : 0 < h) :
    ENNReal.ofReal (π * h ^ 2 * ‖f z‖ ^ 2) ≤
      ∫⁻ w in Metric.closedBall z h, ENNReal.ofReal (‖f w‖ ^ 2) := by
  set G : ℂ → ENNReal :=
    (Metric.closedBall (0 : ℂ) h).indicator (fun v => ENNReal.ofReal (‖f (z + v)‖ ^ 2)) with hG
  have hFm : Measurable fun w => ENNReal.ofReal (‖f w‖ ^ 2) :=
    ((hf.continuous.norm.pow 2).measurable).ennreal_ofReal
  have hGm : Measurable G :=
    (hFm.comp (measurable_const.add measurable_id)).indicator measurableSet_closedBall
  have htrans : ∫⁻ w in Metric.closedBall z h, ENNReal.ofReal (‖f w‖ ^ 2) = ∫⁻ v, G v := by
    rw [← lintegral_indicator measurableSet_closedBall,
      ← lintegral_add_left_eq_self _ z]
    refine lintegral_congr fun v => ?_
    simp only [hG, indicator, Metric.mem_closedBall, dist_self_add_left, dist_zero_right]
  have hHm : Measurable fun p : ℝ × ℝ => ENNReal.ofReal p.1 • G (Complex.polarCoord.symm p) :=
    (measurable_fst.ennreal_ofReal).smul (hGm.comp measurable_polarCoord_symm)
  rw [htrans, ← Complex.lintegral_comp_polarCoord_symm, polarCoord_target,
    Measure.volume_eq_prod, setLIntegral_prod _ hHm.aemeasurable]
  calc ENNReal.ofReal (π * h ^ 2 * ‖f z‖ ^ 2)
      = ∫⁻ s in Ioc 0 h, ENNReal.ofReal (s * (2 * π * ‖f z‖ ^ 2)) := by
        rw [← ofReal_integral_eq_lintegral_ofReal]
        · congr 1
          rw [← intervalIntegral.integral_of_le hh.le, intervalIntegral.integral_mul_const,
            integral_id]
          ring
        · exact (continuous_id.mul continuous_const).integrableOn_Icc.mono_set Ioc_subset_Icc_self
        · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
          exact mul_nonneg hs.1.le (by positivity)
    _ = ∫⁻ s in Ioi 0, (Ioc 0 h).indicator
          (fun s => ENNReal.ofReal (s * (2 * π * ‖f z‖ ^ 2))) s := by
        rw [lintegral_indicator measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc,
          inter_eq_left.mpr Ioc_subset_Ioi_self]
    _ ≤ ∫⁻ s in Ioi 0, ∫⁻ θ in Ioo (-π) π, ENNReal.ofReal s • G (Complex.polarCoord.symm (s, θ)) :=
        setLIntegral_mono' measurableSet_Ioi fun s hs => polar_inner_bound hf z hs

theorem area_submean_real {f : ℂ → ℂ} (hf : Differentiable ℂ f) (z : ℂ) {h : ℝ} (hh : 0 < h) :
    π * h ^ 2 * ‖f z‖ ^ 2 ≤ ∫ w in Metric.closedBall z h, ‖f w‖ ^ 2 := by
  have hint : IntegrableOn (fun w => ‖f w‖ ^ 2) (Metric.closedBall z h) :=
    (hf.continuous.norm.pow 2).continuousOn.integrableOn_compact (isCompact_closedBall z h)
  have h1 := area_submean hf z hh
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun _ => by positivity)] at h1
  exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg fun _ => by positivity)).mp h1

/-! ### The weighted polynomial bound (40) -/

/-- The weight `e^{-2dU}` of the norm (39). -/
def gramWeight (d : ℕ) (z : ℂ) : ℝ := exp (-(2 * d) * potentialU z)

theorem gramWeight_continuous (d : ℕ) : Continuous (gramWeight d) :=
  Real.continuous_exp.comp (continuous_const.mul potentialU_continuous)

theorem gramWeight_pos (d : ℕ) (z : ℂ) : 0 < gramWeight d z := exp_pos _

/-- `‖P‖_d² = ∫_𝒦 |P|² e^{-2dU} dA`. -/
def normSqD (d : ℕ) (x : Fin d → ℂ) : ℝ :=
  ∫ w in discK, gramWeight d w * ‖polyEval x w‖ ^ 2

theorem polyEval_differentiable {d : ℕ} (x : Fin d → ℂ) : Differentiable ℂ (polyEval x) := by
  unfold polyEval; fun_prop

theorem polyEval_continuous {d : ℕ} (x : Fin d → ℂ) : Continuous (polyEval x) :=
  (polyEval_differentiable x).continuous

theorem normSqD_nonneg (d : ℕ) (x : Fin d → ℂ) : 0 ≤ normSqD d x :=
  integral_nonneg fun w => mul_nonneg (gramWeight_pos d w).le (by positivity)

/-- `‖P‖_d²` is the Gram quadratic form of the weighted Gram matrix (39). -/
theorem normSqD_eq_gram (d : ℕ) (x : Fin d → ℂ) :
    dotProduct (star x) (Matrix.mulVec (weightedGram d discK (gramWeight d)) x) =
      (normSqD d x : ℂ) :=
  weightedGram_quad isCompact_discK (gramWeight_continuous d).continuousOn x

/-- **Weighted submean bound (40).** For a support point `z`, `0 < h ≤ 1`, and a polynomial of
degree `< d`: `|P(z)| ≤ (π h²)^{-1/2} e^{d(U(z) + ω(h))} ‖P‖_d`. -/
theorem weighted_submean (d : ℕ) {z : ℂ} (hz : z ∈ supportSet) {h : ℝ} (hh : 0 < h)
    (h1 : h ≤ 1) (x : Fin d → ℂ) :
    ‖polyEval x z‖ ≤ (Real.sqrt (π * h ^ 2))⁻¹ * exp (d * (potentialU z + omegaU h)) *
      Real.sqrt (normSqD d x) := by
  set P := polyEval x with hP
  set E : ℝ := exp (2 * d * (potentialU z + omegaU h)) with hE
  have hE0 : 0 ≤ E := (exp_pos _).le
  have hPc : Continuous P := polyEval_continuous x
  have hA := area_submean_real (polyEval_differentiable x) z hh
  have hint1 : IntegrableOn (fun w => ‖P w‖ ^ 2) (Metric.closedBall z h) :=
    (hPc.norm.pow 2).continuousOn.integrableOn_compact (isCompact_closedBall z h)
  have hcont2 : Continuous fun w => gramWeight d w * ‖P w‖ ^ 2 :=
    (gramWeight_continuous d).mul (hPc.norm.pow 2)
  have hint2 : IntegrableOn (fun w => gramWeight d w * ‖P w‖ ^ 2) discK :=
    hcont2.continuousOn.integrableOn_compact isCompact_discK
  have hint3 : IntegrableOn (fun w => E * (gramWeight d w * ‖P w‖ ^ 2)) (Metric.closedBall z h) :=
    (continuous_const.mul hcont2).continuousOn.integrableOn_compact (isCompact_closedBall z h)
  have hB : ∫ w in Metric.closedBall z h, ‖P w‖ ^ 2 ≤ E * normSqD d x := by
    calc ∫ w in Metric.closedBall z h, ‖P w‖ ^ 2
        ≤ ∫ w in Metric.closedBall z h, E * (gramWeight d w * ‖P w‖ ^ 2) := by
          refine setIntegral_mono_on hint1 hint3 measurableSet_closedBall fun w hw => ?_
          have hU := potentialU_le_add_omega hz h1 hw
          have hexp : 1 ≤ E * gramWeight d w := by
            rw [hE, gramWeight, ← Real.exp_add]
            apply Real.one_le_exp
            have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
            nlinarith
          have := sq_nonneg ‖P w‖
          nlinarith
      _ = E * ∫ w in Metric.closedBall z h, gramWeight d w * ‖P w‖ ^ 2 := integral_const_mul _ _
      _ ≤ E * normSqD d x := by
          apply mul_le_mul_of_nonneg_left _ hE0
          refine setIntegral_mono_set hint2 ?_ ?_
          · exact Filter.Eventually.of_forall fun w => mul_nonneg (gramWeight_pos d w).le (by positivity)
          · exact Filter.Eventually.of_forall (closedBall_subset_discK hz h1)
  have hpos : 0 < π * h ^ 2 := by positivity
  have hN0 := normSqD_nonneg d x
  have hsq : ‖P z‖ ^ 2 ≤
      ((Real.sqrt (π * h ^ 2))⁻¹ * exp (d * (potentialU z + omegaU h)) *
        Real.sqrt (normSqD d x)) ^ 2 := by
    rw [mul_pow, mul_pow, inv_pow, Real.sq_sqrt hpos.le, Real.sq_sqrt hN0,
      ← Real.exp_nat_mul]
    have hEeq : exp ((2 : ℕ) * (d * (potentialU z + omegaU h))) = E := by
      rw [hE]; congr 1; push_cast; ring
    rw [hEeq]
    rw [inv_mul_eq_div, div_mul_eq_mul_div, le_div_iff₀ hpos]
    nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq

end Zeta7Arch

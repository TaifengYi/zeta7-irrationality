import Mathlib

/-! C3, step 5: a regularized logarithm.

For `b > 0` and `t > 0` put `Φ_t(a) = ∫_a^b (1 - e^{-v/t})/v dv`. Then

* `regPhi_le_log`: `Φ_t(a) ≤ log b - log a` for `0 < a ≤ b`, so the regularized logarithm
  `L_t(x) = log √b - Φ_t(|x|²)/2` dominates `log |x|` for `0 < |x| ≤ √b`;
* `log_sub_regPhi_le`: `log b - log a - Φ_t(a) ≤ t/a`, the regularization error;
* `regPhi_nonneg`, `regPhi_le`: `0 ≤ Φ_t(a) ≤ (b - a)/t` for `0 ≤ a ≤ b`;
* `regPhi_gauss_mix` (Gaussian mixture): for `0 ≤ a, b`,
  `Φ_t(a) = ∫_0^1 (e^{-(u/t)a} - e^{-(u/t)b})/u du`, by one application of Fubini on
  `[0,1] × [a,b]`. With `a = |x-y|²` this exhibits `Φ_t(|x-y|²)` as a positive mixture of
  Gaussian kernels minus constants, the structure used for the energy inequality. -/
noncomputable section
set_option autoImplicit false
namespace Zeta7Arch
open MeasureTheory Set Real intervalIntegral

/-- `Φ_t(a) = ∫_a^b (1 - e^{-v/t})/v dv`. -/
def regPhi (b t a : ℝ) : ℝ := ∫ v in a..b, (1 - exp (-v / t)) / v

theorem regIntegrand_nonneg {t v : ℝ} (ht : 0 < t) (hv : 0 < v) :
    0 ≤ (1 - exp (-v / t)) / v := by
  apply div_nonneg _ hv.le
  have : exp (-v / t) ≤ 1 := exp_le_one_iff.mpr (by rw [neg_div]; linarith [div_pos hv ht])
  linarith

theorem regIntegrand_le_inv {t v : ℝ} (_ht : 0 < t) (hv : 0 < v) :
    (1 - exp (-v / t)) / v ≤ v⁻¹ := by
  rw [div_le_iff₀ hv, inv_mul_cancel₀ hv.ne']
  have := exp_pos (-v / t)
  linarith

theorem regIntegrand_le_const {t v : ℝ} (ht : 0 < t) (hv : 0 < v) :
    (1 - exp (-v / t)) / v ≤ t⁻¹ := by
  rw [div_le_iff₀ hv]
  have h := Real.add_one_le_exp (-v / t)
  have : t⁻¹ * v = v / t := by field_simp
  rw [this]
  rw [neg_div] at h ⊢
  linarith

theorem regIntegrand_continuousOn {t : ℝ} :
    ContinuousOn (fun v : ℝ => (1 - exp (-v / t)) / v) (Ioi 0) :=
  ContinuousOn.div (by fun_prop) continuousOn_id fun v hv => (ne_of_gt hv)

/-- The integrand is bounded by `1/t` on `[0, ∞)` (with Lean's value `0` at `v = 0`). -/
theorem regIntegrand_abs_le {t v : ℝ} (ht : 0 < t) (hv : 0 ≤ v) :
    |(1 - exp (-v / t)) / v| ≤ t⁻¹ := by
  rcases hv.eq_or_lt with rfl | hv
  · simp; positivity
  · rw [abs_of_nonneg (regIntegrand_nonneg ht hv)]
    exact regIntegrand_le_const ht hv

theorem regIntegrand_intervalIntegrable {t a b : ℝ} (_ht : 0 < t) (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (fun v : ℝ => (1 - exp (-v / t)) / v) volume a b := by
  apply ContinuousOn.intervalIntegrable
  apply regIntegrand_continuousOn.mono
  intro v hv
  rcases le_total a b with h | h
  · rw [uIcc_of_le h] at hv; exact lt_of_lt_of_le ha hv.1
  · rw [uIcc_of_ge h] at hv; exact lt_of_lt_of_le hb hv.1

/-- **Comparison with the logarithm.** -/
theorem regPhi_le_log {b t a : ℝ} (ht : 0 < t) (ha : 0 < a) (hab : a ≤ b) :
    regPhi b t a ≤ Real.log b - Real.log a := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  rw [← Real.log_div hb.ne' ha.ne', ← integral_inv_of_pos ha hb, regPhi]
  apply integral_mono_on hab (regIntegrand_intervalIntegrable ht ha hb)
    (intervalIntegrable_inv (fun v hv => by
      rw [uIcc_of_le hab] at hv; exact (lt_of_lt_of_le ha hv.1).ne') continuousOn_id)
  intro v hv
  exact regIntegrand_le_inv ht (lt_of_lt_of_le ha hv.1)

theorem regPhi_nonneg {b t a : ℝ} (ht : 0 < t) (ha : 0 ≤ a) (hab : a ≤ b) :
    0 ≤ regPhi b t a := by
  apply integral_nonneg hab
  intro v hv
  rcases (ha.trans hv.1).eq_or_lt with h | h
  · rw [← h]; simp
  · exact regIntegrand_nonneg ht h

/-! ### Local integrability and continuity -/

theorem regIntegrand_abs_le_exp {t : ℝ} (ht : 0 < t) (v : ℝ) :
    |(1 - exp (-v / t)) / v| ≤ exp (|v| / t) / t := by
  rcases lt_trichotomy v 0 with hv | rfl | hv
  · have hw : 0 < -v := neg_pos.mpr hv
    rw [abs_of_neg hv]
    have he := exp_pos (-v / t)
    have hkey : exp (-v / t) - 1 ≤ (-v / t) * exp (-v / t) := by
      have h := Real.add_one_le_exp (-(-v / t))
      have : exp (-(-v / t)) * exp (-v / t) = 1 := by rw [← exp_add]; simp
      nlinarith
    have hge : 1 ≤ exp (-v / t) := Real.one_le_exp (div_nonneg hw.le ht.le)
    rw [show (1 - exp (-v / t)) / v = (exp (-v / t) - 1) / (-v) by
      rw [div_neg, ← neg_div, neg_sub]]
    rw [abs_of_nonneg (div_nonneg (by linarith) hw.le), div_le_div_iff₀ hw ht]
    have : (-v / t) * exp (-v / t) * t = -v * exp (-v / t) := by field_simp
    nlinarith
  · simp; positivity
  · rw [abs_of_pos hv]
    refine (regIntegrand_abs_le ht hv.le).trans ?_
    rw [inv_eq_one_div]
    exact div_le_div_of_nonneg_right (Real.one_le_exp (div_nonneg hv.le ht.le)) ht.le

theorem regIntegrand_measurable (t : ℝ) :
    Measurable fun v : ℝ => (1 - exp (-v / t)) / v := by
  fun_prop

theorem regIntegrand_intervalIntegrable' {t : ℝ} (ht : 0 < t) (a b : ℝ) :
    IntervalIntegrable (fun v : ℝ => (1 - exp (-v / t)) / v) volume a b := by
  rw [intervalIntegrable_iff]
  refine Measure.integrableOn_of_bounded (M := exp ((|a| + |b|) / t) / t)
    (by rw [Real.volume_uIoc]; exact ENNReal.ofReal_ne_top)
    (regIntegrand_measurable t).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with v hv
  rw [Real.norm_eq_abs]
  refine (regIntegrand_abs_le_exp ht v).trans ?_
  apply div_le_div_of_nonneg_right _ ht.le
  apply exp_le_exp.mpr
  apply div_le_div_of_nonneg_right _ ht.le
  have hv' : v ∈ uIcc a b := uIoc_subset_uIcc hv
  rw [mem_uIcc] at hv'
  rw [abs_le]
  rcases hv' with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> constructor <;>
    linarith [le_abs_self a, neg_abs_le a, le_abs_self b, neg_abs_le b]

/-- `Φ_t` is continuous. -/
theorem regPhi_continuous {t : ℝ} (ht : 0 < t) (b : ℝ) : Continuous (regPhi b t) := by
  have h : regPhi b t = fun a => -∫ v in b..a, (1 - exp (-v / t)) / v := by
    funext a; rw [regPhi, integral_symm]
  rw [h]
  exact (continuous_primitive (regIntegrand_intervalIntegrable' ht) b).neg

theorem regPhi_le {b t a : ℝ} (ht : 0 < t) (ha : 0 ≤ a) (hab : a ≤ b) :
    regPhi b t a ≤ (b - a) / t := by
  have h := integral_mono_on hab (regIntegrand_intervalIntegrable' ht a b)
    (intervalIntegrable_const (c := t⁻¹)) fun v hv =>
      (le_abs_self _).trans (regIntegrand_abs_le ht (ha.trans hv.1))
  rw [intervalIntegral.integral_const, smul_eq_mul] at h
  rw [regPhi, div_eq_mul_inv]
  exact h

/-! ### The regularization error -/

theorem exp_neg_le_div {t v : ℝ} (ht : 0 < t) (hv : 0 < v) : exp (-v / t) ≤ t / v := by
  have h := Real.add_one_le_exp (v / t)
  have hpos : 0 < exp (v / t) := exp_pos _
  have hvt : v / t * t = v := by field_simp
  rw [neg_div, Real.exp_neg, inv_le_iff_one_le_mul₀' hpos, mul_div_assoc', le_div_iff₀ hv]
  nlinarith [mul_le_mul_of_nonneg_right h ht.le]

/-- **The regularization error**: `log b - log a - Φ_t(a) ≤ t/a` for `0 < a ≤ b`. -/
theorem log_sub_regPhi_le {b t a : ℝ} (ht : 0 < t) (ha : 0 < a) (hab : a ≤ b) :
    Real.log b - Real.log a - regPhi b t a ≤ t / a := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hinv : IntervalIntegrable (fun v : ℝ => v⁻¹) volume a b :=
    intervalIntegrable_inv (fun v hv => by
      rw [uIcc_of_le hab] at hv; exact (lt_of_lt_of_le ha hv.1).ne') continuousOn_id
  have hsq : ∀ v ∈ uIcc a b, HasDerivAt (fun v : ℝ => -t * v⁻¹) (t * (v ^ 2)⁻¹) v := by
    intro v hv
    rw [uIcc_of_le hab] at hv
    have hv0 : v ≠ 0 := (lt_of_lt_of_le ha hv.1).ne'
    have := (hasDerivAt_inv hv0).const_mul (-t)
    exact this.congr_deriv (by ring)
  have hsqint : IntervalIntegrable (fun v : ℝ => t * (v ^ 2)⁻¹) volume a b := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.inv₀ (continuousOn_pow 2)
    intro v hv
    rw [uIcc_of_le hab] at hv
    exact pow_ne_zero 2 (lt_of_lt_of_le ha hv.1).ne'
  have hFTC := integral_eq_sub_of_hasDerivAt hsq hsqint
  have hlog : Real.log b - Real.log a = ∫ v in a..b, v⁻¹ := by
    rw [integral_inv_of_pos ha hb, Real.log_div hb.ne' ha.ne']
  rw [hlog, regPhi, ← integral_sub hinv (regIntegrand_intervalIntegrable' ht a b)]
  calc ∫ v in a..b, (v⁻¹ - (1 - exp (-v / t)) / v)
      ≤ ∫ v in a..b, t * (v ^ 2)⁻¹ := by
        apply integral_mono_on hab (hinv.sub (regIntegrand_intervalIntegrable' ht a b)) hsqint
        intro v hv
        have hv0 : 0 < v := lt_of_lt_of_le ha hv.1
        have he := exp_neg_le_div ht hv0
        have h1 : v⁻¹ - (1 - exp (-v / t)) / v = exp (-v / t) / v := by field_simp; ring
        have h2 : t * (v ^ 2)⁻¹ = (t / v) / v := by field_simp
        rw [h1, h2]
        exact div_le_div_of_nonneg_right he hv0.le
    _ = -t * b⁻¹ - -t * a⁻¹ := hFTC
    _ ≤ t / a := by
        have : 0 ≤ t * b⁻¹ := by positivity
        rw [div_eq_mul_inv]; linarith

/-! ### The Gaussian mixture representation -/

/-- **Gaussian mixture**: `Φ_t(a) = ∫_0^1 (e^{-(u/t)a} - e^{-(u/t)b})/u du` for `0 ≤ a ≤ b`. -/
theorem regPhi_gauss_mix {b t a : ℝ} (ht : 0 < t) (ha : 0 ≤ a) (hab : a ≤ b) :
    regPhi b t a = ∫ u in (0 : ℝ)..1, (exp (-(u / t) * a) - exp (-(u / t) * b)) / u := by
  let F : ℝ → ℝ → ℝ := fun u v => exp (-(u / t) * v) / t
  have h1 : ∀ u ∈ Ioc (0 : ℝ) 1,
      (exp (-(u / t) * a) - exp (-(u / t) * b)) / u = ∫ v in a..b, F u v := by
    intro u hu
    have hu0 : u ≠ 0 := hu.1.ne'
    have hd : ∀ v ∈ uIcc a b,
        HasDerivAt (fun v => -exp (-(u / t) * v) / u) (F u v) v := by
      intro v _
      have h := (((hasDerivAt_id v).const_mul (-(u / t))).exp.neg).div_const u
      exact h.congr_deriv (by simp only [F, id, mul_one]; field_simp)
    rw [integral_eq_sub_of_hasDerivAt hd (by
      apply Continuous.intervalIntegrable; fun_prop)]
    ring
  have h2 : ∀ v ∈ Ioc a b, ∫ u in (0 : ℝ)..1, F u v = (1 - exp (-v / t)) / v := by
    intro v hv
    have hv0 : v ≠ 0 := (lt_of_le_of_lt ha hv.1).ne'
    have hd : ∀ u ∈ uIcc (0 : ℝ) 1,
        HasDerivAt (fun u => -exp (-(u / t) * v) / v) (F u v) u := by
      intro u _
      have h := ((((hasDerivAt_id u).div_const t).neg.mul_const v).exp.neg).div_const v
      exact h.congr_deriv (by simp only [F, id, Pi.neg_apply]; field_simp)
    rw [integral_eq_sub_of_hasDerivAt hd (by
      apply Continuous.intervalIntegrable; fun_prop)]
    have : -(1 / t) * v = -v / t := by ring
    simp only [zero_div, neg_zero, zero_mul, exp_zero, this]
    field_simp
    ring
  have hFc : Continuous (Function.uncurry F) := by
    simp only [F]; fun_prop
  have hFint : Integrable (Function.uncurry F)
      ((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioc a b))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact (hFc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  have hswap := integral_integral_swap hFint
  rw [regPhi, intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le zero_le_one]
  calc ∫ v in Ioc a b, (1 - exp (-v / t)) / v
      = ∫ v in Ioc a b, ∫ u in Ioc (0 : ℝ) 1, F u v := by
        refine setIntegral_congr_fun measurableSet_Ioc fun v hv => ?_
        rw [← h2 v hv, intervalIntegral.integral_of_le zero_le_one]
    _ = ∫ u in Ioc (0 : ℝ) 1, ∫ v in Ioc a b, F u v := hswap.symm
    _ = ∫ u in Ioc (0 : ℝ) 1, (exp (-(u / t) * a) - exp (-(u / t) * b)) / u := by
        refine setIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
        rw [h1 u hu, intervalIntegral.integral_of_le hab]

end Zeta7Arch

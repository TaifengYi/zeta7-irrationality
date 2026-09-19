import Zeta7Proof.ArchRegLog
import Zeta7Proof.ArchGaussPD
import Zeta7Proof.ArchModulus

/-! C3, step 6: the regularized logarithmic kernel and its conditional negative definiteness.

Put `b = (2(R+1))² + 1`, where `𝒦 = closedBall 0 (R+1)` is the fixed disc, so `|z-w|² ≤ b` on `𝒦`.
For `t > 0` the kernel is

`L_t(x) = ½ log b - ½ Φ_t(min(|x|², b))`.

* `log_le_regL`, `regL_sub_log_le`, `regL_sub_log_le'`: `log|x| ≤ L_t(x)`, and
  `L_t(x) - log|x| ≤ min(t/(2|x|²), ½ log b - log|x|)` for `0 < |x|² ≤ b`;
* `truncLog_le_regL`: `max(log|z-w|, -M_t) ≤ L_t(z-w)` on `𝒦` with `M_t = b/(2t)`;
* `regL_cnd` (**conditional negative definiteness**): for probability measures `α, β` carried by
  `𝒦`, `∬ L_t d(α-β) d(α-β) ≤ 0`. The proof writes `Φ_t` as the Gaussian mixture
  `∫_0^1 (e^{-(u/t)a} - e^{-(u/t)b})/u du` (`regPhi_gauss_mix`), swaps the `u`-integral with the
  product measure (Fubini, the integrand being bounded by `b/t`), and applies `gauss_pd` for
  each `u`; the constants cancel because both measures have mass one. -/
noncomputable section
set_option autoImplicit false
namespace Zeta7Arch
open MeasureTheory Set Real Filter

/-- `b = (2(R+1))² + 1`. -/
def regB : ℝ := (2 * (supR + 1)) ^ 2 + 1

theorem one_le_regB : 1 ≤ regB := by
  unfold regB; nlinarith [sq_nonneg (2 * (supR + 1))]

theorem regB_pos : 0 < regB := by linarith [one_le_regB]

theorem log_regB_nonneg : 0 ≤ Real.log regB := Real.log_nonneg one_le_regB

theorem norm_sub_sq_le_regB {z w : ℂ} (hz : z ∈ discK) (hw : w ∈ discK) :
    ‖z - w‖ ^ 2 ≤ regB := by
  rw [discK, Metric.mem_closedBall, dist_zero_right] at hz hw
  have h := norm_sub_le z w
  have h0 : 0 ≤ ‖z - w‖ := norm_nonneg _
  have h1 : ‖z - w‖ ≤ 2 * (supR + 1) := by linarith
  unfold regB
  nlinarith

/-- `min(|x|², b)`. -/
def regA (x : ℂ) : ℝ := min (‖x‖ ^ 2) regB

theorem regA_nonneg (x : ℂ) : 0 ≤ regA x := le_min (by positivity) regB_pos.le

theorem regA_le (x : ℂ) : regA x ≤ regB := min_le_right _ _

theorem regA_continuous : Continuous regA := by unfold regA; fun_prop

theorem regA_of_le {x : ℂ} (h : ‖x‖ ^ 2 ≤ regB) : regA x = ‖x‖ ^ 2 := min_eq_left h

/-- The regularized logarithm `L_t(x) = ½ log b - ½ Φ_t(min(|x|², b))`. -/
def regL (t : ℝ) (x : ℂ) : ℝ := Real.log regB / 2 - regPhi regB t (regA x) / 2

theorem regL_continuous {t : ℝ} (ht : 0 < t) : Continuous (regL t) := by
  unfold regL
  exact continuous_const.sub (((regPhi_continuous ht regB).comp regA_continuous).div_const 2)

theorem regPhi_regA_nonneg {t : ℝ} (ht : 0 < t) (x : ℂ) : 0 ≤ regPhi regB t (regA x) :=
  regPhi_nonneg ht (regA_nonneg x) (regA_le x)

theorem regPhi_regA_le {t : ℝ} (ht : 0 < t) (x : ℂ) : regPhi regB t (regA x) ≤ regB / t :=
  (regPhi_le ht (regA_nonneg x) (regA_le x)).trans
    (div_le_div_of_nonneg_right (by linarith [regA_nonneg x]) ht.le)

theorem abs_regL_le {t : ℝ} (ht : 0 < t) (x : ℂ) :
    |regL t x| ≤ Real.log regB / 2 + regB / (2 * t) := by
  have h1 := regPhi_regA_nonneg ht x
  have h2 := regPhi_regA_le ht x
  have h3 := log_regB_nonneg
  have h4 : regB / (2 * t) = regB / t / 2 := by ring
  unfold regL
  rw [abs_le]
  constructor <;> linarith

theorem neg_le_regL {t : ℝ} (ht : 0 < t) (x : ℂ) : -(regB / (2 * t)) ≤ regL t x := by
  have h2 := regPhi_regA_le ht x
  have h3 := log_regB_nonneg
  have h4 : regB / (2 * t) = regB / t / 2 := by ring
  unfold regL
  linarith

theorem regL_neg (t : ℝ) (x : ℂ) : regL t (-x) = regL t x := by
  simp [regL, regA]

theorem log_norm_sq (x : ℂ) : Real.log (‖x‖ ^ 2) = 2 * Real.log ‖x‖ := by
  rw [Real.log_pow]; push_cast; ring

/-- **Comparison with the logarithm**: `log|x| ≤ L_t(x)` for `0 < |x|² ≤ b`. -/
theorem log_le_regL {t : ℝ} (ht : 0 < t) {x : ℂ} (hx : x ≠ 0) (hb : ‖x‖ ^ 2 ≤ regB) :
    Real.log ‖x‖ ≤ regL t x := by
  have ha : 0 < ‖x‖ ^ 2 := by positivity
  have h := regPhi_le_log ht ha hb
  rw [regL, regA_of_le hb]
  have := log_norm_sq x
  linarith

/-- The regularization error near infinity: `L_t(x) - log|x| ≤ t/(2|x|²)`. -/
theorem regL_sub_log_le {t : ℝ} (ht : 0 < t) {x : ℂ} (hx : x ≠ 0) (hb : ‖x‖ ^ 2 ≤ regB) :
    regL t x - Real.log ‖x‖ ≤ t / (2 * ‖x‖ ^ 2) := by
  have ha : 0 < ‖x‖ ^ 2 := by positivity
  have h := log_sub_regPhi_le ht ha hb
  rw [regL, regA_of_le hb]
  have := log_norm_sq x
  have h4 : t / (2 * ‖x‖ ^ 2) = t / ‖x‖ ^ 2 / 2 := by ring
  linarith

/-- The regularization error near the diagonal: `L_t(x) - log|x| ≤ ½ log b - log|x|`. -/
theorem regL_sub_log_le' {t : ℝ} (ht : 0 < t) (x : ℂ) :
    regL t x - Real.log ‖x‖ ≤ Real.log regB / 2 - Real.log ‖x‖ := by
  have := regPhi_regA_nonneg ht x
  unfold regL
  linarith

/-- The truncation level `M_t = b/(2t)`. -/
def truncM (t : ℝ) : ℝ := regB / (2 * t)

theorem truncM_nonneg {t : ℝ} (ht : 0 < t) : 0 ≤ truncM t := by
  unfold truncM; have := regB_pos; positivity

/-- **The truncated kernel is dominated by `L_t`** on `𝒦`, diagonal included. -/
theorem truncLog_le_regL {t : ℝ} (ht : 0 < t) {z w : ℂ} (hz : z ∈ discK) (hw : w ∈ discK) :
    truncLog (truncM t) z w ≤ regL t (z - w) := by
  unfold truncLog
  rcases le_total ‖z - w‖ (exp (-truncM t)) with h | h
  · rw [max_eq_right h, Real.log_exp]; exact neg_le_regL ht _
  · rw [max_eq_left h]
    exact log_le_regL ht (norm_pos_iff.mp (lt_of_lt_of_le (exp_pos _) h))
      (norm_sub_sq_le_regB hz hw)

/-! ### The Gaussian mixture integrand -/

/-- `G_t(u, x) = (e^{-(u/t) min(|x|²,b)} - e^{-(u/t) b})/u`. -/
def mixG (t u : ℝ) (x : ℂ) : ℝ := (exp (-(u / t) * regA x) - exp (-(u / t) * regB)) / u

theorem exp_sub_exp_bounds {c a b : ℝ} (hc : 0 ≤ c) (ha : 0 ≤ a) (hab : a ≤ b) :
    0 ≤ exp (-c * a) - exp (-c * b) ∧ exp (-c * a) - exp (-c * b) ≤ c * (b - a) := by
  constructor
  · have : exp (-c * b) ≤ exp (-c * a) := exp_le_exp.mpr (by nlinarith)
    linarith
  · have h1 : exp (-c * b) = exp (-c * a) * exp (-(c * (b - a))) := by
      rw [← exp_add]; ring_nf
    have h2 := Real.add_one_le_exp (-(c * (b - a)))
    have h3 : exp (-c * a) ≤ 1 := exp_le_one_iff.mpr (by nlinarith)
    have h4 : 0 < exp (-c * a) := exp_pos _
    have h5 : 0 ≤ c * (b - a) := mul_nonneg hc (by linarith)
    rw [h1]
    nlinarith

theorem abs_mixG_le {t u : ℝ} (ht : 0 < t) (hu : 0 ≤ u) (x : ℂ) : |mixG t u x| ≤ regB / t := by
  rcases hu.eq_or_lt with rfl | hu
  · simp [mixG]; exact div_nonneg regB_pos.le ht.le
  obtain ⟨h0, h1⟩ := exp_sub_exp_bounds (div_nonneg hu.le ht.le) (regA_nonneg x) (regA_le x)
  unfold mixG
  rw [abs_of_nonneg (div_nonneg h0 hu.le), div_le_div_iff₀ hu ht]
  have h2 := regA_nonneg x
  have h3 : u / t * (regB - regA x) * t = u * (regB - regA x) := by field_simp
  nlinarith [mul_le_mul_of_nonneg_right h1 ht.le]

theorem mixG_measurable (t : ℝ) :
    Measurable fun q : (ℂ × ℂ) × ℝ => mixG t q.2 (q.1.1 - q.1.2) := by
  have hA : Measurable fun q : (ℂ × ℂ) × ℝ => regA (q.1.1 - q.1.2) :=
    regA_continuous.measurable.comp (by fun_prop)
  have hs : Measurable fun q : (ℂ × ℂ) × ℝ => q.2 := measurable_snd
  exact ((((hs.div_const t).neg.mul hA).exp.sub
    ((hs.div_const t).neg.mul_const regB).exp).div hs)

/-- `Φ_t(min(|x|²,b)) = ∫_{(0,1]} G_t(u, x) du`. -/
theorem regPhi_regA_mix {t : ℝ} (ht : 0 < t) (x : ℂ) :
    regPhi regB t (regA x) = ∫ u in Ioc (0 : ℝ) 1, mixG t u x := by
  rw [regPhi_gauss_mix ht (regA_nonneg x) (regA_le x),
    intervalIntegral.integral_of_le zero_le_one]
  rfl

/-! ### Kernel pairings through the product measure -/

section Pairing

variable (γ δ : Measure ℂ) [IsProbabilityMeasure γ] [IsProbabilityMeasure δ]

theorem integrable_kernel_prod {k : ℂ → ℝ} (hk : Continuous k) {C : ℝ} (hC : ∀ x, |k x| ≤ C) :
    Integrable (fun p : ℂ × ℂ => k (p.1 - p.2)) (γ.prod δ) :=
  Integrable.of_bound (hk.comp (continuous_fst.sub continuous_snd)).aestronglyMeasurable C
    (Eventually.of_forall fun p => by rw [Real.norm_eq_abs]; exact hC _)

theorem kernelPair_eq_prod {k : ℂ → ℝ} (hk : Continuous k) {C : ℝ} (hC : ∀ x, |k x| ≤ C) :
    kernelPair k γ δ = ∫ p, k (p.1 - p.2) ∂(γ.prod δ) :=
  (integral_prod _ (integrable_kernel_prod γ δ hk hC)).symm

theorem gaussK_continuous (c : ℝ) : Continuous (gaussK c) := by unfold gaussK; fun_prop

theorem abs_gaussK_le {c : ℝ} (hc : 0 ≤ c) (x : ℂ) : |gaussK c x| ≤ 1 := by
  unfold gaussK
  rw [abs_of_pos (exp_pos _)]
  exact exp_le_one_iff.mpr (by nlinarith [sq_nonneg ‖x‖])

theorem integrable_mixG {t : ℝ} (ht : 0 < t) :
    Integrable (Function.uncurry fun (p : ℂ × ℂ) (u : ℝ) => mixG t u (p.1 - p.2))
      ((γ.prod δ).prod (volume.restrict (Ioc (0 : ℝ) 1))) := by
  refine Integrable.of_bound (mixG_measurable t).aestronglyMeasurable (regB / t) ?_
  filter_upwards [(Measure.quasiMeasurePreserving_snd).ae
    (ae_restrict_mem (μ := volume) measurableSet_Ioc)] with q hq
  rw [Real.norm_eq_abs]
  exact abs_mixG_le ht hq.1.le _

/-- `∬ Φ_t = ∫_{(0,1]} ∬ G_t(u, ·)`. -/
theorem prod_regPhi_eq {t : ℝ} (ht : 0 < t) :
    ∫ p, regPhi regB t (regA (p.1 - p.2)) ∂(γ.prod δ) =
      ∫ u in Ioc (0 : ℝ) 1, ∫ p, mixG t u (p.1 - p.2) ∂(γ.prod δ) := by
  rw [← integral_integral_swap (integrable_mixG γ δ ht)]
  exact integral_congr_ae (Eventually.of_forall fun p => regPhi_regA_mix ht _)

variable {γ δ}

/-- For `u > 0`, `∬ G_t(u, ·) = u⁻¹ (∬ e^{-(u/t)|x-y|²} - e^{-(u/t)b})`. -/
theorem prod_mixG_eq {t u : ℝ} (ht : 0 < t) (hu : 0 < u) (hγ : ∀ᵐ x ∂γ, x ∈ discK)
    (hδ : ∀ᵐ x ∂δ, x ∈ discK) :
    ∫ p, mixG t u (p.1 - p.2) ∂(γ.prod δ) =
      u⁻¹ * (kernelPair (gaussK (u / t)) γ δ - exp (-(u / t) * regB)) := by
  have hc : 0 ≤ u / t := (div_pos hu ht).le
  have hae : ∀ᵐ p ∂(γ.prod δ), mixG t u (p.1 - p.2) =
      u⁻¹ * (gaussK (u / t) (p.1 - p.2) - exp (-(u / t) * regB)) := by
    filter_upwards [(Measure.quasiMeasurePreserving_fst).ae hγ,
      (Measure.quasiMeasurePreserving_snd).ae hδ] with p h1 h2
    rw [mixG, regA_of_le (norm_sub_sq_le_regB h1 h2), gaussK, div_eq_inv_mul]
  rw [integral_congr_ae hae, integral_const_mul,
    integral_sub (integrable_kernel_prod γ δ (gaussK_continuous _) (abs_gaussK_le hc))
      (integrable_const _),
    integral_const, probReal_univ, one_smul,
    kernelPair_eq_prod γ δ (gaussK_continuous _) (abs_gaussK_le hc)]

variable (γ δ) in
/-- `B_{L_t}(γ, δ) = ½ log b - ½ ∬ Φ_t`. -/
theorem kernelPair_regL {t : ℝ} (ht : 0 < t) :
    kernelPair (regL t) γ δ =
      Real.log regB / 2 - (∫ p, regPhi regB t (regA (p.1 - p.2)) ∂(γ.prod δ)) / 2 := by
  have hΦ : Integrable (fun p : ℂ × ℂ => regPhi regB t (regA (p.1 - p.2))) (γ.prod δ) :=
    integrable_kernel_prod γ δ (k := fun x => regPhi regB t (regA x))
      ((regPhi_continuous ht regB).comp regA_continuous) (C := regB / t) fun x => by
        rw [abs_of_nonneg (regPhi_regA_nonneg ht x)]; exact regPhi_regA_le ht x
  rw [kernelPair_eq_prod γ δ (regL_continuous ht) (abs_regL_le ht)]
  unfold regL
  rw [integral_sub (integrable_const _) (hΦ.div_const 2), integral_const, probReal_univ,
    one_smul, integral_div]

end Pairing

/-- **Conditional negative definiteness of `L_t`**: for probability measures carried by `𝒦`,
`∬ L_t d(α-β) d(α-β) ≤ 0`. -/
theorem regL_cnd {t : ℝ} (ht : 0 < t) (α β : Measure ℂ) [IsProbabilityMeasure α]
    [IsProbabilityMeasure β] (hα : ∀ᵐ x ∂α, x ∈ discK) (hβ : ∀ᵐ x ∂β, x ∈ discK) :
    kernelDiffEnergy (regL t) α β ≤ 0 := by
  set Q : Measure ℂ → Measure ℂ → ℝ → ℝ := fun γ δ u => ∫ p, mixG t u (p.1 - p.2) ∂(γ.prod δ)
    with hQ
  have hQi : ∀ (γ δ : Measure ℂ) [IsProbabilityMeasure γ] [IsProbabilityMeasure δ],
      Integrable (Q γ δ) (volume.restrict (Ioc (0 : ℝ) 1)) := fun γ δ _ _ =>
    (integrable_mixG γ δ ht).integral_prod_right
  have hsum : kernelDiffEnergy (regL t) α β = -(1 / 2) *
      ∫ u in Ioc (0 : ℝ) 1, (Q α α u - Q α β u - Q β α u + Q β β u) := by
    have h1 : Integrable (fun u => Q α α u - Q α β u) (volume.restrict (Ioc (0 : ℝ) 1)) :=
      (hQi α α).sub (hQi α β)
    have h2 : Integrable (fun u => Q α α u - Q α β u - Q β α u)
        (volume.restrict (Ioc (0 : ℝ) 1)) := h1.sub (hQi β α)
    rw [integral_add h2 (hQi β β), integral_sub h1 (hQi β α), integral_sub (hQi α α) (hQi α β)]
    simp only [kernelDiffEnergy, kernelPair_regL _ _ ht, prod_regPhi_eq _ _ ht, hQ]
    ring
  have hmix : ∫ u in Ioc (0 : ℝ) 1, (Q α α u - Q α β u - Q β α u + Q β β u) =
      ∫ u in Ioc (0 : ℝ) 1, u⁻¹ * kernelDiffEnergy (gaussK (u / t)) α β := by
    refine setIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
    simp only [hQ]
    rw [prod_mixG_eq ht hu.1 hα hα, prod_mixG_eq ht hu.1 hα hβ, prod_mixG_eq ht hu.1 hβ hα,
      prod_mixG_eq ht hu.1 hβ hβ, kernelDiffEnergy]
    ring
  have hpos : 0 ≤ ∫ u in Ioc (0 : ℝ) 1, u⁻¹ * kernelDiffEnergy (gaussK (u / t)) α β :=
    setIntegral_nonneg measurableSet_Ioc fun u hu =>
      mul_nonneg (inv_nonneg.mpr hu.1.le) (gauss_pd (div_pos hu.1 ht) α β)
  rw [hsum, hmix]
  linarith

end Zeta7Arch

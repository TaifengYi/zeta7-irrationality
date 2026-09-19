import Zeta7Proof.ArchRegKernel
import Zeta7Proof.ArchEmpirical

/-! C3, step 7: the energy inequality (43) and the Gram limsup (45).

For `z ∈ 𝒦^n` let `ν_z = n⁻¹ Σ δ_{z_i}` be the empirical measure and `μ` the actual measure of C1.

* `regPot t` is `V_t = L_t * μ` and `regEnergy t` is `I_t = ∫ V_t dμ`.
* `energyI_le_regEnergy`: `I ≤ I_t`, because `log ≤ L_t` off the diagonal and `μ` has no atoms.
* `regPot_sub_le`: `V_t(z) - U(z) ≤ t e^{2K}/2 + ½ log b · C e^{-αK} + T(K)` on `𝒦`, by the
  small-ball estimate (38) and the tail bound `T`.
* `regL_cnd` applied to `ν_z` and `μ` gives the discrete inequality
  `n⁻² Σ_{i,j} L_t(z_i - z_j) - 2 n⁻¹ Σ V_t(z_i) + I_t ≤ 0`.
* `empiricalEnergy_le` (**energy inequality (43)** in diagonal-corrected form): if
  `V_t - U ≤ ε` on `𝒦`, then for every `n > 0` and `z ∈ 𝒦^n`,
  `n⁻² Σ_{i,j} max(log|z_i - z_j|, -M_t) - 2 n⁻¹ Σ U(z_i) ≤ -I + 2ε`.
* `gram_limsup` (**(45)**): for every `ε > 0`, eventually `det G_d ≤ exp((-I + ε) d²)`, that is
  `limsup d⁻² log det G_d ≤ -I`. -/
noncomputable section
set_option autoImplicit false
namespace Zeta7Arch
open MeasureTheory Set Real Filter

/-! ### Empirical measures -/

/-- `ν_z = n⁻¹ Σ_i δ_{z_i}`. -/
def empMeasure {n : ℕ} (z : Fin n → ℂ) : Measure ℂ :=
  ((n : ENNReal)⁻¹) • ∑ i, Measure.dirac (z i)

theorem empMeasure_isProbability {n : ℕ} (hn : 0 < n) (z : Fin n → ℂ) :
    IsProbabilityMeasure (empMeasure z) := by
  constructor
  simp only [empMeasure, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply,
    measure_univ, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
    smul_eq_mul]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast hn.ne') (ENNReal.natCast_ne_top n)

theorem empMeasure_ae_mem {n : ℕ} {z : Fin n → ℂ} (hz : ∀ i, z i ∈ discK) :
    ∀ᵐ x ∂empMeasure z, x ∈ discK := by
  have hK : MeasurableSet discK := isCompact_discK.isClosed.measurableSet
  rw [ae_iff]
  simp only [empMeasure, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply,
    smul_eq_mul]
  rw [Finset.sum_eq_zero fun i _ => ?_, mul_zero]
  rw [show {a | a ∉ discK} = discKᶜ from rfl, Measure.dirac_apply' _ hK.compl]
  simp [hz i]

theorem integral_empMeasure {n : ℕ} (z : Fin n → ℂ) (f : ℂ → ℝ) :
    ∫ x, f x ∂empMeasure z = (n : ℝ)⁻¹ * ∑ i, f (z i) := by
  rw [empMeasure, integral_smul_measure,
    integral_finsetSum_measure fun i _ => integrable_dirac enorm_lt_top]
  simp [integral_dirac]

/-! ### The regularized potential -/

/-- `V_t(z) = ∫ L_t(z - w) dμ(w)`. -/
def regPot (t : ℝ) (z : ℂ) : ℝ := ∫ w, regL t (z - w) ∂potentialMeasure

/-- `I_t = ∫ V_t dμ`. -/
def regEnergy (t : ℝ) : ℝ := ∫ z, regPot t z ∂potentialMeasure

theorem integrable_regL {t : ℝ} (ht : 0 < t) (z : ℂ) (ν : Measure ℂ) [IsFiniteMeasure ν] :
    Integrable (fun w => regL t (z - w)) ν :=
  Integrable.of_bound
    (((regL_continuous ht).comp (continuous_const.sub continuous_id)).aestronglyMeasurable) _ (Eventually.of_forall fun w => by
      rw [Real.norm_eq_abs]; exact abs_regL_le ht _)

theorem abs_regPot_le {t : ℝ} (ht : 0 < t) (z : ℂ) :
    |regPot t z| ≤ Real.log regB / 2 + regB / (2 * t) := by
  rw [regPot, ← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le_const (C := Real.log regB / 2 + regB / (2 * t)) (Eventually.of_forall fun w => ?_)).trans
    (by simp)
  rw [Real.norm_eq_abs]; exact abs_regL_le ht _

theorem regPot_continuous {t : ℝ} (ht : 0 < t) : Continuous (regPot t) :=
  continuous_of_dominated (bound := fun _ => Real.log regB / 2 + regB / (2 * t))
    (fun z => (((regL_continuous ht).comp (continuous_const.sub continuous_id)).aestronglyMeasurable))
    (fun z => Eventually.of_forall fun w => by rw [Real.norm_eq_abs]; exact abs_regL_le ht _)
    (integrable_const _)
    (Eventually.of_forall fun w => (regL_continuous ht).comp (continuous_id.sub continuous_const))

theorem integrable_regPot {t : ℝ} (ht : 0 < t) (ν : Measure ℂ) [IsFiniteMeasure ν] :
    Integrable (regPot t) ν :=
  Integrable.of_bound (regPot_continuous ht).aestronglyMeasurable _
    (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact abs_regPot_le ht z)

/-- `U ≤ V_t` on `𝒦`. -/
theorem potentialU_le_regPot {t : ℝ} (ht : 0 < t) {z : ℂ} (hz : z ∈ discK) :
    potentialU z ≤ regPot t z := by
  refine integral_mono_ae (integrable_log z) (integrable_regL ht z _) ?_
  filter_upwards [ae_ne z, ae_mem_supportSet] with w hw hwK
  exact log_le_regL ht (sub_ne_zero.mpr hw.symm)
    (norm_sub_sq_le_regB hz (supportSet_subset_discK hwK))

/-- **`I ≤ I_t`.** -/
theorem energyI_le_regEnergy {t : ℝ} (ht : 0 < t) : energyI ≤ regEnergy t := by
  refine integral_mono_ae integrable_potentialU (integrable_regPot ht _) ?_
  filter_upwards [ae_mem_supportSet] with z hz
  exact potentialU_le_regPot ht (supportSet_subset_discK hz)

/-! ### The uniform regularization error -/

/-- The error bound `t e^{2K}/2 + ½ log b · C e^{-αK} + T(K)`. -/
def regErr (t K : ℝ) : ℝ :=
  t * exp (2 * K) / 2 + Real.log regB / 2 * (ballC * exp (-(ballα * K))) + tailBound K

theorem measurableSet_ball' (z : ℂ) (r : ℝ) : MeasurableSet (Metric.ball z r) :=
  Metric.isOpen_ball.measurableSet

/-- **Uniform error**: `V_t(z) - U(z) ≤ regErr t K` for `z ∈ 𝒦` and `K ≥ 0`. -/
theorem regPot_sub_le {t K : ℝ} (ht : 0 < t) (hK : 0 ≤ K) {z : ℂ} (hz : z ∈ discK) :
    regPot t z - potentialU z ≤ regErr t K := by
  set B := Metric.ball z (exp (-K)) with hB
  set g : ℂ → ℝ := fun w => -Real.log ‖z - w‖ with hg
  have hBm : MeasurableSet B := measurableSet_ball' z _
  have hgi : Integrable g potentialMeasure := (integrable_log z).neg
  have hpt : ∀ᵐ w ∂potentialMeasure, regL t (z - w) - Real.log ‖z - w‖ ≤
      t * exp (2 * K) / 2 + (B.indicator (fun _ => Real.log regB / 2) w + B.indicator g w) := by
    filter_upwards [ae_ne z, ae_mem_supportSet] with w hw hwK
    have hx : z - w ≠ 0 := sub_ne_zero.mpr hw.symm
    have hb := norm_sub_sq_le_regB hz (supportSet_subset_discK hwK)
    by_cases hwB : w ∈ B
    · rw [indicator_of_mem hwB, indicator_of_mem hwB]
      have h := regL_sub_log_le' ht (z - w)
      have : 0 ≤ t * exp (2 * K) / 2 := by positivity
      simp only [hg]
      linarith
    · rw [indicator_of_notMem hwB, indicator_of_notMem hwB, add_zero, add_zero]
      have hfar : exp (-K) ≤ ‖z - w‖ := by
        rw [hB, Metric.mem_ball, dist_eq_norm, norm_sub_rev] at hwB
        exact not_lt.mp hwB
      refine (regL_sub_log_le ht hx hb).trans ?_
      have hpos : 0 < ‖z - w‖ := lt_of_lt_of_le (exp_pos _) hfar
      have hsq : exp (-(2 * K)) ≤ ‖z - w‖ ^ 2 := by
        rw [show -(2 * K) = -K + -K by ring, exp_add, sq]
        exact mul_le_mul hfar hfar (exp_pos _).le hpos.le
      rw [div_le_div_iff₀ (by positivity) two_pos]
      have he : exp (2 * K) * exp (-(2 * K)) = 1 := by rw [← exp_add]; simp
      nlinarith [mul_le_mul_of_nonneg_left hsq (mul_nonneg ht.le (exp_pos (2 * K)).le)]
  have hi1 : Integrable (fun w => B.indicator (fun _ => Real.log regB / 2) w) potentialMeasure :=
    (integrable_const _).indicator hBm
  have hi2 : Integrable (fun w => B.indicator g w) potentialMeasure := hgi.indicator hBm
  have hi12 : Integrable (fun w => B.indicator (fun _ => Real.log regB / 2) w + B.indicator g w)
      potentialMeasure := hi1.add hi2
  have hL : Integrable (fun w => regL t (z - w) - Real.log ‖z - w‖) potentialMeasure :=
    (integrable_regL ht z _).sub (integrable_log z)
  have hR : Integrable (fun w => t * exp (2 * K) / 2 +
      (B.indicator (fun _ => Real.log regB / 2) w + B.indicator g w)) potentialMeasure :=
    (integrable_const _).add hi12
  have hmono := integral_mono_ae hL hR hpt
  rw [integral_sub (integrable_regL ht z _) (integrable_log z), integral_add (integrable_const _)
    hi12, integral_add hi1 hi2, integral_const, probReal_univ, one_smul,
    integral_indicator_const _ hBm] at hmono
  -- the ball term
  have hball : potentialMeasure.real B ≤ ballC * exp (-(ballα * K)) := by
    rw [Measure.real]
    exact ENNReal.toReal_le_of_le_ofReal (by have := ballC_nonneg; positivity)
      (ball_bound_exp z hK)
  -- the tail term
  have htail : ∫ w, B.indicator g w ∂potentialMeasure ≤ tailBound K := by
    have hnn : 0 ≤ᵐ[potentialMeasure] fun w => B.indicator g w :=
      Eventually.of_forall fun w => by
        show 0 ≤ B.indicator g w
        by_cases hwB : w ∈ B
        · rw [indicator_of_mem hwB]
          simp only [hg, Left.nonneg_neg_iff]
          rw [hB, Metric.mem_ball, dist_eq_norm, norm_sub_rev] at hwB
          exact Real.log_nonpos (norm_nonneg _)
            (hwB.le.trans (exp_le_one_iff.mpr (by linarith)))
        · rw [indicator_of_notMem hwB]
    rw [integral_eq_lintegral_of_nonneg_ae hnn hi2.aestronglyMeasurable]
    refine ENNReal.toReal_le_of_le_ofReal (tailBound_nonneg hK) (le_trans (le_of_eq ?_)
      (tail_lintegral_le z hK))
    refine lintegral_congr fun w => ?_
    by_cases hwB : w ∈ B
    · rw [indicator_of_mem hwB, indicator_of_mem hwB]
    · rw [indicator_of_notMem hwB, indicator_of_notMem hwB, ENNReal.ofReal_zero]
  have hlog := log_regB_nonneg
  have : potentialMeasure.real B • (Real.log regB / 2) ≤
      Real.log regB / 2 * (ballC * exp (-(ballα * K))) := by
    rw [smul_eq_mul, mul_comm]
    exact mul_le_mul_of_nonneg_left hball (by positivity)
  unfold regErr
  rw [regPot, potentialU]
  linarith

theorem regErr_small {ε : ℝ} (hε : 0 < ε) :
    ∃ t > 0, ∀ z ∈ discK, regPot t z - potentialU z ≤ ε := by
  have h1 : Tendsto (fun K : ℝ => Real.log regB / 2 * (ballC * exp (-(ballα * K))) +
      tailBound K) atTop (nhds 0) := by
    have he : Tendsto (fun K : ℝ => exp (-(ballα * K))) atTop (nhds 0) :=
      tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop ballα_pos)
    simpa using ((he.const_mul ballC).const_mul (Real.log regB / 2)).add tailBound_tendsto
  obtain ⟨K, hKε, hK⟩ := ((h1.eventually (gt_mem_nhds (half_pos hε))).and
    (eventually_ge_atTop 0)).exists
  refine ⟨ε * exp (-(2 * K)), by positivity, fun z hz => ?_⟩
  refine (regPot_sub_le (by positivity) hK hz).trans ?_
  unfold regErr
  have : ε * exp (-(2 * K)) * exp (2 * K) = ε := by
    rw [mul_assoc, ← exp_add]; simp
  linarith

/-! ### The energy inequality -/

/-- The discrete form of conditional negative definiteness. -/
theorem discrete_cnd {t : ℝ} (ht : 0 < t) {n : ℕ} (hn : 0 < n) {z : Fin n → ℂ}
    (hz : ∀ i, z i ∈ discK) :
    ((n : ℝ)⁻¹) ^ 2 * ∑ i, ∑ j, regL t (z i - z j) - 2 * ((n : ℝ)⁻¹ * ∑ i, regPot t (z i)) +
      regEnergy t ≤ 0 := by
  have := empMeasure_isProbability hn z
  have h := regL_cnd ht (empMeasure z) potentialMeasure (empMeasure_ae_mem hz)
    (ae_mem_supportSet.mono fun _ hw => supportSet_subset_discK hw)
  have e1 : kernelPair (regL t) (empMeasure z) (empMeasure z) =
      ((n : ℝ)⁻¹) ^ 2 * ∑ i, ∑ j, regL t (z i - z j) := by
    rw [kernelPair, integral_empMeasure]
    simp_rw [integral_empMeasure, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have e2 : kernelPair (regL t) (empMeasure z) potentialMeasure =
      (n : ℝ)⁻¹ * ∑ i, regPot t (z i) := by
    rw [kernelPair, integral_empMeasure]; rfl
  have e3 : kernelPair (regL t) potentialMeasure (empMeasure z) =
      (n : ℝ)⁻¹ * ∑ i, regPot t (z i) := by
    rw [kernelPair]
    simp_rw [integral_empMeasure]
    rw [integral_const_mul, integral_finsetSum _ fun i _ => integrable_regL' ht (z i)]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [regPot]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    show regL t (x - z i) = regL t (z i - x)
    rw [← regL_neg, neg_sub]
  have e4 : kernelPair (regL t) potentialMeasure potentialMeasure = regEnergy t := rfl
  rw [kernelDiffEnergy, e1, e2, e3, e4] at h
  linarith
where
  integrable_regL' {t : ℝ} (ht : 0 < t) (y : ℂ) :
      Integrable (fun x => regL t (x - y)) potentialMeasure :=
    Integrable.of_bound
      (((regL_continuous ht).comp (continuous_id.sub continuous_const)).aestronglyMeasurable) _ (Eventually.of_forall fun w => by
        rw [Real.norm_eq_abs]; exact abs_regL_le ht _)

/-- **The energy inequality (43)**, in diagonal-corrected form, uniformly on `𝒦^n`. -/
theorem empiricalEnergy_le {t ε : ℝ} (ht : 0 < t) (hε : ∀ z ∈ discK, regPot t z - potentialU z ≤ ε)
    {n : ℕ} (hn : 0 < n) {z : Fin n → ℂ} (hz : ∀ i, z i ∈ discK) :
    empiricalEnergy (truncM t) z ≤ -energyI + 2 * ε := by
  have hcnd := discrete_cnd ht hn hz
  have hI := energyI_le_regEnergy ht
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hinv : 0 < (n : ℝ)⁻¹ := inv_pos.mpr hn'
  have h1 : ∑ i, ∑ j, truncLog (truncM t) (z i) (z j) ≤ ∑ i, ∑ j, regL t (z i - z j) :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => truncLog_le_regL ht (hz i) (hz j)
  have h2 : ∑ i, regPot t (z i) ≤ ∑ i, potentialU (z i) + n * ε := by
    have := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) =>
      (show regPot t (z i) ≤ potentialU (z i) + ε by linarith [hε (z i) (hz i)])
    rwa [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] at this
  have h3 : (n : ℝ)⁻¹ * (n * ε) = ε := by field_simp
  have h4 := mul_le_mul_of_nonneg_left h1 (pow_nonneg hinv.le 2)
  have h5 := mul_le_mul_of_nonneg_left h2 hinv.le
  rw [mul_add, h3] at h5
  unfold empiricalEnergy
  linarith

/-! ### The Gram limsup (45) -/

/-- **(45)**: for every `ε > 0`, eventually `det G_d ≤ exp((-I + ε) d²)`. -/
theorem gram_limsup {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ d : ℕ in atTop,
      (weightedGram d discK (gramWeight d)).det.re ≤ exp ((-energyI + ε) * (d : ℝ) ^ 2) := by
  obtain ⟨t, ht, hterr⟩ := regErr_small (by positivity : 0 < ε / 4)
  set A := truncM t + Real.log (max (volume.real discK) 1) with hA
  have hA0 : 0 ≤ A := add_nonneg (truncM_nonneg ht) (Real.log_nonneg (le_max_right _ _))
  filter_upwards [eventually_ge_atTop 1, eventually_ge_atTop ⌈2 * A / ε⌉₊] with d hd1 hdA
  have hd : 0 < d := hd1
  have hdr : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  have hB : ∀ z : Fin d → ℂ, (∀ i, z i ∈ discK) → empiricalEnergy (truncM t) z ≤
      -energyI + ε / 2 := fun z hz => by
    have := empiricalEnergy_le ht hterr hd hz; linarith
  refine (gram_det_le hd hB).trans ?_
  have hv0 : 0 ≤ volume.real discK := measureReal_nonneg
  have hmax : 0 < max (volume.real discK) 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hpow : volume.real discK ^ d / d.factorial ≤
      exp (d * Real.log (max (volume.real discK) 1)) := by
    rw [← Real.log_rpow hmax, Real.exp_log (by positivity), Real.rpow_natCast]
    have hf : (1 : ℝ) ≤ d.factorial := by exact_mod_cast Nat.factorial_pos d
    calc volume.real discK ^ d / d.factorial ≤ volume.real discK ^ d :=
          div_le_self (by positivity) hf
      _ ≤ max (volume.real discK) 1 ^ d := pow_le_pow_left₀ hv0 (le_max_left _ _) d
  have hdA' : 2 * A / ε ≤ d := (Nat.le_ceil _).trans (by exact_mod_cast hdA)
  have hlin : (d : ℝ) * A ≤ ε / 2 * (d : ℝ) ^ 2 := by
    rw [div_le_iff₀ hε] at hdA'
    nlinarith
  calc volume.real discK ^ d / d.factorial *
        exp ((d : ℝ) ^ 2 * (-energyI + ε / 2) + d * truncM t)
      ≤ exp (d * Real.log (max (volume.real discK) 1)) *
        exp ((d : ℝ) ^ 2 * (-energyI + ε / 2) + d * truncM t) :=
        mul_le_mul_of_nonneg_right hpow (exp_pos _).le
    _ = exp ((d : ℝ) ^ 2 * (-energyI + ε / 2) + d * A) := by
        rw [← exp_add, hA]; ring_nf
    _ ≤ exp ((-energyI + ε) * (d : ℝ) ^ 2) := exp_le_exp.mpr (by nlinarith)

/-- **(45), logarithmic form**: `log det G_d ≤ (-I + ε) d²` eventually, whenever `det G_d > 0`. -/
theorem gram_limsup_log {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ d : ℕ in atTop, 0 < (weightedGram d discK (gramWeight d)).det.re →
      Real.log (weightedGram d discK (gramWeight d)).det.re ≤ (-energyI + ε) * (d : ℝ) ^ 2 :=
  (gram_limsup hε).mono fun _ h hpos => (Real.log_le_iff_le_exp hpos).mpr h

end Zeta7Arch

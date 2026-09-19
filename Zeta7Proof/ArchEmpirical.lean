import Zeta7Proof.ArchGramVandermonde

/-! C3, step 3: empirical measures with diagonal correction, (44), and the resulting Gram bound.

For a configuration `z ∈ ℂ^n` let `ν_z = (1/n) Σ δ_{z_i}` be its empirical measure. With the
continuous truncated kernel `k_M(z,w) = max(log|z-w|, -M)`,

* `norm_sub_le_exp_truncLog`: `|z - w| ≤ e^{k_M(z,w)}` for all `z, w` (no `log 0` occurs);
* `vandermonde_sq_le` (44, exponentiated): `∏_{i<j} |z_j - z_i|² ≤ exp(Σ_{i,j} k_M(z_i,z_j) + nM)`,
  the diagonal terms `k_M(z_i,z_i) = -M` being exactly the correction `M/n` of (44);
* `empiricalEnergy M z = ∬ k_M dν_z dν_z - 2 ∫ U dν_z` (as the finite double sum), and
* `gram_det_le`: if `empiricalEnergy M z ≤ B` for all `z ∈ 𝒦^d`, then
  `det G_d ≤ area(𝒦)^d / d! · exp(d² B + d M)`. -/
noncomputable section
set_option autoImplicit false
namespace Zeta7Arch
open MeasureTheory Real Finset

theorem norm_sub_le_exp_truncLog (M : ℝ) (z w : ℂ) : ‖z - w‖ ≤ exp (truncLog M z w) := by
  rw [truncLog, exp_log (truncLog_arg_pos M z w)]
  exact le_max_left _ _

theorem truncLog_self (M : ℝ) (z : ℂ) : truncLog M z z = -M := by
  rw [truncLog, sub_self, norm_zero, max_eq_right (exp_pos _).le, log_exp]

theorem truncLog_comm (M : ℝ) (z w : ℂ) : truncLog M z w = truncLog M w z := by
  rw [truncLog, truncLog, norm_sub_rev]

/-- The product over ordered pairs `i ≠ j` of `|z_j - z_i|` equals `∏_{i<j} |z_j - z_i|²`. -/
theorem prod_offDiag_eq {n : ℕ} (z : Fin n → ℂ) :
    ∏ i : Fin n, ∏ j ∈ Ioi i, ‖z j - z i‖ ^ 2 =
      ∏ i : Fin n, ∏ j ∈ univ.erase i, ‖z j - z i‖ := by
  have hsplit : ∀ i : Fin n, ∏ j ∈ univ.erase i, ‖z j - z i‖ =
      (∏ j ∈ Ioi i, ‖z j - z i‖) * ∏ j ∈ Iio i, ‖z j - z i‖ := by
    intro i
    rw [← prod_union (disjoint_left.mpr fun j h1 h2 => by
      simp only [mem_Ioi, mem_Iio] at h1 h2; exact absurd (h1.trans h2) (lt_irrefl _))]
    refine prod_congr ?_ fun _ _ => rfl
    ext j
    simp only [mem_erase, mem_univ, and_true, mem_union, mem_Ioi, mem_Iio]
    exact ⟨fun h => (lt_or_gt_of_ne h).symm, fun h => h.elim (ne_of_gt) (ne_of_lt)⟩
  simp_rw [hsplit, prod_mul_distrib]
  have hswap : ∏ i : Fin n, ∏ j ∈ Iio i, ‖z j - z i‖ = ∏ i : Fin n, ∏ j ∈ Ioi i, ‖z j - z i‖ := by
    rw [prod_comm' (t' := univ) (s' := fun j => Ioi j)]
    · refine prod_congr rfl fun j _ => prod_congr rfl fun i _ => ?_
      rw [norm_sub_rev]
    · intro i j
      simp only [mem_univ, mem_Iio, mem_Ioi, true_and, and_true]
  rw [hswap, ← prod_mul_distrib]
  refine prod_congr rfl fun i _ => ?_
  rw [← prod_mul_distrib]
  refine prod_congr rfl fun j _ => ?_
  ring

/-- **(44), exponentiated.** -/
theorem vandermonde_sq_le {n : ℕ} (M : ℝ) (z : Fin n → ℂ) :
    ∏ i : Fin n, ∏ j ∈ Ioi i, ‖z j - z i‖ ^ 2 ≤
      exp (∑ i, ∑ j, truncLog M (z i) (z j) + n * M) := by
  rw [prod_offDiag_eq]
  calc ∏ i : Fin n, ∏ j ∈ univ.erase i, ‖z j - z i‖
      ≤ ∏ i : Fin n, ∏ j ∈ univ.erase i, exp (truncLog M (z i) (z j)) := by
        refine prod_le_prod (fun i _ => prod_nonneg fun j _ => norm_nonneg _) fun i _ => ?_
        refine prod_le_prod (fun j _ => norm_nonneg _) fun j _ => ?_
        rw [norm_sub_rev]
        exact norm_sub_le_exp_truncLog M (z i) (z j)
    _ = exp (∑ i, ∑ j ∈ univ.erase i, truncLog M (z i) (z j)) := by
        rw [exp_sum]
        refine prod_congr rfl fun i _ => ?_
        rw [exp_sum]
    _ = exp (∑ i, ∑ j, truncLog M (z i) (z j) + n * M) := by
        congr 1
        have h : ∀ i : Fin n, ∑ j ∈ univ.erase i, truncLog M (z i) (z j) =
            ∑ j, truncLog M (z i) (z j) + M := by
          intro i
          rw [← sum_erase_add _ _ (mem_univ i), truncLog_self]
          ring
        simp_rw [h, sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- The empirical energy `∬ k_M dν_z dν_z - 2∫ U dν_z`, as the finite double sum. -/
def empiricalEnergy {n : ℕ} (M : ℝ) (z : Fin n → ℂ) : ℝ :=
  ((n : ℝ)⁻¹) ^ 2 * ∑ i, ∑ j, truncLog M (z i) (z j) - 2 * ((n : ℝ)⁻¹ * ∑ i, potentialU (z i))

/-- The Gram integrand, weighted, is bounded by the empirical energy. -/
theorem integrand_le_energy {d : ℕ} (hd : 0 < d) (M : ℝ) (z : Fin d → ℂ) :
    (∏ i : Fin d, ∏ j ∈ Ioi i, ‖z j - z i‖ ^ 2) * exp (-(2 * d) * ∑ i, potentialU (z i)) ≤
      exp ((d : ℝ) ^ 2 * empiricalEnergy M z + d * M) := by
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  calc (∏ i : Fin d, ∏ j ∈ Ioi i, ‖z j - z i‖ ^ 2) * exp (-(2 * d) * ∑ i, potentialU (z i))
      ≤ exp (∑ i, ∑ j, truncLog M (z i) (z j) + d * M) * exp (-(2 * d) * ∑ i, potentialU (z i)) :=
        mul_le_mul_of_nonneg_right (vandermonde_sq_le M z) (exp_pos _).le
    _ = exp ((d : ℝ) ^ 2 * empiricalEnergy M z + d * M) := by
        rw [← exp_add, empiricalEnergy]
        congr 1
        field_simp
        ring

/-- The `d`-fold product of Lebesgue measure on `𝒦`. -/
theorem piRestrict_real_univ (d : ℕ) :
    (Measure.pi fun _ : Fin d => volume.restrict discK).real Set.univ =
      (volume.real discK) ^ d := by
  rw [Measure.real, ← Set.pi_univ, Measure.pi_pi, ENNReal.toReal_prod]
  simp [Measure.real]

/-- **Gram bound from the empirical energy.** -/
theorem gram_det_le {d : ℕ} (hd : 0 < d) {M B : ℝ}
    (hB : ∀ z : Fin d → ℂ, (∀ i, z i ∈ discK) → empiricalEnergy M z ≤ B) :
    (weightedGram d discK (gramWeight d)).det.re ≤
      (volume.real discK) ^ d / d.factorial * exp ((d : ℝ) ^ 2 * B + d * M) := by
  rw [gram_det_eq_integral_density, Complex.ofReal_re, gramDensityMeasure]
  set μK := Measure.pi fun _ : Fin d => volume.restrict discK with hμK
  have hdens : Measurable fun z : Fin d → ℂ =>
      (Real.exp (-(2 * d) * ∑ i, potentialU (z i))).toNNReal :=
    (Real.continuous_exp.comp (continuous_const.mul
      (continuous_finsetSum _ fun i _ =>
        potentialU_continuous.comp (continuous_apply i)))).measurable.real_toNNReal
  rw [show (fun z : Fin d → ℂ => ENNReal.ofReal (Real.exp (-(2 * d) * ∑ i, potentialU (z i)))) =
      fun z => (((Real.exp (-(2 * d) * ∑ i, potentialU (z i))).toNNReal : NNReal) : ENNReal)
      from rfl, integral_withDensity_eq_integral_smul hdens]
  have hae : ∀ᵐ z ∂μK, ∀ i, z i ∈ discK := by
    rw [ae_all_iff]
    intro i
    exact Measure.tendsto_eval_ae_ae.eventually (ae_restrict_mem isCompact_discK.isClosed.measurableSet)
  set C : ℝ := exp ((d : ℝ) ^ 2 * B + d * M) with hC
  have hpt : ∀ᵐ z ∂μK,
      (Real.exp (-(2 * d) * ∑ i, potentialU (z i))).toNNReal •
        ∏ i : Fin d, ∏ j ∈ Ioi i, ‖z j - z i‖ ^ 2 ≤ C := by
    filter_upwards [hae] with z hz
    rw [NNReal.smul_def, Real.coe_toNNReal _ (exp_pos _).le, smul_eq_mul, mul_comm]
    refine (integrand_le_energy hd M z).trans (exp_le_exp.mpr ?_)
    have := hB z hz
    have hd2 : (0 : ℝ) ≤ (d : ℝ) ^ 2 := by positivity
    nlinarith
  have hnn : 0 ≤ᵐ[μK] fun z : Fin d → ℂ =>
      (Real.exp (-(2 * d) * ∑ i, potentialU (z i))).toNNReal •
        ∏ i : Fin d, ∏ j ∈ Ioi i, ‖z j - z i‖ ^ 2 :=
    Filter.Eventually.of_forall fun z => by positivity
  have hint := integral_mono_of_nonneg hnn (integrable_const C) hpt
  rw [integral_const, smul_eq_mul, hμK, piRestrict_real_univ] at hint
  have hfac : (0 : ℝ) ≤ (d.factorial : ℝ)⁻¹ := by positivity
  calc (d.factorial : ℝ)⁻¹ * ∫ z, (Real.exp (-(2 * d) * ∑ i, potentialU (z i))).toNNReal •
          ∏ i : Fin d, ∏ j ∈ Ioi i, ‖z j - z i‖ ^ 2 ∂μK
      ≤ (d.factorial : ℝ)⁻¹ * ((volume.real discK) ^ d * C) :=
        mul_le_mul_of_nonneg_left hint hfac
    _ = (volume.real discK) ^ d / d.factorial * exp ((d : ℝ) ^ 2 * B + d * M) := by
        rw [hC]; ring

end Zeta7Arch

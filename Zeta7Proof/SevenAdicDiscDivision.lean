import Zeta7Proof.SevenAdicSeriesEvaluation

/-! Explicit analytic division at a unit-norm point by convergent coefficient tails. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
open PowerSeries Filter Topology
namespace Zeta7Common
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

theorem restricted_mono_radius {f : ℚ_[7]⟦X⟧} {r s : ℝ}
    (hr : 0 ≤ r) (hrs : r ≤ s) (hf : IsRestricted s f) : IsRestricted r f := by
  rw [isRestricted_iff']
  exact squeeze_zero (fun n => mul_nonneg (norm_nonneg _) (pow_nonneg hr n))
    (fun n => mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr hrs n) (norm_nonneg _))
    ((isRestricted_iff' _ _).mp hf)

def discQuotient (f : ℚ_[7]⟦X⟧) (a : ℚ_[7]) : ℚ_[7]⟦X⟧ :=
  mk (fun n => ∑' k : ℕ, coeff (n + k + 1) f * a ^ k)

theorem discQuotient_summable (f : ℚ_[7]⟦X⟧) (hf : IsRestricted 1 f)
    (a : ℚ_[7]) (ha : ‖a‖ = 1) (n : ℕ) :
    Summable (fun k : ℕ => coeff (n + k + 1) f * a ^ k) := by
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  rw [Nat.cofinite_eq_atTop, tendsto_zero_iff_norm_tendsto_zero]
  have ht : Tendsto (fun k : ℕ => ‖coeff k f‖) atTop (𝓝 0) := by
    simpa only [one_pow, mul_one] using (isRestricted_iff' 1 f).mp hf
  simpa only [norm_mul, norm_pow, ha, one_pow, mul_one, Nat.add_comm, Nat.add_left_comm,
    Nat.add_assoc, Function.comp_def] using ht.comp (tendsto_add_atTop_nat (n + 1))

theorem discQuotient_recurrence (f : ℚ_[7]⟦X⟧) (hf : IsRestricted 1 f)
    (a : ℚ_[7]) (ha : ‖a‖ = 1) (n : ℕ) :
    coeff n (discQuotient f a) = coeff (n + 1) f + a * coeff (n + 1) (discQuotient f a) := by
  simp only [discQuotient, coeff_mk]
  rw [(discQuotient_summable f hf a ha n).tsum_eq_zero_add]
  simp only [Nat.add_zero, pow_zero, mul_one]
  rw [← tsum_mul_left]
  congr 1
  apply tsum_congr
  intro k
  simp only [pow_succ, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  ring

theorem discQuotient_constant_relation (f : ℚ_[7]⟦X⟧) (hf : IsRestricted 1 f)
    (a : ℚ_[7]) (ha : ‖a‖ = 1) :
    seriesValue f a = coeff 0 f + a * coeff 0 (discQuotient f a) := by
  rw [seriesValue, (restricted_summable_at (by norm_num) hf a ha.le).tsum_eq_zero_add]
  simp only [pow_zero, mul_one, discQuotient, coeff_mk, Nat.zero_add]
  rw [← tsum_mul_left]
  congr 1
  apply tsum_congr
  intro k
  rw [pow_succ]
  ring

theorem discQuotient_mul (f : ℚ_[7]⟦X⟧) (hf : IsRestricted 1 f)
    (a : ℚ_[7]) (ha : ‖a‖ = 1) :
    (X - C a) * discQuotient f a = f - C (seriesValue f a) := by
  ext n
  cases n with
  | zero =>
      have h := discQuotient_constant_relation f hf a ha
      simp only [sub_mul, map_sub, coeff_zero_X_mul, coeff_C_mul, coeff_C, ↓reduceIte]
      linear_combination h
  | succ n =>
      have h := discQuotient_recurrence f hf a ha n
      simp only [sub_mul, map_sub, coeff_succ_X_mul, coeff_C_mul, coeff_C,
        Nat.succ_ne_zero, ↓reduceIte, sub_zero]
      linear_combination h

theorem discQuotient_restricted (f : ℚ_[7]⟦X⟧) {s r : ℝ}
    (hs : 1 ≤ s) (hr : 0 ≤ r) (hrs : r < s) (hf : IsRestricted s f)
    (a : ℚ_[7]) (ha : ‖a‖ = 1) : IsRestricted r (discQuotient f a) := by
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs
  obtain ⟨C₀, hC₀⟩ := ((isRestricted_iff' _ _).mp hf).bddAbove_range
  let C := max C₀ 0
  have hC : 0 ≤ C := le_max_right _ _
  have hbound (m : ℕ) : ‖coeff m f‖ ≤ C / s ^ m := by
    apply (le_div_iff₀ (pow_pos hs0 m)).mpr
    exact (hC₀ (Set.mem_range_self m)).trans (le_max_left _ _)
  have hq (n : ℕ) : ‖coeff n (discQuotient f a)‖ ≤ C / s ^ (n + 1) := by
    rw [discQuotient, coeff_mk]
    apply seven_norm_tsum_le
      (discQuotient_summable f (restricted_mono_radius (by norm_num) hs hf) a ha n)
      (div_nonneg hC (pow_nonneg hs0.le _))
    intro k
    rw [norm_mul, norm_pow, ha, one_pow, mul_one]
    exact (hbound _).trans (div_le_div_of_nonneg_left hC (pow_pos hs0 _)
      (pow_le_pow_right₀ hs (by omega)))
  rw [isRestricted_iff']
  have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hr hs0.le)
    ((div_lt_one hs0).mpr hrs)).const_mul (C / s)
  apply squeeze_zero (fun n => mul_nonneg (norm_nonneg _) (pow_nonneg hr n))
    (fun n => ?_) (by simpa only [mul_zero] using ht)
  calc
    _ ≤ C / s ^ (n + 1) * r ^ n := mul_le_mul_of_nonneg_right (hq n) (pow_nonneg hr n)
    _ = C / s * (r / s) ^ n := by rw [pow_succ, div_pow]; field_simp

end Zeta7Common

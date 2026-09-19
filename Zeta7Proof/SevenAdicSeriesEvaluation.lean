import Zeta7Proof.RetainedRadiusJets
import Zeta7Proof.ActualTargetPrimitiveBounds
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-! Convergent coefficient evaluation, including points of norm one. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
open PowerSeries Filter Topology
namespace Zeta7Common
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩
local instance : NonarchimedeanRing ℚ_[7] where
  is_nonarchimedean := NonarchimedeanAddGroup.is_nonarchimedean

def seriesValue (f : ℚ_[7]⟦X⟧) (a : ℚ_[7]) : ℚ_[7] :=
  ∑' n : ℕ, coeff n f * a ^ n

theorem restricted_summable_at {f : ℚ_[7]⟦X⟧} {r : ℝ} (hr : 0 ≤ r)
    (hf : IsRestricted r f) (a : ℚ_[7]) (ha : ‖a‖ ≤ r) :
    Summable (fun n : ℕ => coeff n f * a ^ n) := by
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  rw [Nat.cofinite_eq_atTop, tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero (fun n => norm_nonneg _)
    (fun n => ?_) ((isRestricted_iff' r f).mp hf)
  rw [norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) ha n) (norm_nonneg _)

theorem seriesValue_add {r : ℝ} (hr : 0 ≤ r) (f g : ℚ_[7]⟦X⟧)
    (hf : IsRestricted r f) (hg : IsRestricted r g) (a : ℚ_[7]) (ha : ‖a‖ ≤ r) :
    seriesValue (f + g) a = seriesValue f a + seriesValue g a := by
  simp only [seriesValue, map_add, add_mul]
  exact (restricted_summable_at hr hf a ha).tsum_add (restricted_summable_at hr hg a ha)

theorem seriesValue_sub {r : ℝ} (hr : 0 ≤ r) (f g : ℚ_[7]⟦X⟧)
    (hf : IsRestricted r f) (hg : IsRestricted r g) (a : ℚ_[7]) (ha : ‖a‖ ≤ r) :
    seriesValue (f - g) a = seriesValue f a - seriesValue g a := by
  simp only [seriesValue, map_sub, sub_mul]
  exact (restricted_summable_at hr hf a ha).tsum_sub (restricted_summable_at hr hg a ha)

set_option maxHeartbeats 1000000 in
theorem seriesValue_mul {r : ℝ} (hr : 0 ≤ r) (f g : ℚ_[7]⟦X⟧)
    (hf : IsRestricted r f) (hg : IsRestricted r g) (a : ℚ_[7]) (ha : ‖a‖ ≤ r) :
    seriesValue (f * g) a = seriesValue f a * seriesValue g a := by
  have hs := restricted_summable_at hr hf a ha
  have ht := restricted_summable_at hr hg a ha
  rw [seriesValue, seriesValue, seriesValue,
    hs.tsum_mul_tsum_eq_tsum_sum_antidiagonal ht (hs.mul_of_nonarchimedean ht)]
  apply tsum_congr
  intro n
  rw [coeff_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ij hij
  rw [← Finset.HasAntidiagonal.mem_antidiagonal.mp hij, pow_add]
  ring

@[simp] theorem seriesValue_C (b a : ℚ_[7]) : seriesValue (C b) a = b := by
  simp [seriesValue, coeff_C]

@[simp] theorem seriesValue_X (a : ℚ_[7]) : seriesValue X a = a := by
  simp [seriesValue, coeff_X]

theorem seriesValue_polynomial (p : Polynomial ℚ_[7]) (a : ℚ_[7]) :
    seriesValue (p : ℚ_[7]⟦X⟧) a = p.eval a := by
  rw [seriesValue, Polynomial.eval_eq_sum_range]
  simp only [Polynomial.coeff_coe]
  apply tsum_eq_sum
  intro n hn
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by
    have := mt Finset.mem_range.mpr hn; omega), zero_mul]

theorem restricted_polynomial (p : Polynomial ℚ_[7]) (r : ℝ) :
    IsRestricted r (p : ℚ_[7]⟦X⟧) := by
  rw [isRestricted_iff']
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop p.natDegree] with n hn
  simp [Polynomial.coeff_eq_zero_of_natDegree_lt hn]

theorem restricted_euler {f : ℚ_[7]⟦X⟧} {r : ℝ} (hr : 0 ≤ r)
    (hf : IsRestricted r f) : IsRestricted r (euler f) := by
  rw [isRestricted_iff']
  apply squeeze_zero (fun n => mul_nonneg (norm_nonneg _) (pow_nonneg hr n))
    (fun n => mul_le_mul_of_nonneg_right (euler_iterate_coeff_norm_le f 1 n)
      (pow_nonneg hr n))
  exact (isRestricted_iff' _ _).mp hf

theorem seven_norm_tsum_le {f : ℕ → ℚ_[7]} (hf : Summable f) {C : ℝ}
    (hC : 0 ≤ C) (h : ∀ n, ‖f n‖ ≤ C) : ‖∑' n, f n‖ ≤ C := by
  apply le_of_tendsto hf.hasSum.norm
  exact Filter.Eventually.of_forall (fun s =>
    IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hC (fun i _ => h i))

end Zeta7Common

import Zeta7Proof.SevenAdicSeriesEvaluation
import Mathlib.Analysis.SpecificLimits.Normed

/-! Integer division loses only a polynomial factor, absorbed by any smaller radius. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
open PowerSeries Filter Topology
namespace Zeta7Common
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

theorem coeff_norm_le_euler (f : ℚ_[7]⟦X⟧) (n : ℕ) (hn : n ≠ 0) :
    ‖coeff n f‖ ≤ (n : ℝ) * ‖coeff n (euler f)‖ := by
  have he : coeff n f = (n : ℚ_[7])⁻¹ * coeff n (euler f) := by
    rw [euler_coeff, ← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast hn), one_mul]
  rw [he, norm_mul]
  exact mul_le_mul_of_nonneg_right (padic_inverse_nat_norm_le n) (norm_nonneg _)

theorem restricted_of_euler {f : ℚ_[7]⟦X⟧} {r s : ℝ}
    (hr : 0 ≤ r) (hs : 0 < s) (hrs : r < s) (hf : IsRestricted s (euler f)) :
    IsRestricted r f := by
  obtain ⟨C₀, hC₀⟩ := ((isRestricted_iff' _ _).mp hf).bddAbove_range
  let C := max C₀ 0
  have hbound (n : ℕ) : ‖coeff n (euler f)‖ * s ^ n ≤ C :=
    (hC₀ (Set.mem_range_self n)).trans (le_max_left _ _)
  have hb (n : ℕ) (hn : n ≠ 0) : ‖coeff n f‖ * r ^ n ≤ C * ((n : ℝ) * (r / s) ^ n) := by
    calc
      _ ≤ (n : ℝ) * ‖coeff n (euler f)‖ * r ^ n :=
        mul_le_mul_of_nonneg_right (coeff_norm_le_euler f n hn) (pow_nonneg hr n)
      _ = (‖coeff n (euler f)‖ * s ^ n) * ((n : ℝ) * (r / s) ^ n) := by
        rw [div_pow]; field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (hbound n) (by positivity)
  rw [isRestricted_iff']
  have ht := (tendsto_self_mul_const_pow_of_lt_one (div_nonneg hr hs.le)
    ((div_lt_one hs).mpr hrs)).const_mul C
  apply squeeze_zero' (Filter.Eventually.of_forall (fun n =>
    mul_nonneg (norm_nonneg _) (pow_nonneg hr n))) ?_ (by simpa only [mul_zero] using ht)
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact hb n (Nat.ne_of_gt hn)

theorem euler_primitive_seven (f : ℚ_[7]⟦X⟧) : euler (primitive f) = X * f := by
  ext n
  cases n with
  | zero => simp [euler_coeff, primitive]
  | succ n =>
      simp only [euler_coeff, primitive, coeff_mk, Nat.succ_ne_zero, ↓reduceIte,
        Nat.succ_sub_one, coeff_succ_X_mul]
      exact mul_div_cancel₀ _ (by exact_mod_cast Nat.succ_ne_zero n)

end Zeta7Common

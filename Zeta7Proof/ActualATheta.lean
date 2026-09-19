import Zeta7Proof.RamanujanTwo

/-! Differential consequences for the original product-defined A.
The Euler operator here acts on q, and expansion replaces q by q^7. -/
noncomputable section
open PowerSeries
namespace Zeta7Common
open Zeta7Main Zeta7Classical

theorem euler_expand_seven (f : ℚ⟦X⟧) :
    euler ((expand 7 (by decide)) f) = C (7 : ℚ) * (expand 7 (by decide)) (euler f) := by
  ext n
  rw [euler_coeff, coeff_expand, coeff_C_mul, coeff_expand]
  by_cases hn : 7 ∣ n
  · simp only [hn, ite_true, euler_coeff]
    have he : (n : ℚ) = 7 * ((n / 7 : ℕ) : ℚ) := by
      exact_mod_cast (Nat.mul_div_cancel' hn).symm
    rw [he]
    ring
  · simp [hn]

/-- A denominator-cleared differential identity for the actual A. -/
theorem ASeries_theta_eisenstein :
    C (72 : ℚ) * euler ASeries = C (36 : ℚ) * ASeries ^ 2 +
      C (12 : ℚ) * ASeries * eisensteinTwoQ + eisensteinFourQ -
      C (49 : ℚ) * (expand 7 (by decide)) eisensteinFourQ := by
  have ha := ASeries_eisensteinTwo
  have hd := congrArg euler ha
  simp only [euler_mul, euler_C, zero_mul, zero_add, euler_sub, euler_expand_seven] at hd
  have h2 := eisensteinTwoQ_ramanujan
  have h7 := congrArg (expand 7 (by decide) (R := ℚ)) h2
  simp only [map_mul, map_sub, map_pow, expand_C] at h7
  simp only [map_ofNat] at ha hd h2 h7 ⊢
  linear_combination 12 * hd - h2 + 49 * h7 -
    (6 * ASeries + eisensteinTwoQ + 7 * (expand 7 (by decide)) eisensteinTwoQ) * ha

end Zeta7Common

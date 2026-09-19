import Zeta7Proof.AnnulusEstimates
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! Section 3 equation (12), with its actual epsilon-dependent constants.
No bound for the target H is assumed or asserted by an instance. -/

set_option autoImplicit false
noncomputable section
namespace Zeta7Section3
open Filter Topology PowerSeries
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

theorem exists_small_exponent (q : ℝ) (hq1 : q < 1) :
    ∃ ε : ℝ, 0 < ε ∧ (7 : ℝ) ^ ε * q < 1 := by
  have ht : Tendsto (fun ε : ℝ => (7 : ℝ) ^ ε * q) (𝓝 0) (𝓝 q) := by
    simpa using (Real.continuousAt_const_rpow (b := 0)
      (by norm_num : (7 : ℝ) ≠ 0)).tendsto.mul_const q
  obtain ⟨δ, hδ, hd⟩ := Metric.eventually_nhds_iff.mp (ht.eventually (gt_mem_nhds hq1))
  refine ⟨δ / 2, by linarith, hd ?_⟩
  simp only [dist_zero_right, Real.norm_eq_abs, abs_of_pos (by linarith : 0 < δ / 2)]
  linarith

/-- Equation (12)'s norm form implies decay on every smaller normalized disc. -/
theorem weighted_decay_of_epsilon_bound (a : ℕ → ℚ_[7])
    (hbound : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧
      ∀ n : ℕ, ‖a n‖ ≤ (7 : ℝ) ^ (ε * n + B))
    (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    Tendsto (fun n => ‖a n‖ * q ^ n) atTop (𝓝 0) := by
  obtain ⟨ε, hε, hsmall⟩ := exists_small_exponent q hq1
  obtain ⟨B, _, hB⟩ := hbound ε hε
  have hfactor (n : ℕ) :
      (7 : ℝ) ^ (ε * n + B) * q ^ n =
        (7 : ℝ) ^ B * ((7 : ℝ) ^ ε * q) ^ n := by
    rw [Real.rpow_add (by norm_num), Real.rpow_mul (by norm_num),
      Real.rpow_natCast, mul_pow]
    ring
  have hgeom := tendsto_pow_atTop_nhds_zero_of_lt_one
    (mul_nonneg (Real.rpow_nonneg (by norm_num) _) hq0.le) hsmall
  apply squeeze_zero (fun n => mul_nonneg (norm_nonneg _) (pow_nonneg hq0.le n))
    (fun n => (mul_le_mul_of_nonneg_right (hB n) (pow_nonneg hq0.le n)).trans_eq (hfactor n))
  simpa using hgeom.const_mul ((7 : ℝ) ^ B)

/-- Exact rescaling for an arbitrary scalar series, retaining |49|_7=1/49. -/
theorem weighted_rescale_identity (f : ℚ_[7]⟦X⟧) (ρ : ℝ) (n : ℕ) :
    ‖coeff n (rescale (49 : ℚ_[7])⁻¹ f)‖ * (ρ / 49) ^ n =
      ‖coeff n f‖ * ρ ^ n := by
  rw [coeff_rescale, norm_mul, norm_pow, norm_inv, Zeta7Main.norm_seven_square,
    inv_inv, div_pow]
  field_simp

/-- Scalar criterion from precisely the manuscript's epsilon-dependent estimate.
This generic criterion does not prove the bound for HSeries. -/
theorem radius49_of_epsilon_bound (f : ℚ_[7]⟦X⟧)
    (hbound : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧
      ∀ n : ℕ, ‖coeff n (rescale (49 : ℚ_[7])⁻¹ f)‖ ≤
        (7 : ℝ) ^ (ε * n + B))
    (ρ : ℝ) (hρ0 : 0 < ρ) (hρ49 : ρ < 49) :
    Tendsto (fun n => ‖coeff n f‖ * ρ ^ n) atTop (𝓝 0) := by
  have h := weighted_decay_of_epsilon_bound
    (fun n => coeff n (rescale (49 : ℚ_[7])⁻¹ f)) hbound
    (ρ / 49) (by positivity) ((div_lt_one (by norm_num)).mpr hρ49)
  simpa only [weighted_rescale_identity] using h

/-- Real-valued valuation inequalities, with zero treated separately as infinity. -/
theorem norm_bound_of_valuation (x : ℚ_[7]) (L : ℝ)
    (hv : x ≠ 0 → L ≤ (Padic.valuation x : ℝ)) :
    ‖x‖ ≤ (7 : ℝ) ^ (-L) := by
  by_cases hx : x = 0
  · simp only [hx, norm_zero]
    exact Real.rpow_nonneg (by norm_num) _
  · rw [Padic.norm_eq_zpow_neg_valuation hx, Nat.cast_ofNat, ← Real.rpow_intCast]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    simpa only [Int.cast_neg, neg_le_neg_iff] using hv hx

/-- The valuation form of equation (12), not a stronger logarithmic estimate. -/
theorem radius49_of_valuation_estimate (f : ℚ_[7]⟦X⟧)
    (hbound : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧
      ∀ n : ℕ, coeff n (rescale (49 : ℚ_[7])⁻¹ f) ≠ 0 →
        -ε * n - B ≤ (Padic.valuation (coeff n (rescale (49 : ℚ_[7])⁻¹ f)) : ℝ))
    (ρ : ℝ) (hρ0 : 0 < ρ) (hρ49 : ρ < 49) :
    Tendsto (fun n => ‖coeff n f‖ * ρ ^ n) atTop (𝓝 0) := by
  apply radius49_of_epsilon_bound f ?_ ρ hρ0 hρ49
  intro ε hε
  obtain ⟨B, hB0, hB⟩ := hbound ε hε
  refine ⟨B, hB0, fun n => ?_⟩
  have h := norm_bound_of_valuation (coeff n (rescale (49 : ℚ_[7])⁻¹ f))
    (-ε * n - B) (hB n)
  have heq : -(-ε * (n : ℝ) - B) = ε * n + B := by ring
  simpa only [heq] using h

/-- The exact valuation shift under t=49x; this fixes the sign of the radius exponent. -/
theorem rescale_valuation (f : ℚ_[7]⟦X⟧) (n : ℕ) (hn : coeff n f ≠ 0) :
    (Padic.valuation (coeff n (rescale (49 : ℚ_[7])⁻¹ f)) : ℝ) =
      (Padic.valuation (coeff n f) : ℝ) - 2 * n := by
  have h7 : Padic.valuation (7 : ℚ_[7]) = 1 := by
    simpa only [Nat.cast_ofNat] using Padic.valuation_p (p := 7)
  have h49 : Padic.valuation (49 : ℚ_[7]) = 2 := by
    rw [show (49 : ℚ_[7]) = (7 : ℚ_[7]) ^ 2 by norm_num, Padic.valuation_pow, h7]
    norm_num
  rw [coeff_rescale, Padic.valuation_mul (pow_ne_zero _ (inv_ne_zero (by norm_num))) hn,
    Padic.valuation_pow, Padic.valuation_inv, h49]
  push_cast
  ring

/-- In x-coordinates the manuscript gives (2-epsilon)n-B, not 2n-O(log n). -/
theorem radius49_of_unscaled_valuation_estimate (f : ℚ_[7]⟦X⟧)
    (hbound : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧
      ∀ n : ℕ, coeff n f ≠ 0 →
        (2 - ε) * n - B ≤ (Padic.valuation (coeff n f) : ℝ))
    (ρ : ℝ) (hρ0 : 0 < ρ) (hρ49 : ρ < 49) :
    Tendsto (fun n => ‖coeff n f‖ * ρ ^ n) atTop (𝓝 0) := by
  apply radius49_of_valuation_estimate f ?_ ρ hρ0 hρ49
  intro ε hε
  obtain ⟨B, hB0, hB⟩ := hbound ε hε
  refine ⟨B, hB0, fun n hn => ?_⟩
  have hn' : coeff n f ≠ 0 := by
    intro hzero
    apply hn
    simp only [coeff_rescale, hzero, mul_zero]
  rw [rescale_valuation f n hn']
  have h := hB n hn'
  linarith


end Zeta7Section3

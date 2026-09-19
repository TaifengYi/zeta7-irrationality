import Zeta7Proof.Section3ScalarCriterion
import Mathlib.RingTheory.PowerSeries.Restricted
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! The coefficient bridge for actual restricted power series.
The hypotheses below are explicit generic coefficient-space membership.
No membership or continuation is asserted for the genuine H-series. -/

set_option autoImplicit false
noncomputable section
namespace Zeta7Radius49
open PowerSeries Filter Topology
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

theorem restricted_coeff_bound (δ : ℝ)
    (f : PowerSeries.IsRestricted.subring (R := ℚ_[7]) ((7 : ℝ) ^ (-δ))) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ, coeff n (f : ℚ_[7]⟦X⟧) ≠ 0 →
      -δ * (n : ℝ) - B ≤ (Padic.valuation (coeff n (f : ℚ_[7]⟦X⟧)) : ℝ) := by
  have ht := (PowerSeries.isRestricted_iff' _ _).mp f.property
  obtain ⟨C, hC⟩ := ht.bddAbove_range
  let D : ℝ := max C 1
  have hD : 1 ≤ D := le_max_right _ _
  have hD0 : 0 < D := lt_of_lt_of_le zero_lt_one hD
  refine ⟨Real.logb 7 D, Real.logb_nonneg (by norm_num) hD, fun n hn => ?_⟩
  have hbound : ‖coeff n (f : ℚ_[7]⟦X⟧)‖ * ((7 : ℝ) ^ (-δ)) ^ n ≤ D :=
    (hC (Set.mem_range_self n)).trans (le_max_left _ _)
  have hnorm : ‖coeff n (f : ℚ_[7]⟦X⟧)‖ =
      (7 : ℝ) ^ (-(Padic.valuation (coeff n (f : ℚ_[7]⟦X⟧)) : ℝ)) := by
    rw [Padic.norm_eq_zpow_neg_valuation hn]
    simp only [Nat.cast_ofNat, ← Real.rpow_intCast, Int.cast_neg]
  have hpow : ‖coeff n (f : ℚ_[7]⟦X⟧)‖ * ((7 : ℝ) ^ (-δ)) ^ n =
      (7 : ℝ) ^ (-(Padic.valuation (coeff n (f : ℚ_[7]⟦X⟧)) : ℝ) - δ*n) := by
    rw [hnorm, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
      ← Real.rpow_add (by norm_num)]
    congr 1
    ring
  rw [hpow] at hbound
  have h := (Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 7) hD0).mpr hbound
  linarith

/-- A single smaller-disc restriction supplies every weaker epsilon estimate. -/
theorem restricted_coeff_epsilon_bound (δ ε : ℝ) (hδε : δ ≤ ε)
    (f : PowerSeries.IsRestricted.subring (R := ℚ_[7]) ((7 : ℝ) ^ (-δ))) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ, coeff n (f : ℚ_[7]⟦X⟧) ≠ 0 →
      -ε * (n : ℝ) - B ≤ (Padic.valuation (coeff n (f : ℚ_[7]⟦X⟧)) : ℝ) := by
  obtain ⟨B, hB, hb⟩ := restricted_coeff_bound δ f
  refine ⟨B, hB, fun n hn => ?_⟩
  have h := hb n hn
  have hm := mul_le_mul_of_nonneg_right hδε (Nat.cast_nonneg (α := ℝ) n)
  linarith

/-- Rational smaller radii suffice; the estimate is uniform in the coefficient index. -/
theorem equation12_of_rational_restrictions (f : ℚ_[7]⟦X⟧)
    (hf : ∀ δ : ℚ, 0 < δ → PowerSeries.IsRestricted ((7 : ℝ) ^ (-(δ : ℝ))) f)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ, coeff n f ≠ 0 →
      -ε * (n : ℝ) - B ≤ (Padic.valuation (coeff n f) : ℝ) := by
  obtain ⟨δ, hδ0, hδε⟩ := exists_rat_btwn hε
  have hδ : (0 : ℚ) < δ := by exact_mod_cast hδ0
  exact restricted_coeff_epsilon_bound (δ : ℝ) ε hδε.le ⟨f, hf δ hδ⟩

theorem isRestricted_map_iff (K : Type*) [NormedField K] [NormedAlgebra ℚ_[7] K]
    (f : ℚ_[7]⟦X⟧) (s : ℝ) :
    PowerSeries.IsRestricted s (f.map (algebraMap ℚ_[7] K)) ↔
      PowerSeries.IsRestricted s f := by
  simp only [PowerSeries.isRestricted_iff', coeff_map, norm_algebraMap' K]

end Zeta7Radius49

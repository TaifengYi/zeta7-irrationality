import Zeta7Proof.Radius49Bridge
import Mathlib.Analysis.Normed.Group.Ultra

/-! Radius internalization, Phase VII: the fixed-point bootstrap engine.

Everything here is independent of modular geometry and of the published radius input.

* `BoundedAt h ρ`: `‖hₙ‖ ρⁿ` is bounded (membership in the bounded unit ball at radius `ρ`).
* `boundedAt_of_matrix`: if `hᵢ = Σ_{n ≤ 7i} tᵢₙ hₙ` and `‖tᵢₙ‖ ρ'^i ≤ K Rⁿ`, then boundedness at
  radius `R` gives boundedness at radius `ρ'` (one ultrametric step, no loss in the number of
  terms).
* `reach_all_below_two`: for the `p = 7` improvement map `s ↦ min (7s) ((12+s)/7)` (the canonical
  side `s ↦ 7s` and the far side `2-s ↦ (2-s)/7`), any property that is antitone, holds at some
  `s₀ > 0`, and is preserved by the map on `(0,2)`, holds for every `s < 2`.
* `decay_all_below_two`: the resulting coefficient decay at every radius `7^r`, `r < 2`. -/

set_option autoImplicit false
noncomputable section
namespace Zeta7Radius49
open Filter Topology
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- Bounded coefficient growth at radius `ρ`. -/
def BoundedAt (h : ℕ → ℚ_[7]) (ρ : ℝ) : Prop := ∃ C : ℝ, ∀ n, ‖h n‖ * ρ ^ n ≤ C

theorem BoundedAt.mono {h : ℕ → ℚ_[7]} {ρ ρ' : ℝ} (hb : BoundedAt h ρ') (h0 : 0 ≤ ρ)
    (hle : ρ ≤ ρ') : BoundedAt h ρ := by
  obtain ⟨C, hC⟩ := hb
  exact ⟨C, fun n => (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 hle n)
    (norm_nonneg _)).trans (hC n)⟩

/-- Boundedness at a larger radius gives decay at every smaller radius. -/
theorem decay_of_boundedAt {h : ℕ → ℚ_[7]} {ρ ρ' : ℝ} (hb : BoundedAt h ρ') (h0 : 0 ≤ ρ)
    (hlt : ρ < ρ') : Tendsto (fun n => ‖h n‖ * ρ ^ n) atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := hb
  have hρ' : 0 < ρ' := h0.trans_lt hlt
  have hr0 : 0 ≤ ρ / ρ' := div_nonneg h0 hρ'.le
  have hr1 : ρ / ρ' < 1 := (div_lt_one hρ').mpr hlt
  have hg : Tendsto (fun n : ℕ => C * (ρ / ρ') ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).const_mul C
  refine squeeze_zero (fun n => mul_nonneg (norm_nonneg _) (pow_nonneg h0 n)) (fun n => ?_) hg
  have hpos : 0 < ρ' ^ n := pow_pos hρ' n
  calc ‖h n‖ * ρ ^ n = (‖h n‖ * ρ' ^ n) * (ρ / ρ') ^ n := by
        rw [div_pow]; field_simp
    _ ≤ C * (ρ / ρ') ^ n := mul_le_mul_of_nonneg_right (hC n) (pow_nonneg hr0 n)

/-- **One ultrametric matrix step.** -/
theorem boundedAt_of_matrix (h : ℕ → ℚ_[7]) (t : ℕ → ℕ → ℚ_[7])
    (hfix : ∀ i, h i = ∑ n ∈ Finset.range (7 * i + 1), t i n * h n)
    {R ρ K : ℝ} (hR : 0 ≤ R) (hρ : 0 ≤ ρ) (hK0 : 0 ≤ K)
    (hK : ∀ i n, ‖t i n‖ * ρ ^ i ≤ K * R ^ n) (hb : BoundedAt h R) : BoundedAt h ρ := by
  obtain ⟨C, hC⟩ := hb
  have hC0 : 0 ≤ C := (mul_nonneg (norm_nonneg _) (pow_nonneg hR 0)).trans (hC 0)
  refine ⟨K * C, fun i => ?_⟩
  have hsum : ‖∑ n ∈ Finset.range (7 * i + 1), t i n * h n‖ ≤ (K * C) / ρ ^ i ∨ ρ ^ i = 0 := by
    rcases eq_or_lt_of_le (pow_nonneg hρ i) with h0 | hpos
    · exact Or.inr h0.symm
    left
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
    intro n _
    rw [norm_mul, le_div_iff₀ hpos]
    calc ‖t i n‖ * ‖h n‖ * ρ ^ i = (‖t i n‖ * ρ ^ i) * ‖h n‖ := by ring
      _ ≤ (K * R ^ n) * ‖h n‖ := mul_le_mul_of_nonneg_right (hK i n) (norm_nonneg _)
      _ = K * (‖h n‖ * R ^ n) := by ring
      _ ≤ K * C := mul_le_mul_of_nonneg_left (hC n) hK0
  rw [hfix i]
  rcases hsum with hs | h0
  · rcases eq_or_lt_of_le (pow_nonneg hρ i) with h0 | hpos
    · rw [← h0, mul_zero]; positivity
    · calc _ ≤ (K * C) / ρ ^ i * ρ ^ i := mul_le_mul_of_nonneg_right hs hpos.le
        _ = K * C := by field_simp
  · rw [h0, mul_zero]; positivity

/-- The `p = 7` radius-improvement map on depths `s = log₇(radius)`. -/
def improve (s : ℝ) : ℝ := min (7 * s) ((12 + s) / 7)

theorem improve_ge_of_small {s : ℝ} (hs : s ≤ 1 / 4) (hs0 : 0 ≤ s) :
    min (7 * s) (1 / 4) ≤ improve s := by
  unfold improve
  apply le_min (min_le_left _ _) ((min_le_right _ _).trans (by linarith))

theorem improve_eq_of_large {s : ℝ} (hs : 1 / 4 ≤ s) : improve s = (12 + s) / 7 := by
  unfold improve; exact min_eq_right (by linarith)

/-- **The iteration reaches every depth below `2`.** -/
theorem reach_all_below_two (P : ℝ → Prop) (hmono : ∀ s s', s' ≤ s → P s → P s')
    {s₀ : ℝ} (hs₀ : 0 < s₀) (h₀ : P s₀)
    (hstep : ∀ s, 0 < s → s < 2 → P s → P (improve s)) :
    ∀ r, r < 2 → P r := by
  -- Phase 1: reach depth `1/4`.
  set s₁ := min s₀ (1 / 4) with hs₁
  have hs₁pos : 0 < s₁ := lt_min hs₀ (by norm_num)
  have hP₁ : P s₁ := hmono s₀ s₁ (min_le_left _ _) h₀
  have hind : ∀ k : ℕ, P (min ((7 : ℝ) ^ k * s₁) (1 / 4)) := by
    intro k
    induction k with
    | zero => exact hmono _ _ (by simp) hP₁
    | succ k ih =>
      set u := min ((7 : ℝ) ^ k * s₁) (1 / 4) with hu
      have hu0 : 0 < u := lt_min (by positivity) (by norm_num)
      have hu4 : u ≤ 1 / 4 := min_le_right _ _
      have hP := hstep u hu0 (by linarith) ih
      apply hmono _ _ _ hP
      calc min ((7 : ℝ) ^ (k + 1) * s₁) (1 / 4) ≤ min (7 * u) (1 / 4) := by
            rcases le_total ((7 : ℝ) ^ k * s₁) (1 / 4) with h | h
            · apply min_le_min_right
              rw [hu, min_eq_left h, pow_succ]; linarith
            · exact le_min ((min_le_right _ _).trans (by rw [hu, min_eq_right h]; norm_num))
                (min_le_right _ _)
        _ ≤ improve u := improve_ge_of_small hu4 hu0.le
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (1 / 4 / s₁) (by norm_num : (1 : ℝ) < 7)
  have hq : (1 / 4 : ℝ) ≤ (7 : ℝ) ^ k * s₁ := by
    rw [div_lt_iff₀ hs₁pos] at hk; linarith
  have hP4 : P (1 / 4) := by have := hind k; rwa [min_eq_right hq] at this
  -- Phase 2: geometric approach to `2`.
  have hind2 : ∀ k : ℕ, P (2 - (7 / 4) / (7 : ℝ) ^ k) := by
    intro k
    induction k with
    | zero => exact hmono _ _ (by norm_num) hP4
    | succ k ih =>
      have hpos : (0 : ℝ) < 7 ^ k := by positivity
      have hge : (1 / 4 : ℝ) ≤ 2 - (7 / 4) / 7 ^ k := by
        have : (7 / 4 : ℝ) / 7 ^ k ≤ 7 / 4 := div_le_self (by norm_num) (one_le_pow₀ (by norm_num))
        linarith
      have hlt : 2 - (7 / 4) / (7 : ℝ) ^ k < 2 := by
        have : (0 : ℝ) < (7 / 4) / 7 ^ k := by positivity
        linarith
      have hP := hstep _ (by linarith) hlt ih
      rw [improve_eq_of_large hge] at hP
      apply hmono _ _ (le_of_eq _) hP
      rw [pow_succ]; field_simp; ring
  intro r hr
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt ((7 / 4) / (2 - r)) (by norm_num : (1 : ℝ) < 7)
  have hpos : (0 : ℝ) < 7 ^ k := by positivity
  apply hmono _ _ _ (hind2 k)
  rw [div_lt_iff₀ (by linarith)] at hk
  have : (7 / 4 : ℝ) / 7 ^ k < 2 - r := by rw [div_lt_iff₀ hpos]; linarith
  linarith

/-- **Fixed-point bootstrap.** Initial boundedness at some depth `s₀ > 0` and the one-step
improvement on `(0,2)` give coefficient decay at every radius `7^r`, `r < 2`. -/
theorem decay_all_below_two (h : ℕ → ℚ_[7]) {s₀ : ℝ} (hs₀ : 0 < s₀)
    (h₀ : BoundedAt h ((7 : ℝ) ^ s₀))
    (hstep : ∀ s, 0 < s → s < 2 → BoundedAt h ((7 : ℝ) ^ s) →
      BoundedAt h ((7 : ℝ) ^ improve s)) :
    ∀ r : ℝ, r < 2 → Tendsto (fun n => ‖h n‖ * ((7 : ℝ) ^ r) ^ n) atTop (𝓝 0) := by
  have hall := reach_all_below_two (fun s => BoundedAt h ((7 : ℝ) ^ s))
    (fun s s' hle hb => hb.mono (by positivity)
      (Real.rpow_le_rpow_of_exponent_le (by norm_num) hle)) hs₀ h₀ hstep
  intro r hr
  have hb := hall ((r + 2) / 2) (by linarith)
  exact decay_of_boundedAt hb (by positivity)
    (Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith))

end Zeta7Radius49

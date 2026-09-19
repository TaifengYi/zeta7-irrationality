import Zeta7Proof.AnnularDeterminantLogBound

/-! Annular saving for the original common rational determinant. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
namespace Zeta7Annulus
local instance ActualAnnularSaving_prime : Fact (Nat.Prime 7) := ⟨by decide⟩
open Zeta7Common

theorem actualNormalizedDeterminant_annular_bound (β ε : ℝ)
    (hε : 0 < ε) (hεβ : ε < β) (hβ2 : β < 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (d : ℕ), 7 ≤ d → ∀ (c : ℚ),
      (c : ℚ_[7]) = Zeta7Main.eta →
      (β / 2 - 42 * ε) * (d : ℝ) ^ 2 - K * d ≤
        (padicValRat 7 (actualNormalizedDeterminant d c) : ℝ) := by
  have hβ : 0 < β := hε.trans hεβ
  have h7 : (0 : ℝ) < 7 := by norm_num
  have hlog : 0 < Real.log 7 := Real.log_pos (by norm_num)
  let ρ : ℝ := (7 : ℝ) ^ (-β)
  let σ : ℝ := (7 : ℝ) ^ (-ε)
  have hρ : (1 / 49 : ℝ) < ρ := by
    have hh : (7 : ℝ) ^ (-2 : ℝ) = 1 / 49 := by norm_num [Real.rpow_neg]
    rw [← hh]
    exact (Real.rpow_lt_rpow_left_iff (by norm_num)).mpr (by linarith)
  have hρσ : ρ < σ :=
    (Real.rpow_lt_rpow_left_iff (by norm_num)).mpr (neg_lt_neg hεβ)
  have hσ1 : σ < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos hε)
  obtain ⟨a, ha⟩ := actualNormalizedDeterminant_log_bound
  obtain ⟨C, hC, hb⟩ := ha ρ σ hρ hρσ hσ1
  let L : ℝ := Real.log C / Real.log 7
  have hL : 0 ≤ L := div_nonneg (Real.log_nonneg hC) hlog.le
  have hCL : Real.log C = L * Real.log 7 := by
    exact (div_mul_cancel₀ _ hlog.ne').symm
  refine ⟨6 * L + 1050 * ε + 7 * β + a, by positivity, fun d hd c hc => ?_⟩
  have hh := hb d c hc
  have hk : ((d - 6 : ℕ) : ℝ) = (d : ℝ) - 6 := by
    rw [Nat.cast_sub (by omega : 6 ≤ d)]; norm_num
  have hs : (∑ m : Fin (d - 6), (m.val : ℝ)) =
      ((d : ℝ) - 6) * ((d : ℝ) - 7) / 2 := by
    have ht := two_mul_sum_fin_cast (d - 6)
    rw [hk] at ht
    nlinarith
  dsimp [ρ, σ] at hh
  rw [Real.log_rpow h7, Real.log_rpow h7, hCL, hk, hs] at hh
  have hh' : -((padicValRat 7 (actualNormalizedDeterminant d c) : ℝ) +
      a * ((d : ℝ) - 6)) ≤
      6 * (d : ℝ) * (L + (7 * (d : ℝ) + 175) * ε) -
        ((d : ℝ) - 6) * ((d : ℝ) - 7) / 2 * β := by
    apply (mul_le_mul_iff_left₀ hlog).mp
    nlinarith [hh]
  have hdn : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have had : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  nlinarith [mul_nonneg hβ.le hdn]

theorem actualCommonDeterminant_annular_bound_small (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (d : ℕ), 7 ≤ d → ∀ (c : ℚ),
      (c : ℚ_[7]) = Zeta7Main.eta →
      (43 - δ) * (d : ℝ) ^ 2 - K * d ≤
        (padicValRat 7 (actualCommonDeterminant d c) : ℝ) := by
  obtain ⟨K, hK, hb⟩ := actualNormalizedDeterminant_annular_bound (2 - δ) (δ / 84)
    (by positivity) (by linarith) (by linarith)
  refine ⟨K, hK, fun d hd c hc => ?_⟩
  have hn := hb d hd c hc
  have hbase : 42 * (d : ℝ) ^ 2 + (padicValRat 7 (actualNormalizedDeterminant d c) : ℝ) ≤
      (padicValRat 7 (actualCommonDeterminant d c) : ℝ) := by
    exact_mod_cast actualCommonDeterminant_valuation_baseline d c
  nlinarith

/-- The constant precedes all degrees and all rational target parameters.
Its radius input is the internally proved `Zeta7Main.HSeries_radius49`; it uses only `propext`,
`Classical.choice` and `Quot.sound`. -/
theorem actualCommonDeterminant_annular_saving (δ : ℝ) (hδ : 0 < δ) (hδ2 : δ < 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (d : ℕ), 7 ≤ d → ∀ (c : ℚ),
      (c : ℚ_[7]) = Zeta7Main.eta →
      (43 - δ) * (d : ℝ) ^ 2 - K * d ≤
        (padicValRat 7 (actualCommonDeterminant d c) : ℝ) := by
  by_cases hd : δ ≤ 1
  · exact actualCommonDeterminant_annular_bound_small δ hδ hd
  · obtain ⟨K, hK, hb⟩ := actualCommonDeterminant_annular_bound_small 1 (by norm_num) le_rfl
    refine ⟨K, hK, fun d hd' c hc => ?_⟩
    have hn := hb d hd' c hc
    have hpos := mul_nonneg (show 0 ≤ δ - 1 by linarith) (sq_nonneg (d : ℝ))
    nlinarith

end Zeta7Annulus

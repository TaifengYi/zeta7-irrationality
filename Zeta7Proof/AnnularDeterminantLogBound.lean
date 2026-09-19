import Zeta7Proof.AnnularCompletedMatrix

/-! Exact logarithmic estimate with the original integral completion cost. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
namespace Zeta7Annulus
local instance AnnularDeterminantLogBound_prime : Fact (Nat.Prime 7) := ⟨by decide⟩
open Zeta7Common Zeta7AnnularSource

theorem padic_log_norm (x : ℚ_[7]) (hx : x ≠ 0) :
    Real.log ‖x‖ = -(x.valuation : ℝ) * Real.log 7 := by
  rw [Padic.norm_eq_zpow_neg_valuation hx, Real.log_zpow, Int.cast_neg]
  norm_num

theorem two_mul_sum_fin_cast (n : ℕ) :
    2 * (∑ i : Fin n, (i.val : ℝ)) = (n : ℝ) * ((n : ℝ) - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, Nat.cast_add, Nat.cast_one]
    nlinarith

/-- The fixed source cost a is chosen independently of the radii, parameter,
and degree. All determinants are the original canonical determinants. -/
theorem actualNormalizedDeterminant_log_bound :
    ∃ a : ℕ, ∀ (ρ σ : ℝ), (1 / 49 : ℝ) < ρ → ρ < σ → σ < 1 →
      ∃ C : ℝ, 1 ≤ C ∧ ∀ (d : ℕ) (c : ℚ), (c : ℚ_[7]) = Zeta7Main.eta →
        -((padicValRat 7 (actualNormalizedDeterminant d c) : ℝ) +
            (a : ℝ) * (d - 6 : ℕ)) * Real.log 7 ≤
          (6 * (d : ℝ)) * (Real.log C - (7 * (d : ℝ) + 175) * Real.log σ) +
            (∑ m : Fin (d - 6), (m.val : ℝ)) * Real.log ρ := by
  obtain ⟨a, ell, hell, hcost⟩ := actualAnnularSourceCompletion_cost
  refine ⟨a, fun ρ σ hρ hρσ hσ1 => ?_⟩
  have hρ0 : 0 < ρ := lt_trans (by norm_num) hρ
  have hσ0 : 0 < σ := hρ0.trans hρσ
  obtain ⟨C, hC, hb⟩ := actualCompletedMatrix_det_bound hρ hρσ hσ1
  have hC0 : 0 < C := lt_of_lt_of_le zero_lt_one hC
  refine ⟨C, hC, fun d c hc => ?_⟩
  let s := (sourceCompletion actualIntegralAnnularCoefficients d ell hell).det
  have hs : (s : ℚ_[7]) ≠ 0 := PadicInt.coe_ne_zero.mpr (hcost d).1
  have hq : (actualNormalizedDeterminant d c : ℚ_[7]) ≠ 0 := by
    exact_mod_cast actualNormalizedDeterminant_ne_zero d c
  have hd : (actualCompletedMatrix d c ell hell).det =
      (actualNormalizedDeterminant d c : ℚ_[7]) * (s : ℚ_[7]) :=
    actualNormalized_source_change d c hc ell hell
  have hn : (actualCompletedMatrix d c ell hell).det ≠ 0 := by
    rw [hd]; exact mul_ne_zero hq hs
  have hl := Real.log_le_log (norm_pos_iff.mpr hn) (hb d c ell hell)
  rw [hd, norm_mul, Real.log_mul (norm_ne_zero_iff.mpr hq) (norm_ne_zero_iff.mpr hs),
    padic_log_norm _ hq, padic_log_norm _ hs, Padic.valuation_ratCast,
    PadicInt.valuation_coe] at hl
  have hsv : s.valuation = a * (d - 6) := (hcost d).2
  rw [hsv, Real.log_mul (by positivity) (by positivity), Real.log_pow,
    Real.log_mul (ne_of_gt hC0) (by positivity), Real.log_pow, Real.log_inv,
    Real.log_pow] at hl
  push_cast at hl
  convert hl using 1 <;> ring

end Zeta7Annulus

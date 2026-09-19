import Zeta7Proof.AuxiliaryProfile
import Zeta7Proof.PNT.ThetaAsymptotic

/-! P8, milestone 4: the weighted profile prime sum.

`Σ_{p ≤ 7d} d f(p/d) log p = Σ_k w_k S(a_k d)` exactly, with `S(X) = Σ_{p≤X} (X-p) log p` and the
hinge decomposition `f = Σ_k w_k (a_k - z)₊` on `z ≥ 0`. All breakpoints and endpoint primes are
accounted for by the hinge form; since the last node is `a = 7` with `f(7) = 0`, no endpoint atom
arises. With `S(X) = X²/2 + o(X²)` (from the ported prime number theorem) and
`Σ_k w_k a_k²/2 = 12325/168`, the sum is `≤ (12325/168 + ε) d²` for large `d`. -/
noncomputable section
set_option autoImplicit false
namespace Zeta7Auxiliary

open Zeta7PNT

/-- The profile prime sum `Σ_{p ≤ 7d} d f(p/d) log p`. -/
def profileSum (d : ℕ) : ℝ :=
  ∑ p ∈ (Finset.range (7 * d + 1)).filter Nat.Prime, (d : ℝ) * profileF ((p : ℝ) / d) * Real.log p

theorem hinge_scaled {d : ℝ} (hd : 0 < d) (a z : ℝ) :
    d * hinge a (z / d) = max (a * d - z) 0 := by
  unfold hinge
  rw [mul_max_of_nonneg _ _ hd.le, mul_zero, mul_sub, mul_div_cancel₀ _ hd.ne', mul_comm d a]

theorem hinge_sum_eq (d : ℕ) (a : ℝ) (ha0 : 0 ≤ a) (ha7 : a ≤ 7) :
    ∑ p ∈ (Finset.range (7 * d + 1)).filter Nat.Prime, max (a * d - p) 0 * Real.log p =
      primeWeightSum (a * d) := by
  have had : 0 ≤ a * d := mul_nonneg ha0 (Nat.cast_nonneg _)
  have hfl : ⌊a * d⌋₊ ≤ 7 * d := by
    apply Nat.floor_le_of_le
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) d]
  rw [primeWeightSum]
  have hsub : (Finset.range (⌊a * d⌋₊ + 1)).filter Nat.Prime ⊆
      (Finset.range (7 * d + 1)).filter Nat.Prime := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_range] at hp ⊢
    exact ⟨by omega, hp.2⟩
  rw [← Finset.sum_subset hsub (f := fun p : ℕ => max (a * d - p) 0 * Real.log p) ?_]
  · refine Finset.sum_congr rfl fun p hp => ?_
    simp only [Finset.mem_filter, Finset.mem_range] at hp
    have hp' : (p : ℝ) ≤ a * d := by
      have : p ≤ ⌊a * d⌋₊ := by omega
      exact (Nat.cast_le.mpr this).trans (Nat.floor_le had)
    rw [max_eq_left (by linarith)]
  · intro p hp hpn
    simp only [Finset.mem_filter, Finset.mem_range, not_and] at hp hpn
    have hlt : ⌊a * d⌋₊ < p := by
      by_contra h
      exact hpn (by omega) hp.2
    have : a * d < p := (Nat.floor_lt had).mp hlt
    rw [max_eq_right (by linarith), zero_mul]

theorem profileSum_eq (d : ℕ) (hd : 0 < d) :
    profileSum d = ∑ k : Fin 9, hingeW k * primeWeightSum (hingeA k * d) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  unfold profileSum
  have e : ∀ p : ℕ, (d : ℝ) * profileF ((p : ℝ) / d) * Real.log p =
      ∑ k : Fin 9, hingeW k * (max (hingeA k * d - p) 0 * Real.log p) := by
    intro p
    rw [profileF_eq_hinge (div_nonneg (Nat.cast_nonneg _) hdR.le), profileHinge_eq_sum,
      Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← hinge_scaled hdR]
    ring
  simp_rw [e]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.mul_sum, hinge_sum_eq d (hingeA k) (hingeA_mem k).1 (hingeA_mem k).2]

theorem hingeW_abs_sum : ∑ k : Fin 9, |hingeW k| ≤ 23 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, hingeW, Matrix.cons_val_zero,
    Matrix.cons_val_succ, abs_neg]
  norm_num [abs_of_nonneg]

theorem hingeA_ge (k : Fin 9) : 1 / 2 ≤ hingeA k := by
  fin_cases k <;> simp [hingeA] <;> norm_num

/-- **Weighted profile prime sum** (the specialized PNT statement):
`Σ_{p ≤ 7d} d f(p/d) log p ≤ (12325/168 + ε) d²` for all large `d`. -/
theorem profileSum_asymptotic {ε : ℝ} (hε : 0 < ε) :
    ∃ D₀ : ℕ, ∀ d : ℕ, D₀ ≤ d → profileSum d ≤ (12325 / 168 + ε) * (d : ℝ) ^ 2 := by
  obtain ⟨X₀, hX₀⟩ := primeWeightSum_asymptotic (ε := ε / (49 * 23)) (by positivity)
  obtain ⟨D₀, hD₀⟩ := exists_nat_gt (2 * |X₀| + 1)
  refine ⟨D₀, fun d hd => ?_⟩
  have hdR : 2 * |X₀| + 1 < d := lt_of_lt_of_le hD₀ (by exact_mod_cast hd)
  have hd0 : 0 < d := by
    have : (0 : ℝ) < d := by linarith [abs_nonneg X₀]
    exact_mod_cast this
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd0
  rw [profileSum_eq d hd0]
  have hk : ∀ k : Fin 9, |hingeW k * primeWeightSum (hingeA k * d) -
      hingeW k * ((hingeA k * d) ^ 2 / 2)| ≤ |hingeW k| * (ε / 23 * (d : ℝ) ^ 2) := by
    intro k
    have ha := hingeA_mem k
    have ha2 := hingeA_ge k
    have hX : X₀ ≤ hingeA k * d := by
      have : |X₀| ≤ hingeA k * d := by nlinarith [abs_nonneg X₀]
      exact (le_abs_self X₀).trans this
    have h1 := hX₀ _ hX
    rw [← mul_sub, abs_mul]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    refine h1.trans ?_
    have ha49 : hingeA k ^ 2 ≤ 49 := by nlinarith
    have : (hingeA k * d) ^ 2 ≤ 49 * (d : ℝ) ^ 2 := by
      rw [mul_pow]; exact mul_le_mul_of_nonneg_right ha49 (sq_nonneg _)
    calc ε / (49 * 23) * (hingeA k * d) ^ 2 ≤ ε / (49 * 23) * (49 * (d : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = ε / 23 * (d : ℝ) ^ 2 := by ring
  have hsum : |∑ k : Fin 9, hingeW k * primeWeightSum (hingeA k * d) -
      ∑ k : Fin 9, hingeW k * ((hingeA k * d) ^ 2 / 2)| ≤ ε * (d : ℝ) ^ 2 := by
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun k _ => hk k).trans ?_
    rw [← Finset.sum_mul]
    have h23 := hingeW_abs_sum
    have : 0 ≤ ε / 23 * (d : ℝ) ^ 2 := by positivity
    calc (∑ k : Fin 9, |hingeW k|) * (ε / 23 * (d : ℝ) ^ 2) ≤ 23 * (ε / 23 * (d : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_right h23 this
      _ = ε * (d : ℝ) ^ 2 := by ring
  have hmain : ∑ k : Fin 9, hingeW k * ((hingeA k * d) ^ 2 / 2) = 12325 / 168 * (d : ℝ) ^ 2 := by
    rw [← hinge_moment, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [hmain] at hsum
  rw [abs_le] at hsum
  linarith [hsum.2]

theorem profileSum_nonneg (d : ℕ) : 0 ≤ profileSum d := by
  unfold profileSum
  refine Finset.sum_nonneg fun p _ => ?_
  have h1 := profileF_nonneg (div_nonneg (Nat.cast_nonneg (α := ℝ) p) (Nat.cast_nonneg (α := ℝ) d))
  have h2 : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  positivity

end Zeta7Auxiliary

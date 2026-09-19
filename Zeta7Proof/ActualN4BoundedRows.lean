import Zeta7Proof.ActualN4ZeroEstimate
import Zeta7Proof.N4BoundedRows

/-! The proved N4 estimate discharges the canonical-row premises for the original blocks. -/
noncomputable section
set_option autoImplicit false
namespace Zeta7Common

theorem rationalGerms_prefix_independent (c : ℚ) (d : ℕ) :
    LinearIndependent ℚ (fun i : BlockIndex d =>
      fun n : Fin (7 * d + 176) => coefficientRow d (rationalGerms c) n.val i) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro b hb i
  by_contra hi
  have hn : b ≠ 0 := by intro h; exact hi (congrFun h i)
  obtain ⟨n, hn, he⟩ := Zeta7Germ.actual_block_zero_estimate c d b hn
  have hz := congrFun hb (⟨n, by omega⟩ : Fin (7 * d + 176))
  apply he
  simpa [coefficientRow, Finset.sum_apply] using hz

theorem rationalGerms_prefix_full (c : ℚ) (d : ℕ) :
    Zeta7Jump.rowSpan (K := ℚ) (coefficientRow d (rationalGerms c))
      (7 * d + 176) = ⊤ := by
  have h := span_flip_eq_top_iff_linearIndependent.mpr (rationalGerms_prefix_independent c d)
  have he : Set.range (fun n : Fin (7 * d + 176) => coefficientRow d (rationalGerms c) n.val) =
      coefficientRow d (rationalGerms c) '' (Finset.range (7 * d + 176) : Set ℕ) := by
    ext v
    constructor
    · rintro ⟨n, rfl⟩
      exact ⟨n.val, Finset.mem_range.mpr n.isLt, rfl⟩
    · rintro ⟨n, hn, rfl⟩
      exact ⟨⟨n, Finset.mem_range.mp hn⟩, rfl⟩
  change Submodule.span ℚ
    (Set.range (fun n : Fin (7 * d + 176) => coefficientRow d (rationalGerms c) n.val)) = ⊤ at h
  rw [he] at h
  exact h

theorem rationalGerms_cutoff_le (c : ℚ) (d : ℕ) :
    Zeta7Jump.cutoff (coefficientRow d (rationalGerms c)) (rationalGerms_fullRank c d) ≤
      7 * d + 176 :=
  Zeta7Jump.cutoff_le_of_full_prefix _ _ _ (rationalGerms_prefix_full c d)

theorem rationalGerms_jumpRow_bounds (c : ℚ) (d : ℕ) (j : Fin (Fintype.card (BlockIndex d))) :
    j.val ≤ Zeta7Jump.fullJumpRow (coefficientRow d (rationalGerms c))
      (rationalGerms_fullRank c d) j ∧
    Zeta7Jump.fullJumpRow (coefficientRow d (rationalGerms c))
      (rationalGerms_fullRank c d) j ≤ j.val + 176 := by
  refine ⟨Zeta7Jump.fullJumpRow_lower _ _ j, ?_⟩
  apply Zeta7Jump.fullJumpRow_upper_of_full_prefix _ _ 176
  have hc : Fintype.card (BlockIndex d) = 7 * d := by
    simp [BlockIndex, TailIndex]
    omega
  simpa only [hc] using rationalGerms_prefix_full c d

theorem actualTailRow_upper (d : ℕ) (c : ℚ) (i : TailIndex d) :
    actualTailRow d c i ≤ d + (i.2.val + d * i.1.val) + 176 :=
  actualTailRow_upper_of_full_prefix d c (rationalGerms_prefix_full c d) i

theorem actualTailExcess_le (d : ℕ) (c : ℚ) (i : TailIndex d) :
    actualTailExcess d c i ≤ 176 :=
  actualTailExcess_le_of_full_prefix d c (rationalGerms_prefix_full c d) i

theorem actualTailRow_lt (d : ℕ) (c : ℚ) (i : TailIndex d) :
    actualTailRow d c i < 7 * d + 176 :=
  actualTailRow_lt_of_full_prefix d c (rationalGerms_prefix_full c d) i

theorem actualTailExcess_sum_le (d : ℕ) (c : ℚ) :
    (∑ i : TailIndex d, (actualTailExcess d c i : ℤ)) ≤ 1056 * (d : ℤ) := by
  calc
    _ ≤ ∑ _i : TailIndex d, (176 : ℤ) :=
      Finset.sum_le_sum (fun i _ => by exact_mod_cast actualTailExcess_le d c i)
    _ = _ := by simp [TailIndex]; ring

/-- The proved row bound gives a uniform linear coordinate error on the same determinant. -/
theorem actualCommonDeterminant_coordinate_error (d : ℕ) (c : ℚ) :
    0 ≤ padicValRat 7 (actualCommonDeterminant d c) - 42 * (d : ℤ) ^ 2 -
      padicValRat 7 (actualNormalizedDeterminant d c) ∧
    padicValRat 7 (actualCommonDeterminant d c) - 42 * (d : ℤ) ^ 2 -
      padicValRat 7 (actualNormalizedDeterminant d c) ≤ 2112 * (d : ℤ) := by
  rw [actualCommonDeterminant_valuation_normalized]
  have hlo : 0 ≤ ∑ i, (actualTailExcess d c i : ℤ) :=
    Finset.sum_nonneg (fun _ _ => Int.natCast_nonneg _)
  have hhi := actualTailExcess_sum_le d c
  constructor <;> linarith

end Zeta7Common

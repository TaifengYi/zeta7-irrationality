import Zeta7Proof.ActualDeterminantNormalization

/-! The canonical-row part of N5. The uniform prefix hypothesis is displayed
explicitly: proving it for 7*d+176 is the remaining N4 zero estimate. -/
noncomputable section
set_option autoImplicit false
namespace Zeta7Jump

theorem fullJumpRow_lt_cutoff {K ι : Type*} [Field K] [Fintype ι]
    (v : ℕ → ι → K) (hv : FullRank v) (i : Fin (Fintype.card ι)) :
    fullJumpRow v hv i < cutoff v hv := by
  classical
  have hm := (pivots (K := K) v (cutoff v hv)).orderEmbOfFin_mem (full_pivots_card v hv) i
  exact Finset.mem_range.mp (Finset.mem_filter.mp hm).1

theorem cutoff_le_of_full_prefix {K ι : Type*} [Field K] [Fintype ι]
    (v : ℕ → ι → K) (hv : FullRank v) (N : ℕ)
    (hN : rowSpan (K := K) v N = ⊤) : cutoff v hv ≤ N := Nat.find_min' hv hN

theorem strictMono_fin_gap {n : ℕ} (f : Fin n → ℕ) (hf : StrictMono f)
    (i j : Fin n) (hij : i ≤ j) : f i + j.val ≤ f j + i.val := by
  have aux : ∀ k : ℕ, ∀ j : Fin n, j.val = i.val + k → f i + k ≤ f j := by
    intro k
    induction k with
    | zero =>
        intro j hj
        have he : j = i := Fin.ext (by omega)
        simp [he]
    | succ k ih =>
        intro j hj
        let p : Fin n := ⟨i.val + k, by have := j.isLt; omega⟩
        have hp := ih p rfl
        have hlt := hf (show p < j by change i.val + k < j.val; omega)
        omega
  have h := aux (j.val - i.val) j (by have : i.val ≤ j.val := hij; omega)
  omega

/-- The empty index case needs no special last-row convention. The supplied
index already implies that the cardinal is positive. -/
theorem fullJumpRow_upper_of_full_prefix {K ι : Type*} [Field K] [Fintype ι]
    (v : ℕ → ι → K) (hv : FullRank v) (C : ℕ)
    (hN : rowSpan (K := K) v (Fintype.card ι + C) = ⊤)
    (i : Fin (Fintype.card ι)) : fullJumpRow v hv i ≤ i.val + C := by
  have hi := i.isLt
  let j : Fin (Fintype.card ι) := ⟨Fintype.card ι - 1, by omega⟩
  have hj := fullJumpRow_lt_cutoff v hv j
  have hc := cutoff_le_of_full_prefix v hv _ hN
  have hg := strictMono_fin_gap (fullJumpRow v hv) (fullJumpRow v hv).strictMono i j
    (by change i.val ≤ Fintype.card ι - 1; omega)
  change _ + (Fintype.card ι - 1) ≤ _ + i.val at hg
  omega

end Zeta7Jump
namespace Zeta7Common

theorem actualTailRow_upper_of_full_prefix (d : ℕ) (c : ℚ)
    (hN : Zeta7Jump.rowSpan (K := ℚ) (coefficientRow d (rationalGerms c)) (7 * d + 176) = ⊤)
    (i : TailIndex d) : actualTailRow d c i ≤ d + (i.2.val + d * i.1.val) + 176 := by
  apply Zeta7Jump.fullJumpRow_upper_of_full_prefix _ (rationalGerms_fullRank c d) 176
  have hc : Fintype.card (BlockIndex d) = 7 * d := by
    simp [BlockIndex, TailIndex]
    omega
  simpa only [hc] using hN

theorem actualTailExcess_le_of_full_prefix (d : ℕ) (c : ℚ)
    (hN : Zeta7Jump.rowSpan (K := ℚ) (coefficientRow d (rationalGerms c)) (7 * d + 176) = ⊤)
    (i : TailIndex d) : actualTailExcess d c i ≤ 176 := by
  have h := actualTailRow_upper_of_full_prefix d c hN i
  unfold actualTailExcess
  omega

theorem actualTailRow_lt_of_full_prefix (d : ℕ) (c : ℚ)
    (hN : Zeta7Jump.rowSpan (K := ℚ) (coefficientRow d (rationalGerms c)) (7 * d + 176) = ⊤)
    (i : TailIndex d) : actualTailRow d c i < 7 * d + 176 := by
  exact (Zeta7Jump.fullJumpRow_lt_cutoff _ (rationalGerms_fullRank c d)
    (blockOrder d (.inr i))).trans_le
      (Zeta7Jump.cutoff_le_of_full_prefix _ (rationalGerms_fullRank c d) _ hN)

end Zeta7Common

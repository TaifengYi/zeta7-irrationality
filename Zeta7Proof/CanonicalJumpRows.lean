import Mathlib

/-! Canonical coefficient-row pivots, obtained by scanning every row in order.
The existence of enough pivots is a separate full-rank hypothesis. -/

set_option autoImplicit false
noncomputable section
open Set Submodule
namespace Zeta7Jump
attribute [local instance] Classical.propDecidable

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def rowSpan (v : ℕ → V) (N : ℕ) : Submodule K V :=
  span K (v '' (Finset.range N : Set ℕ))

def pivots (v : ℕ → V) (N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range N).filter (fun n => v n ∉ rowSpan (K := K) v n)

theorem pivots_succ (v : ℕ → V) (N : ℕ) :
    pivots (K := K) v (N + 1) =
      if v N ∈ rowSpan (K := K) v N then pivots (K := K) v N
      else insert N (pivots (K := K) v N) := by
  classical
  simp only [pivots, Finset.range_add_one, Finset.filter_insert]
  split_ifs <;> rfl

theorem pivots_independent_span (v : ℕ → V) (N : ℕ) :
    LinearIndepOn K v (pivots (K := K) v N : Set ℕ) ∧
      span K (v '' (pivots (K := K) v N : Set ℕ)) = rowSpan (K := K) v N := by
  classical
  induction N with
  | zero => simp [pivots, rowSpan]
  | succ N ih =>
    have hs : rowSpan (K := K) v (N + 1) =
        span K (insert (v N) (v '' (Finset.range N : Set ℕ))) := by
      rw [rowSpan, Finset.range_add_one, Finset.coe_insert, Set.image_insert_eq]
    rw [pivots_succ]
    split_ifs with h
    · refine ⟨ih.1, ?_⟩
      rw [ih.2, hs, span_insert_eq_span h]
      rfl
    · refine ⟨?_, ?_⟩
      · simpa only [Finset.coe_insert] using ih.1.insert (by rwa [ih.2])
      · rw [Finset.coe_insert, Set.image_insert_eq, span_insert, ih.2, hs, span_insert]
        rfl

theorem pivots_card (v : ℕ → V) (N : ℕ) :
    (pivots (K := K) v N).card = Module.finrank K (rowSpan (K := K) v N) := by
  classical
  have h := pivots_independent_span (K := K) v N
  have hc := finrank_span_eq_card h.1
  have hr : Set.range (fun x : (pivots (K := K) v N : Set ℕ) => v x) =
      v '' (pivots (K := K) v N : Set ℕ) := by
    ext x
    simp
  rw [hr, h.2] at hc
  simpa using hc.symm

/-- The increasing enumeration of precisely the rank-jump rows in a prefix. -/
def jumpRow (v : ℕ → V) (N : ℕ) : Fin (pivots (K := K) v N).card ↪o ℕ :=
  (pivots (K := K) v N).orderEmbOfFin rfl

theorem jumpRow_isPivot (v : ℕ → V) (N : ℕ)
    (i : Fin (pivots (K := K) v N).card) :
    v (jumpRow (K := K) v N i) ∉ rowSpan (K := K) v (jumpRow (K := K) v N i) := by
  classical
  exact (Finset.mem_filter.mp ((pivots (K := K) v N).orderEmbOfFin_mem rfl i)).2

theorem jumpRow_independent (v : ℕ → V) (N : ℕ) :
    LinearIndependent K (fun i => v (jumpRow (K := K) v N i)) := by
  exact (pivots_independent_span (K := K) v N).1.comp
    ((pivots (K := K) v N).orderIsoOfFin rfl) (Equiv.injective _)

theorem rowSpan_mono (v : ℕ → V) {N M : ℕ} (h : N ≤ M) :
    rowSpan (K := K) v N ≤ rowSpan (K := K) v M :=
  span_mono (Set.image_mono (by simpa using Finset.range_mono h))

theorem rank_jump_iff (v : ℕ → V) (N : ℕ) :
    Module.finrank K (rowSpan (K := K) v (N + 1)) =
      Module.finrank K (rowSpan (K := K) v N) + 1 ↔
        v N ∉ rowSpan (K := K) v N := by
  classical
  rw [← pivots_card, ← pivots_card, pivots_succ]
  have hn : N ∉ pivots (K := K) v N := by simp [pivots]
  split_ifs with h <;> simp [h, Finset.card_insert_of_notMem hn]

theorem pivots_stable_of_full (v : ℕ → V) {N M : ℕ}
    (hN : rowSpan (K := K) v N = ⊤) (hNM : N ≤ M) :
    pivots (K := K) v M = pivots (K := K) v N := by
  classical
  ext n
  simp only [pivots, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hnM, hn⟩
    refine ⟨?_, hn⟩
    by_contra hge
    have hs := rowSpan_mono (K := K) v (Nat.le_of_not_gt hge)
    rw [hN] at hs
    exact hn (hs (by trivial))
  · rintro ⟨hnN, hn⟩
    exact ⟨hnN.trans_le hNM, hn⟩

theorem exists_rowSpan_eq_top [Module.Finite K V] (v : ℕ → V)
    (hv : span K (Set.range v) = ⊤) :
    ∃ N, rowSpan (K := K) v N = ⊤ := by
  classical
  have hfg : (span K (Set.range v)).FG := by rw [hv]; exact Module.Finite.fg_top
  obtain ⟨s, hs, heq⟩ := (fg_span_iff_fg_span_finset_subset _).mp hfg
  choose f hf using (fun x : s => hs x.property)
  let N := (Finset.univ.sup fun x : s => f x) + 1
  refine ⟨N, top_unique ?_⟩
  rw [← hv, heq]
  apply span_le.mpr
  intro x hx
  apply subset_span
  refine ⟨f ⟨x, hx⟩, ?_, hf ⟨x, hx⟩⟩
  simp only [Finset.mem_coe, Finset.mem_range]
  exact Nat.lt_succ_of_le (Finset.le_sup (f := fun x : s => f x) (Finset.mem_univ _))

section Square
variable {ι : Type*} [Fintype ι]

/-- Full row span is an explicit finite-dimensional independence obligation. -/
def FullRank (v : ℕ → ι → K) : Prop := ∃ N, rowSpan (K := K) v N = ⊤

def cutoff (v : ℕ → ι → K) (hv : FullRank v) : ℕ := Nat.find hv

omit [Fintype ι] in
theorem cutoff_full (v : ℕ → ι → K) (hv : FullRank v) :
    rowSpan (K := K) v (cutoff v hv) = ⊤ := Nat.find_spec hv

theorem full_pivots_card (v : ℕ → ι → K) (hv : FullRank v) :
    (pivots (K := K) v (cutoff v hv)).card = Fintype.card ι := by
  rw [pivots_card, cutoff_full]
  simp

def fullJumpRow (v : ℕ → ι → K) (hv : FullRank v) : Fin (Fintype.card ι) ↪o ℕ :=
  (pivots (K := K) v (cutoff v hv)).orderEmbOfFin (full_pivots_card v hv)

def jumpMatrix (v : ℕ → ι → K) (hv : FullRank v) : Matrix ι ι K :=
  fun i => v (fullJumpRow v hv (Fintype.equivFin ι i))

theorem fullJumpRow_independent (v : ℕ → ι → K) (hv : FullRank v) :
    LinearIndependent K (fun i => v (fullJumpRow v hv i)) :=
  (pivots_independent_span (K := K) v (cutoff v hv)).1.comp
    ((pivots (K := K) v (cutoff v hv)).orderIsoOfFin (full_pivots_card v hv))
    (Equiv.injective _)

theorem fullJumpRow_lower (v : ℕ → ι → K) (hv : FullRank v)
    (i : Fin (Fintype.card ι)) : i.val ≤ fullJumpRow v hv i := by
  have aux : ∀ n, ∀ j : Fin (Fintype.card ι), j.val = n → n ≤ fullJumpRow v hv j := by
    intro n
    induction n with
    | zero => intro j hj; exact Nat.zero_le _
    | succ n ih =>
      intro j hj
      let k : Fin (Fintype.card ι) := ⟨n, by have := j.isLt; omega⟩
      have hk := ih k rfl
      have hlt := (fullJumpRow v hv).strictMono (show k < j by change n < j.val; omega)
      omega
  exact aux i.val i rfl

theorem fullJumpRow_initial (v : ℕ → ι → K) (hv : FullRank v) (d : ℕ)
    (hd : ∀ n < d, n ∈ pivots (K := K) v (cutoff v hv))
    (i : Fin (Fintype.card ι)) (hi : i.val < d) : fullJumpRow v hv i = i.val := by
  have aux : ∀ n, ∀ i : Fin (Fintype.card ι), i.val = n → n < d →
      fullJumpRow v hv i = n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro i hin hnd
      have hm := hd n hnd
      have hr := (pivots (K := K) v (cutoff v hv)).range_orderEmbOfFin
        (full_pivots_card v hv)
      obtain ⟨j, hj⟩ : n ∈ Set.range (fullJumpRow v hv) := by rwa [fullJumpRow, hr]
      have hjle : j.val ≤ n := by simpa [hj] using fullJumpRow_lower v hv j
      by_cases hji : j = i
      · simpa [hji] using hj
      · have hjlt : j.val < n := by
          have : j.val ≠ i.val := fun heq => hji (Fin.ext heq)
          omega
        have hprev := ih j.val hjlt j rfl (by omega)
        omega
  exact aux i.val i rfl hi

theorem jumpMatrix_det_ne_zero (v : ℕ → ι → K) (hv : FullRank v) :
    (jumpMatrix v hv).det ≠ 0 := by
  have hi := (pivots_independent_span (K := K) v (cutoff v hv)).1
  have hj := hi.comp
    ((pivots (K := K) v (cutoff v hv)).orderIsoOfFin (full_pivots_card v hv))
    (Equiv.injective _)
  have hm : LinearIndependent K (jumpMatrix v hv).row :=
    hj.comp (Fintype.equivFin ι) (Equiv.injective _)
  exact ((Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.linearIndependent_rows_iff_isUnit.mp hm)).ne_zero

end Square
end Zeta7Jump

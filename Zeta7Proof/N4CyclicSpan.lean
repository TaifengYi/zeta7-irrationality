import Zeta7Proof.N4ConnectionSeven

/-! The actual cyclic span, its stability, and independence of its first
rank-many derivative vectors. No cyclic-rank premise is assumed. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
open scoped RatFunc LaurentSeries
namespace Zeta7Germ

def cyclicSpan (z : SevenCoordinates) : Submodule (RatFunc ℂ) SevenCoordinates :=
  Submodule.span (RatFunc ℂ) (Set.range (fun n : ℕ => connection7^[n] z))

def derivativePrefix (z : SevenCoordinates) (n : ℕ) :
    Submodule (RatFunc ℂ) SevenCoordinates :=
  Submodule.span (RatFunc ℂ) (Set.range (fun i : Fin n => connection7^[i.val] z))

theorem connection7_zero : connection7 0 = 0 := by
  simp [connection7, connection4, connection3, primitiveCoupling, primitiveMultiplier]
  rfl

theorem iterate_mem_cyclicSpan (z : SevenCoordinates) (n : ℕ) :
    connection7^[n] z ∈ cyclicSpan z := Submodule.subset_span ⟨n, rfl⟩

theorem self_mem_cyclicSpan (z : SevenCoordinates) : z ∈ cyclicSpan z :=
  iterate_mem_cyclicSpan z 0

theorem cyclicSpan_stable (z : SevenCoordinates) :
    ∀ w ∈ cyclicSpan z, connection7 w ∈ cyclicSpan z := by
  intro w hw
  induction hw using Submodule.span_induction with
  | mem w hw =>
      obtain ⟨n, rfl⟩ := hw
      rw [← Function.iterate_succ_apply' connection7]
      exact iterate_mem_cyclicSpan z (n + 1)
  | zero => rw [connection7_zero]; exact (cyclicSpan z).zero_mem
  | add w v _ _ hw hv => rw [connection7_add]; exact (cyclicSpan z).add_mem hw hv
  | smul a w hw ih =>
      rw [connection7_leibniz]
      exact (cyclicSpan z).add_mem ((cyclicSpan z).smul_mem _ hw)
        ((cyclicSpan z).smul_mem _ ih)

theorem cyclicSpan_minimal (z : SevenCoordinates)
    (S : Submodule (RatFunc ℂ) SevenCoordinates)
    (hs : ∀ w ∈ S, connection7 w ∈ S) (hz : z ∈ S) : cyclicSpan z ≤ S := by
  apply Submodule.span_le.mpr
  rintro _ ⟨n, rfl⟩
  induction n with
  | zero => exact hz
  | succ n ih =>
      change connection7^[n + 1] z ∈ S
      rw [Function.iterate_succ_apply']
      exact hs _ ih

theorem cyclicSpan_contains_four (z : SevenCoordinates)
    (hz : z.1.2 ≠ 0 ∨ z.2 ≠ 0) : fourRestriction (cyclicSpan z) = ⊤ :=
  fourRestriction_eq_top_of_nonrational (cyclicSpan z) (cyclicSpan_stable z)
    z (self_mem_cyclicSpan z) hz

theorem sevenEval_iterate (c : ℚ) (z : SevenCoordinates) (n : ℕ) :
    sevenEval c (connection7^[n] z) = laurentD^[n] (sevenEval c z) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        ← sevenEval_derivative, ih]

theorem derivativePrefix_le (z : SevenCoordinates) (n : ℕ) :
    derivativePrefix z n ≤ cyclicSpan z := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact iterate_mem_cyclicSpan z i.val

theorem iterate_mem_derivativePrefix (z : SevenCoordinates) (n m : ℕ) (hm : m < n) :
    connection7^[m] z ∈ derivativePrefix z n := Submodule.subset_span ⟨⟨m, hm⟩, rfl⟩

theorem derivativePrefix_stable_of_next_mem (z : SevenCoordinates) (n : ℕ)
    (hn : connection7^[n] z ∈ derivativePrefix z n) :
    ∀ w ∈ derivativePrefix z n, connection7 w ∈ derivativePrefix z n := by
  intro w hw
  induction hw using Submodule.span_induction with
  | mem w hw =>
      obtain ⟨i, rfl⟩ := hw
      rw [← Function.iterate_succ_apply' connection7]
      by_cases hi : i.val + 1 < n
      · exact iterate_mem_derivativePrefix z n _ hi
      · have he : i.val + 1 = n := by have := i.isLt; omega
        simpa [he] using hn
  | zero => rw [connection7_zero]; exact (derivativePrefix z n).zero_mem
  | add w v _ _ hw hv =>
      rw [connection7_add]; exact (derivativePrefix z n).add_mem hw hv
  | smul a w hw ih =>
      rw [connection7_leibniz]
      exact (derivativePrefix z n).add_mem ((derivativePrefix z n).smul_mem _ hw)
        ((derivativePrefix z n).smul_mem _ ih)

/-- The first dependence makes the entire prefix stable, including n=0. -/
theorem derivativePrefix_eq_cyclicSpan_of_next_mem (z : SevenCoordinates) (n : ℕ)
    (hn : connection7^[n] z ∈ derivativePrefix z n) :
    derivativePrefix z n = cyclicSpan z := by
  apply le_antisymm (derivativePrefix_le z n)
  apply cyclicSpan_minimal z _ (derivativePrefix_stable_of_next_mem z n hn)
  cases n with
  | zero => exact hn
  | succ n => exact iterate_mem_derivativePrefix z (n + 1) 0 (Nat.zero_lt_succ n)

theorem derivativePrefix_finrank_le (z : SevenCoordinates) (n : ℕ) :
    Module.finrank (RatFunc ℂ) (derivativePrefix z n) ≤ n := by
  simpa [derivativePrefix, Set.finrank] using
    (finrank_range_le_card (R := RatFunc ℂ) (fun i : Fin n => connection7^[i.val] z))

/-- The derivative rows are proved independent up to the actual cyclic rank. -/
theorem cyclic_derivatives_independent (z : SevenCoordinates) (n : ℕ)
    (hn : n ≤ Module.finrank (RatFunc ℂ) (cyclicSpan z)) :
    LinearIndependent (RatFunc ℂ) (fun i : Fin n => connection7^[i.val] z) := by
  induction n with
  | zero => exact linearIndependent_empty_type
  | succ n ih =>
      apply linearIndependent_finSucc'.mpr
      constructor
      · exact ih (by omega)
      · intro hm
        have hmem : connection7^[n] z ∈ derivativePrefix z n := hm
        have he := derivativePrefix_eq_cyclicSpan_of_next_mem z n hmem
        have hd := derivativePrefix_finrank_le z n
        rw [he] at hd
        omega

theorem cyclic_rank_le_seven (z : SevenCoordinates) :
    Module.finrank (RatFunc ℂ) (cyclicSpan z) ≤ 7 := by
  simpa [SevenCoordinates, FourCoordinates] using (cyclicSpan z).finrank_le

end Zeta7Germ

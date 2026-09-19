import Zeta7Proof.GermLocalCalculus

/-! The minimal-support lemma used on the projected relation kernel in N3. -/
noncomputable section
set_option autoImplicit false
open scoped RatFunc
namespace Zeta7Germ

theorem exists_constant_vector {n : ℕ} (S : Submodule (RatFunc ℂ) (Fin n → RatFunc ℂ))
    (hS : S ≠ ⊥)
    (hstable : ∀ v ∈ S, (fun i => rationalD (v i)) ∈ S) :
    ∃ a : Fin n → ℂ, a ≠ 0 ∧ (fun i => RatFunc.C (a i)) ∈ S := by
  classical
  let supp (v : Fin n → RatFunc ℂ) := Finset.univ.filter (fun i => v i ≠ 0)
  have hex : ∃ k : ℕ, ∃ v ∈ S, v ≠ 0 ∧ (supp v).card = k := by
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS
    exact ⟨_, v, hv, hv0, rfl⟩
  obtain ⟨v, hvS, hv0, hvmin⟩ := Nat.find_spec hex
  have hmin (w : Fin n → RatFunc ℂ) (hwS : w ∈ S) (hw0 : w ≠ 0) :
      (supp v).card ≤ (supp w).card := by
    rw [hvmin]
    exact Nat.find_min' hex ⟨w, hwS, hw0, rfl⟩
  obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
    by_contra h
    apply hv0
    ext j
    simpa using not_exists.mp h j
  let w : Fin n → RatFunc ℂ := (v j)⁻¹ • v
  have hwS : w ∈ S := S.smul_mem _ hvS
  have hwj : w j = 1 := by simp [w, hj]
  have hwsupp : supp w = supp v := by
    ext i
    simp [supp, w, hj]
  let dw : Fin n → RatFunc ℂ := fun i => rationalD (w i)
  have hdwS : dw ∈ S := hstable w hwS
  have hdz : dw = 0 := by
    by_contra hne
    have hsub : supp dw ⊂ supp w := by
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨?_, ?_⟩
      · intro i hi
        simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and] at *
        intro hwi
        exact hi (by simp [dw, hwi])
      · intro he
        have hjw : j ∈ supp w := by simp [supp, hwj]
        rw [← he] at hjw
        simpa [supp, dw, hwj] using hjw
    have hlt := Finset.card_lt_card hsub
    rw [hwsupp] at hlt
    exact (not_lt_of_ge (hmin dw hdwS hne)) hlt
  have hconst : ∀ i, ∃ a : ℂ, w i = RatFunc.C a := by
    intro i
    apply (rationalD_eq_zero_iff _).mp
    exact congrFun hdz i
  choose a ha using hconst
  refine ⟨a, ?_, ?_⟩
  · intro ha0
    have hh := ha j
    rw [hwj, ha0] at hh
    simpa using hh
  · have he : (fun i => RatFunc.C (a i)) = w := funext fun i => (ha i).symm
    rw [he]
    exact hwS

end Zeta7Germ

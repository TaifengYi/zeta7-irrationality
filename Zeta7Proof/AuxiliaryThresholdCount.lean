import Mathlib

/-! Finite threshold counting for four simultaneous integral caps. -/
noncomputable section
set_option autoImplicit false
namespace Zeta7Auxiliary

def thresholdMass {ι : Type*} [Fintype ι] (h : ℕ) (e : ι → ℕ) : ℕ := by
  classical
  exact ∑ k : Fin 4, min h ((Finset.univ.filter (fun j => k.val < e j)).card)

theorem cap_eq_layers (n : ℕ) (hn : n ≤ 4) :
    n = ∑ k : Fin 4, if k.val < n then 1 else 0 := by
  interval_cases n <;> decide

theorem thresholdMass_mono {ι : Type*} [Fintype ι] (e : ι → ℕ) {h r : ℕ} (hr : h ≤ r) :
    thresholdMass h e ≤ thresholdMass r e := by
  apply Finset.sum_le_sum
  intro k _
  exact min_le_min_right _ hr

theorem sum_caps_le_thresholdMass {ι : Type*} [Fintype ι] (e : ι → ℕ)
    (he : ∀ j, e j ≤ 4) (s : Finset ι) :
    (∑ j ∈ s, e j) ≤ thresholdMass s.card e := by
  classical
  calc
    _ = ∑ j ∈ s, ∑ k : Fin 4, if k.val < e j then 1 else 0 := by
      apply Finset.sum_congr rfl; intro j _; exact cap_eq_layers (e j) (he j)
    _ = ∑ k : Fin 4, (s.filter (fun j => k.val < e j)).card := by
      rw [Finset.sum_comm]
      simp
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro k _
      apply le_min
      · exact Finset.card_filter_le _ _
      · apply Finset.card_le_card
        intro j hj
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, (Finset.mem_filter.mp hj).2⟩

theorem permutation_bad_card {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (π : Equiv.Perm ι) :
    (Finset.univ.filter (fun j => π j ∈ s)).card = s.card := by
  classical
  have he : (Finset.univ.filter (fun j => π j ∈ s)).image π = s := by
    ext i
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨j, hj, rfl⟩; exact hj
    · intro hi; exact ⟨π.symm i, by simpa, π.apply_symm_apply i⟩
  rw [← Finset.card_image_of_injective _ π.injective, he]

end Zeta7Auxiliary

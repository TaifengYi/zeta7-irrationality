import Zeta7Proof.ActualSevenFrameIndependence

/-! N4: the actual rank-four extension has no stable complement to its
rational line. The proof uses the already proved universal N1 obstruction. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open scoped RatFunc LaurentSeries
namespace Zeta7Germ

abbrev FourCoordinates := RatFunc ℂ × (Fin 3 → RatFunc ℂ)

def connection4 (z : FourCoordinates) : FourCoordinates :=
  (rationalD z.1 + z.2 2 * R, connection3 z.2)

def rationalLine : Submodule (RatFunc ℂ) FourCoordinates :=
  LinearMap.ker (LinearMap.snd (RatFunc ℂ) (RatFunc ℂ) (Fin 3 → RatFunc ℂ))

theorem mem_rationalLine (z : FourCoordinates) : z ∈ rationalLine ↔ z.2 = 0 := Iff.rfl

theorem connection3_add (v w : Fin 3 → RatFunc ℂ) :
    connection3 (v + w) = connection3 v + connection3 w := by
  ext i
  fin_cases i <;> simp [connection3] <;> ring

theorem connection4_add (z w : FourCoordinates) :
    connection4 (z + w) = connection4 z + connection4 w := by
  apply Prod.ext
  · simp [connection4]; ring
  · exact connection3_add _ _

theorem connection4_leibniz (a : RatFunc ℂ) (z : FourCoordinates) :
    connection4 (a • z) = rationalD a • z + a • connection4 z := by
  apply Prod.ext
  · simp [connection4, Derivation.leibniz, smul_eq_mul]; ring
  · exact connection3_leibniz _ _

def fourEval (c : ℚ) (z : FourCoordinates) : ℂ⸨X⸩ := embed z.1 + jetEval c z.2

theorem fourEval_derivative (c : ℚ) (z : FourCoordinates) :
    laurentD (fourEval c z) = fourEval c (connection4 z) := by
  simp only [fourEval, map_add, ← embed_rationalD, jetEval_derivative, connection4]
  ring

theorem fourEval_injective (c : ℚ) : Function.Injective (fourEval c) := by
  intro z w he
  have hrel : embed (z.1 - w.1) + jetEval c (z.2 - w.2) = 0 := by
    have hj : jetEval c (z.2 - w.2) = jetEval c z.2 - jetEval c w.2 := by
      simp [jetEval]; ring
    rw [map_sub, hj]
    dsimp [fourEval] at he
    linear_combination he
  obtain ⟨hr, hv⟩ := actual_four_jet_relation c _ _ hrel
  exact Prod.ext (sub_eq_zero.mp hr) (sub_eq_zero.mp hv)

def jetProjection (S : Submodule (RatFunc ℂ) FourCoordinates) :
    Submodule (RatFunc ℂ) (Fin 3 → RatFunc ℂ) where
  carrier := {v | ∃ r, (r, v) ∈ S}
  zero_mem' := ⟨0, S.zero_mem⟩
  add_mem' := by
    rintro v w ⟨r, hr⟩ ⟨s, hs⟩
    exact ⟨r + s, S.add_mem hr hs⟩
  smul_mem' := by
    rintro a v ⟨r, hr⟩
    exact ⟨a * r, S.smul_mem a hr⟩

theorem jetProjection_stable (S : Submodule (RatFunc ℂ) FourCoordinates)
    (hs : ∀ z ∈ S, connection4 z ∈ S) :
    ∀ v ∈ jetProjection S, connection3 v ∈ jetProjection S := by
  rintro v ⟨r, hr⟩
  exact ⟨rationalD r + v 2 * R, hs (r, v) hr⟩

/-- A nonzero rational vector generates the entire rational line. -/
theorem rationalLine_le_of_nonzero (S : Submodule (RatFunc ℂ) FourCoordinates)
    (a : RatFunc ℂ) (ha : a ≠ 0) (hm : (a, 0) ∈ S) : rationalLine ≤ S := by
  intro z hz
  have hz0 := (mem_rationalLine z).mp hz
  have h := S.smul_mem (z.1 / a) hm
  have he : (z.1 / a) • (a, (0 : Fin 3 → RatFunc ℂ)) = z := by
    apply Prod.ext
    · simp [smul_eq_mul, ha]
    · simpa using hz0.symm
  rwa [he] at h

/-- Stability of three basis lifts would give La=-R; N1 excludes it.
There is no assumed splitting or differential-module category here. -/
theorem connection4_no_complement (S : Submodule (RatFunc ℂ) FourCoordinates)
    (hs : ∀ z ∈ S, connection4 z ∈ S)
    (hp : jetProjection S = ⊤)
    (hz : ∀ a : RatFunc ℂ, (a, 0) ∈ S → a = 0) : False := by
  have hmem (v : Fin 3 → RatFunc ℂ) : v ∈ jetProjection S := by rw [hp]; trivial
  obtain ⟨a, ha⟩ := hmem ![1, 0, 0]
  obtain ⟨b, hb⟩ := hmem ![0, 1, 0]
  obtain ⟨f, hf⟩ := hmem ![0, 0, 1]
  have hda : rationalD a = b := by
    have h := S.sub_mem (hs _ ha) hb
    have he : connection4 (a, ![1, 0, 0]) - (b, ![0, 1, 0]) =
        (rationalD a - b, (0 : Fin 3 → RatFunc ℂ)) := by
      ext i <;> simp [connection4, connection3]
    rw [he] at h
    exact sub_eq_zero.mp (hz _ h)
  have hdb : rationalD b = f := by
    have h := S.sub_mem (hs _ hb) hf
    have he : connection4 (b, ![0, 1, 0]) - (f, ![0, 0, 1]) =
        (rationalD b - f, (0 : Fin 3 → RatFunc ℂ)) := by
      ext i <;> simp [connection4, connection3]
    rw [he] at h
    exact sub_eq_zero.mp (hz _ h)
  have hdf : rationalD f + R - rationalD V / 2 * a - V * b = 0 := by
    have h := S.sub_mem (S.sub_mem (hs _ hf) (S.smul_mem (rationalD V / 2) ha))
      (S.smul_mem V hb)
    have he : connection4 (f, ![0, 0, 1]) - (rationalD V / 2) • (a, ![1, 0, 0]) -
        V • (b, ![0, 1, 0]) =
        (rationalD f + R - rationalD V / 2 * a - V * b, (0 : Fin 3 → RatFunc ℂ)) := by
      apply Prod.ext
      · simp [connection4, smul_eq_mul]
      · ext i; fin_cases i <;> simp [connection4, connection3, smul_eq_mul]
    rw [he] at h
    exact hz _ h
  have hL : L a = ((-1 : Polynomial ℂ) : RatFunc ℂ) * R := by
    simp only [L, hda, hdb]
    norm_num
    linear_combination hdf
  exact no_rational_inhomogeneous_solution a (-1) (by simp) (by simp) hL

theorem connection4_submodule_classification
    (S : Submodule (RatFunc ℂ) FourCoordinates)
    (hs : ∀ z ∈ S, connection4 z ∈ S) :
    S = ⊥ ∨ S = rationalLine ∨ S = ⊤ := by
  rcases connection3_irreducible (jetProjection S) (jetProjection_stable S hs) with hp | hp
  · have hle : S ≤ rationalLine := by
      intro z hz
      have hm : z.2 ∈ jetProjection S := ⟨z.1, hz⟩
      rw [hp] at hm
      exact hm
    by_cases hzero : ∀ a : RatFunc ℂ, (a, 0) ∈ S → a = 0
    · left
      apply le_antisymm _ bot_le
      intro z hz
      have hv := (mem_rationalLine z).mp (hle hz)
      have hr := hzero z.1 (by rw [← hv]; exact hz)
      exact Prod.ext hr hv
    · push_neg at hzero
      obtain ⟨a, hm, ha⟩ := hzero
      exact Or.inr (Or.inl (le_antisymm hle (rationalLine_le_of_nonzero S a ha hm)))
  · right; right
    have hex : ∃ a : RatFunc ℂ, (a, 0) ∈ S ∧ a ≠ 0 := by
      by_contra h
      push_neg at h
      exact connection4_no_complement S hs hp h
    obtain ⟨a, hm, ha⟩ := hex
    have hl := rationalLine_le_of_nonzero S a ha hm
    apply top_unique
    intro z _
    have hproj : z.2 ∈ jetProjection S := by rw [hp]; trivial
    obtain ⟨r, hr⟩ := hproj
    have hh : (z.1 - r, (0 : Fin 3 → RatFunc ℂ)) ∈ S := hl rfl
    have hsum := S.add_mem hh hr
    simpa using hsum

end Zeta7Germ

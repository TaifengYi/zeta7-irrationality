import Zeta7Proof.RankThreeIrreducible
import Zeta7Proof.ActualLaurentConnection

/-! Independence of the actual four jets. The rational jet-relation subspace
is stable in rank three; irreducibility and N1 force that subspace to vanish. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open scoped RatFunc LaurentSeries
namespace Zeta7Germ

theorem rational_smul (a : RatFunc ℂ) (f : ℂ⸨X⸩) : a • f = embed a * f :=
  Algebra.smul_def a f

theorem laurentL_embed (f : RatFunc ℂ) : laurentL (embed f) = embed (L f) := by
  simp [laurentL, L, embed_rationalD, map_ofNat]

theorem actualH_not_rational (c : ℚ) (f : RatFunc ℂ) : actualH c ≠ embed f := by
  intro he
  have hl := actualH_laurentL c
  rw [he, laurentL_embed] at hl
  have hr := embed_injective hl
  apply no_rational_inhomogeneous_solution f (1 : Polynomial ℂ) (by simp) (by simp)
  simpa using hr

def jetEval (c : ℚ) (v : Fin 3 → RatFunc ℂ) : ℂ⸨X⸩ :=
  embed (v 0) * actualH c + embed (v 1) * laurentD (actualH c) +
    embed (v 2) * laurentD (laurentD (actualH c))

theorem jetEval_add (c : ℚ) (v w : Fin 3 → RatFunc ℂ) :
    jetEval c (v + w) = jetEval c v + jetEval c w := by
  simp [jetEval]
  ring

theorem jetEval_smul (c : ℚ) (a : RatFunc ℂ) (v : Fin 3 → RatFunc ℂ) :
    jetEval c (a • v) = embed a * jetEval c v := by
  simp [jetEval, Pi.smul_apply, smul_eq_mul]
  ring

theorem jetEval_derivative (c : ℚ) (v : Fin 3 → RatFunc ℂ) :
    laurentD (jetEval c v) = jetEval c (connection3 v) + embed (v 2 * R) := by
  have h := actualH_laurentL c
  dsimp [laurentL] at h
  simp only [jetEval, connection3, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val, Matrix.head_cons, Matrix.tail_cons,
    map_add, map_mul, map_div₀, map_ofNat,
    Derivation.leibniz, smul_eq_mul, ← embed_rationalD]
  linear_combination embed (v 2) * h

def rationalJetRelations (c : ℚ) : Submodule (RatFunc ℂ) (Fin 3 → RatFunc ℂ) where
  carrier := {v | ∃ r : RatFunc ℂ, jetEval c v = embed r}
  zero_mem' := ⟨0, by simp [jetEval]⟩
  add_mem' := by
    rintro v w ⟨r, hr⟩ ⟨s, hs⟩
    exact ⟨r + s, by rw [jetEval_add, hr, hs, map_add]⟩
  smul_mem' := by
    rintro a v ⟨r, hr⟩
    exact ⟨a * r, by rw [jetEval_smul, hr, map_mul]⟩

theorem rationalJetRelations_stable (c : ℚ) :
    ∀ v ∈ rationalJetRelations c, connection3 v ∈ rationalJetRelations c := by
  rintro v ⟨r, hr⟩
  refine ⟨rationalD r - v 2 * R, ?_⟩
  have he := jetEval_derivative c v
  rw [hr, ← embed_rationalD] at he
  rw [map_sub]
  linear_combination -he

theorem rationalJetRelations_eq_bot (c : ℚ) : rationalJetRelations c = ⊥ := by
  rcases connection3_irreducible (rationalJetRelations c) (rationalJetRelations_stable c) with h | h
  · exact h
  · have hm : (![1, 0, 0] : Fin 3 → RatFunc ℂ) ∈ rationalJetRelations c := by rw [h]; trivial
    obtain ⟨r, hr⟩ := hm
    have he : actualH c = embed r := by simpa [jetEval] using hr
    exact (actualH_not_rational c r he).elim

theorem actual_four_jet_relation (c : ℚ) (r : RatFunc ℂ) (v : Fin 3 → RatFunc ℂ)
    (he : embed r + jetEval c v = 0) : r = 0 ∧ v = 0 := by
  have hm : v ∈ rationalJetRelations c := by
    refine ⟨-r, ?_⟩
    rw [map_neg]
    linear_combination he
  rw [rationalJetRelations_eq_bot] at hm
  have hv : v = 0 := hm
  refine ⟨?_, hv⟩
  rw [hv] at he
  simp [jetEval] at he
  exact he

def actualFourJets (c : ℚ) : Fin 4 → ℂ⸨X⸩ :=
  ![1, actualH c, laurentD (actualH c), laurentD (laurentD (actualH c))]

theorem actualFourJets_independent (c : ℚ) : LinearIndependent (RatFunc ℂ) (actualFourJets c) := by
  apply Fintype.linearIndependent_iff.mpr
  intro a ha i
  have hrel : embed (a 0) + jetEval c ![a 1, a 2, a 3] = 0 := by
    simpa [actualFourJets, jetEval, Fin.sum_univ_succ, rational_smul, add_assoc] using ha
  obtain ⟨h0, hrest⟩ := actual_four_jet_relation c (a 0) ![a 1, a 2, a 3] hrel
  have h1 := congrFun hrest 0
  have h2 := congrFun hrest 1
  have h3 := congrFun hrest 2
  fin_cases i
  · exact h0
  · simpa using h1
  · simpa using h2
  · simpa using h3

end Zeta7Germ

import Zeta7Proof.N4PrimitiveConstants

/-! A finite constant basis for every actual primitive projection. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open scoped RatFunc BigOperators
namespace Zeta7Germ

def constantSpace (S : Submodule (RatFunc ℂ) (Fin 3 → RatFunc ℂ)) :
    Submodule ℂ (Fin 3 → ℂ) where
  carrier := {a | (fun i => RatFunc.C (a i)) ∈ S}
  zero_mem' := by
    change (fun i : Fin 3 => RatFunc.C ((0 : Fin 3 → ℂ) i)) ∈ S
    convert S.zero_mem using 1
    ext i
    simp
  add_mem' := by
    intro a b ha hb
    change (fun i => RatFunc.C (a i + b i)) ∈ S
    have he : (fun i => RatFunc.C (a i + b i)) =
        (fun i => RatFunc.C (a i)) + (fun i => RatFunc.C (b i)) := by ext i; simp
    rw [he]
    exact S.add_mem ha hb
  smul_mem' := by
    intro r a ha
    change (fun i => RatFunc.C (r * a i)) ∈ S
    have he : (fun i => RatFunc.C (r * a i)) = RatFunc.C r • (fun i => RatFunc.C (a i)) := by
      ext i; simp [smul_eq_mul]
    rw [he]
    exact S.smul_mem (RatFunc.C r) ha

theorem exists_constant_basis (S : Submodule (RatFunc ℂ) (Fin 3 → RatFunc ℂ))
    (hs : ∀ v ∈ S, (fun i => rationalD (v i)) ∈ S) :
    ∃ (r : ℕ) (_ : r ≤ 3) (a : Fin r → Fin 3 → ℂ),
      LinearIndependent ℂ a ∧
      LinearIndependent (RatFunc ℂ) (fun j i => RatFunc.C (a j i)) ∧
      (∀ j, (fun i => RatFunc.C (a j i)) ∈ S) ∧
      Submodule.span (RatFunc ℂ) (Set.range (fun j i => RatFunc.C (a j i))) = S := by
  classical
  let b := Module.finBasis ℂ (constantSpace S)
  let a := fun j => ((b j : constantSpace S) : Fin 3 → ℂ)
  have ha : LinearIndependent ℂ a := b.linearIndependent.map' (constantSpace S).subtype
    (by simp)
  have hm (j) : (fun i => RatFunc.C (a j i)) ∈ S := (b j).property
  refine ⟨Module.finrank ℂ (constantSpace S), ?_, a, ha,
    constant_vectors_independent a ha, hm, ?_⟩
  · simpa using (constantSpace S).finrank_le
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact hm j
  · apply le_trans (le_of_eq (constantSpan_eq_of_stable S hs).symm)
    apply Submodule.span_le.mpr
    rintro _ ⟨w, rfl, hw⟩
    let v : constantSpace S := ⟨w, hw⟩
    have he : (∑ j, RatFunc.C (b.repr v j) • (fun i => RatFunc.C (a j i))) =
        (fun i => RatFunc.C (w i)) := by
      ext i
      have h := congrArg (fun v : constantSpace S => (v : Fin 3 → ℂ) i) (b.sum_repr v)
      simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul] at h
      have hc := congrArg RatFunc.C h
      simpa only [map_sum, map_mul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hc
    rw [← he]
    apply Submodule.sum_mem
    intro j _
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem actual_primitive_projection_basis
    (S : Submodule (RatFunc ℂ) SevenCoordinates)
    (hs : ∀ z ∈ S, connection7 z ∈ S) :
    ∃ (r : ℕ) (_ : r ≤ 3) (a : Fin r → Fin 3 → ℂ),
      LinearIndependent ℂ a ∧
      LinearIndependent (RatFunc ℂ) (fun j i => RatFunc.C (a j i)) ∧
      (∀ j, (fun i => RatFunc.C (a j i)) ∈ primitiveProjection S) ∧
      Submodule.span (RatFunc ℂ) (Set.range (fun j i => RatFunc.C (a j i))) =
        primitiveProjection S :=
  exists_constant_basis _ (primitiveProjection_stable S hs)

end Zeta7Germ

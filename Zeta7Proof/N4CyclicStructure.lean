import Zeta7Proof.N4CyclicSpan
import Zeta7Proof.N4PrimitiveBasis

/-! The actual cyclic space is the full four-jet space plus a constant
primitive subspace. Its rank is proved to be four plus the primitive rank. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
open scoped RatFunc
namespace Zeta7Germ

theorem submodule_eq_prod_of_fourRestriction_top
    (S : Submodule (RatFunc ℂ) SevenCoordinates) (h : fourRestriction S = ⊤) :
    S = (⊤ : Submodule (RatFunc ℂ) FourCoordinates).prod (primitiveProjection S) := by
  apply le_antisymm
  · intro z hz
    exact ⟨Submodule.mem_top, ⟨z.1, hz⟩⟩
  · rintro z ⟨_, hw⟩
    obtain ⟨v, hv⟩ := hw
    have hm : z.1 - v ∈ fourRestriction S := by rw [h]; trivial
    have hh : (z.1 - v, (0 : Fin 3 → RatFunc ℂ)) ∈ S := hm
    have he := S.add_mem hh hv
    simpa using he

def splitFourPrimitive (S : Submodule (RatFunc ℂ) SevenCoordinates)
    (h : fourRestriction S = ⊤) :
    S ≃ₗ[RatFunc ℂ] (FourCoordinates × primitiveProjection S) where
  toFun z := (z.val.1, ⟨z.val.2, ⟨z.val.1, z.property⟩⟩)
  invFun z := ⟨(z.1, z.2.val), by
    exact (submodule_eq_prod_of_fourRestriction_top S h).ge
      ⟨Submodule.mem_top, z.2.property⟩⟩
  left_inv z := by rfl
  right_inv z := by rfl
  map_add' z w := by rfl
  map_smul' a z := by rfl

theorem cyclic_rank_eq_four_add_projection (z : SevenCoordinates)
    (hz : z.1.2 ≠ 0 ∨ z.2 ≠ 0) :
    Module.finrank (RatFunc ℂ) (cyclicSpan z) =
      4 + Module.finrank (RatFunc ℂ) (primitiveProjection (cyclicSpan z)) := by
  have he := (splitFourPrimitive (cyclicSpan z) (cyclicSpan_contains_four z hz)).finrank_eq
  simpa [Module.finrank_prod, FourCoordinates] using he

theorem actual_cyclic_constant_structure (z : SevenCoordinates)
    (hz : z.1.2 ≠ 0 ∨ z.2 ≠ 0) :
    ∃ (r : ℕ) (_ : r ≤ 3) (a : Fin r → Fin 3 → ℂ),
      LinearIndependent ℂ a ∧
      LinearIndependent (RatFunc ℂ) (fun j i => RatFunc.C (a j i)) ∧
      cyclicSpan z = (⊤ : Submodule (RatFunc ℂ) FourCoordinates).prod
        (Submodule.span (RatFunc ℂ) (Set.range (fun j i => RatFunc.C (a j i)))) ∧
      Module.finrank (RatFunc ℂ) (cyclicSpan z) = 4 + r ∧
      LinearIndependent (RatFunc ℂ) (fun i : Fin (4 + r) => connection7^[i.val] z) := by
  obtain ⟨r, hr, a, ha, haE, hm, hspan⟩ :=
    actual_primitive_projection_basis (cyclicSpan z) (cyclicSpan_stable z)
  have hdim : Module.finrank (RatFunc ℂ) (primitiveProjection (cyclicSpan z)) = r := by
    have he := finrank_span_eq_card haE
    rw [hspan] at he
    simpa using he
  have hrank : Module.finrank (RatFunc ℂ) (cyclicSpan z) = 4 + r := by
    rw [cyclic_rank_eq_four_add_projection z hz, hdim]
  refine ⟨r, hr, a, ha, haE, ?_, hrank, cyclic_derivatives_independent z (4 + r) hrank.ge⟩
  rw [hspan]
  exact submodule_eq_prod_of_fourRestriction_top _ (cyclicSpan_contains_four z hz)

end Zeta7Germ

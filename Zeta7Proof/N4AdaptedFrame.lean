import Zeta7Proof.N4PolynomialSource

/-! Coordinates in the actual constant-primitive cyclic frame. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
open scoped RatFunc
open Polynomial
namespace Zeta7Germ

abbrev AdaptedIndex (r : ℕ) := Fin 4 ⊕ Fin r

def adaptedMap {r : ℕ} (a : Fin r → Fin 3 → ℂ) :
    (AdaptedIndex r → RatFunc ℂ) →ₗ[RatFunc ℂ] SevenCoordinates where
  toFun v := ((v (.inl 0), ![v (.inl 1), v (.inl 2), v (.inl 3)]),
    ∑ j, v (.inr j) • (fun i => RatFunc.C (a j i)))
  map_add' v w := by
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · ext i; fin_cases i <;> rfl
    · simp [add_smul, Finset.sum_add_distrib]
  map_smul' s v := by
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · ext i; fin_cases i <;> rfl
    · simp [smul_smul, Finset.smul_sum]

theorem adaptedMap_injective {r : ℕ} (a : Fin r → Fin 3 → ℂ)
    (ha : LinearIndependent (RatFunc ℂ) (fun j i => RatFunc.C (a j i))) :
    Function.Injective (adaptedMap a) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm _ bot_le
  intro v hv
  change adaptedMap a v = 0 at hv
  have hr := congrArg (fun z : SevenCoordinates => z.1.1) hv
  have hjet := congrArg (fun z : SevenCoordinates => z.1.2) hv
  have hw := congrArg (fun z : SevenCoordinates => z.2) hv
  change (∑ j, v (.inr j) • (fun i => RatFunc.C (a j i))) = 0 at hw
  have hh := Fintype.linearIndependent_iff.mp ha (fun j => v (.inr j)) hw
  ext i
  cases i with
  | inr j => exact hh j
  | inl j =>
      have h0 := congrFun hjet 0
      have h1 := congrFun hjet 1
      have h2 := congrFun hjet 2
      fin_cases j
      · exact hr
      · exact h0
      · exact h1
      · exact h2

theorem adapted_polynomial_coordinates {r M : ℕ} (a : Fin r → Fin 3 → ℂ)
    (p : PolynomialSevenCoordinates) (hp : sevenDegreeLE M p)
    (hs : (polynomialSevenCast p).2 ∈
      Submodule.span (RatFunc ℂ) (Set.range (fun j i => RatFunc.C (a j i)))) :
    ∃ q : AdaptedIndex r → Polynomial ℂ, (∀ i, (q i).natDegree ≤ M) ∧
      adaptedMap a (fun i => (q i : RatFunc ℂ)) = polynomialSevenCast p := by
  obtain ⟨b, hb, he⟩ := polynomial_coordinates_of_constant_span a p.2 M hp.2.2 hs
  let q : AdaptedIndex r → Polynomial ℂ :=
    Sum.elim ![p.1.1, p.1.2 0, p.1.2 1, p.1.2 2] b
  refine ⟨q, ?_, ?_⟩
  · intro i
    cases i with
    | inr j => exact hb j
    | inl j => fin_cases j <;> first | exact hp.1 | exact hp.2.1 _
  · apply Prod.ext
    · apply Prod.ext
      · rfl
      · ext i; fin_cases i <;> rfl
    · ext i
      have h := congrArg (fun p : Polynomial ℂ => (p : RatFunc ℂ)) (he i)
      simp only [RatFunc.coePolynomial_eq_algebraMap, map_sum, map_mul,
        RatFunc.algebraMap_C] at h
      simpa only [adaptedMap, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul, q, Sum.elim_inr, polynomialSevenCast,
        RatFunc.coePolynomial_eq_algebraMap] using h

theorem actual_source_adapted_coordinates {r : ℕ} (d : ℕ)
    (b : Zeta7Common.BlockIndex d → ℚ) (a : Fin r → Fin 3 → ℂ)
    (hs : (actualBlockCoordinates d b).2 ∈
      Submodule.span (RatFunc ℂ) (Set.range (fun j i => RatFunc.C (a j i)))) :
    ∃ q : AdaptedIndex r → Polynomial ℂ, (∀ i, (q i).natDegree ≤ d + 1) ∧
      adaptedMap a (fun i => (q i : RatFunc ℂ)) = actualBlockCoordinates d b := by
  obtain ⟨q, hq, he⟩ := adapted_polynomial_coordinates a (actualPolynomialCoordinates d b)
    (actualPolynomialCoordinates_degree d b) (by rwa [actualPolynomialCoordinates_cast])
  exact ⟨q, hq, he.trans (actualPolynomialCoordinates_cast d b)⟩

/-- All adapted polynomial-coordinate premises are supplied by the original
source and its proved cyclic structure. -/
theorem actual_source_adapted_frame (d : ℕ) (b : Zeta7Common.BlockIndex d → ℚ)
    (hn : (actualBlockCoordinates d b).1.2 ≠ 0 ∨ (actualBlockCoordinates d b).2 ≠ 0) :
    ∃ (r : ℕ) (_ : r ≤ 3) (a : Fin r → Fin 3 → ℂ)
      (q : AdaptedIndex r → Polynomial ℂ),
      LinearIndependent (RatFunc ℂ) (fun j i => RatFunc.C (a j i)) ∧
      (∀ i, (q i).natDegree ≤ d + 1) ∧
      adaptedMap a (fun i => (q i : RatFunc ℂ)) = actualBlockCoordinates d b ∧
      Module.finrank (RatFunc ℂ) (cyclicSpan (actualBlockCoordinates d b)) = 4 + r := by
  obtain ⟨r, hr, a, ha, haE, hs, hdim, hi⟩ := actual_cyclic_constant_structure _ hn
  have hm := self_mem_cyclicSpan (actualBlockCoordinates d b)
  rw [hs] at hm
  obtain ⟨q, hq, he⟩ := actual_source_adapted_coordinates d b a hm.2
  exact ⟨r, hr, a, q, haE, hq, he, hdim⟩

end Zeta7Germ

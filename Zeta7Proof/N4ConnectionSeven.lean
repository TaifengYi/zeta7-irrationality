import Zeta7Proof.N4ConnectionFour

/-! The explicit seven-coordinate connection and the actual evaluation map.
Stable subspaces containing a nonrational vector contain the four-jet space. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open scoped RatFunc LaurentSeries
namespace Zeta7Germ

abbrev SevenCoordinates := FourCoordinates × (Fin 3 → RatFunc ℂ)

def primitiveCoupling (w : Fin 3 → RatFunc ℂ) : FourCoordinates :=
  (0, ![primitiveMultiplier w * R, 0, 0])

def connection7 (z : SevenCoordinates) : SevenCoordinates :=
  (connection4 z.1 + primitiveCoupling z.2, fun i => rationalD (z.2 i))

def sevenEval (c : ℚ) (z : SevenCoordinates) : ℂ⸨X⸩ :=
  fourEval c z.1 + primitiveEval c z.2

theorem primitiveCoupling_add (w v : Fin 3 → RatFunc ℂ) :
    primitiveCoupling (w + v) = primitiveCoupling w + primitiveCoupling v := by
  apply Prod.ext
  · simp [primitiveCoupling]
  · ext i; fin_cases i <;> simp [primitiveCoupling, primitiveMultiplier] <;> ring

theorem primitiveCoupling_smul (a : RatFunc ℂ) (w : Fin 3 → RatFunc ℂ) :
    primitiveCoupling (a • w) = a • primitiveCoupling w := by
  apply Prod.ext
  · simp [primitiveCoupling]
  · ext i; fin_cases i <;> simp [primitiveCoupling, primitiveMultiplier, smul_eq_mul] <;> ring

theorem connection7_add (z w : SevenCoordinates) :
    connection7 (z + w) = connection7 z + connection7 w := by
  apply Prod.ext
  · simp only [connection7, Prod.fst_add, Prod.snd_add, connection4_add, primitiveCoupling_add]
    abel
  · ext i; simp [connection7]

theorem connection7_leibniz (a : RatFunc ℂ) (z : SevenCoordinates) :
    connection7 (a • z) = rationalD a • z + a • connection7 z := by
  apply Prod.ext
  · simp only [connection7, Prod.smul_fst, Prod.smul_snd, Prod.fst_add,
      connection4_leibniz, primitiveCoupling_smul, smul_add]
    abel
  · ext i; simp [connection7, Derivation.leibniz, smul_eq_mul]; ring

theorem sevenEval_add (c : ℚ) (z w : SevenCoordinates) :
    sevenEval c (z + w) = sevenEval c z + sevenEval c w := by
  simp [sevenEval, fourEval, jetEval_add, primitiveEval_add]
  ring

theorem sevenEval_smul (c : ℚ) (a : RatFunc ℂ) (z : SevenCoordinates) :
    sevenEval c (a • z) = embed a * sevenEval c z := by
  simp [sevenEval, fourEval, jetEval_smul, primitiveEval_smul, smul_eq_mul]
  ring

theorem sevenEval_derivative (c : ℚ) (z : SevenCoordinates) :
    laurentD (sevenEval c z) = sevenEval c (connection7 z) := by
  dsimp only [sevenEval]
  rw [map_add, fourEval_derivative, primitiveEval_derivative]
  simp only [
    connection7, fourEval, Prod.fst_add, Prod.snd_add, map_add, jetEval_add]
  have hp : embed (primitiveCoupling z.2).1 + jetEval c (primitiveCoupling z.2).2 =
      embed (primitiveMultiplier z.2 * R) * actualH c := by
    simp [primitiveCoupling, jetEval]
  linear_combination -hp

theorem sevenEval_eq_zero_iff (c : ℚ) (z : SevenCoordinates) :
    sevenEval c z = 0 ↔ z = 0 := by
  constructor
  · intro he
    obtain ⟨hr, hv, hw⟩ := actual_seven_frame_relation c z.1.1 z.1.2 z.2 he
    exact Prod.ext (Prod.ext hr hv) hw
  · rintro rfl; simp [sevenEval, fourEval, jetEval, primitiveEval]

def fourRestriction (S : Submodule (RatFunc ℂ) SevenCoordinates) :
    Submodule (RatFunc ℂ) FourCoordinates :=
  S.comap (LinearMap.inl (RatFunc ℂ) FourCoordinates (Fin 3 → RatFunc ℂ))

def primitiveProjection (S : Submodule (RatFunc ℂ) SevenCoordinates) :
    Submodule (RatFunc ℂ) (Fin 3 → RatFunc ℂ) where
  carrier := {w | ∃ z, (z, w) ∈ S}
  zero_mem' := ⟨0, S.zero_mem⟩
  add_mem' := by
    rintro v w ⟨r, hr⟩ ⟨s, hs⟩
    exact ⟨r + s, S.add_mem hr hs⟩
  smul_mem' := by
    rintro a v ⟨r, hr⟩
    exact ⟨a • r, S.smul_mem a hr⟩

theorem fourRestriction_stable (S : Submodule (RatFunc ℂ) SevenCoordinates)
    (hs : ∀ z ∈ S, connection7 z ∈ S) :
    ∀ z ∈ fourRestriction S, connection4 z ∈ fourRestriction S := by
  intro z hz
  have h := hs (z, 0) hz
  have he : connection7 (z, 0) = (connection4 z, 0) := by
    simp [connection7, primitiveCoupling, primitiveMultiplier]
    rfl
  rwa [he] at h

theorem primitiveProjection_stable (S : Submodule (RatFunc ℂ) SevenCoordinates)
    (hs : ∀ z ∈ S, connection7 z ∈ S) :
    ∀ w ∈ primitiveProjection S, (fun i => rationalD (w i)) ∈ primitiveProjection S := by
  rintro w ⟨z, hz⟩
  exact ⟨connection4 z + primitiveCoupling w, hs (z, w) hz⟩

/-- A constant primitive lift cannot differentiate into the rational line. -/
theorem constant_primitive_lift_obstruction (z : FourCoordinates) (a : Fin 3 → ℂ)
    (ha : a ≠ 0) :
    connection4 z + primitiveCoupling (fun i => RatFunc.C (a i)) ∉ rationalLine := by
  intro hm
  have hv := (mem_rationalLine _).mp hm
  have h0 := congrFun hv 0
  have h1 := congrFun hv 1
  have h2 := congrFun hv 2
  simp [connection4, connection3, primitiveCoupling] at h0 h1 h2
  have hL := correction_elimination (z.2 0) (z.2 1) (z.2 2)
    (primitiveMultiplier (fun i => RatFunc.C (a i)))
    (by linear_combination h0) h1 h2
  have he : L (z.2 2) = ((-constantPrimitivePolynomial a : Polynomial ℂ) : RatFunc ℂ) * R := by
    rw [RatFunc.coePolynomial_eq_algebraMap, map_neg,
      ← RatFunc.coePolynomial_eq_algebraMap, constantPrimitivePolynomial_cast]
    exact hL
  exact no_rational_inhomogeneous_solution (z.2 2) (-constantPrimitivePolynomial a)
    (neg_ne_zero.mpr (constantPrimitivePolynomial_ne_zero a ha))
    (by simpa using constantPrimitivePolynomial_degree a) he

theorem fourRestriction_eq_top_of_primitiveProjection_ne_bot
    (S : Submodule (RatFunc ℂ) SevenCoordinates)
    (hs : ∀ z ∈ S, connection7 z ∈ S) (hp : primitiveProjection S ≠ ⊥) :
    fourRestriction S = ⊤ := by
  obtain ⟨a, ha, ham⟩ := exists_constant_vector (primitiveProjection S) hp
    (primitiveProjection_stable S hs)
  obtain ⟨z, hz⟩ := ham
  have hd := hs _ hz
  have he : (fun i => rationalD (RatFunc.C (a i))) = (0 : Fin 3 → RatFunc ℂ) := by
    ext i; exact rationalD_constant _
  change (connection4 z + primitiveCoupling (fun i => RatFunc.C (a i)),
    (fun i => rationalD (RatFunc.C (a i)))) ∈ S at hd
  rw [he] at hd
  have hm : connection4 z + primitiveCoupling (fun i => RatFunc.C (a i)) ∈
      fourRestriction S := hd
  rcases connection4_submodule_classification (fourRestriction S)
      (fourRestriction_stable S hs) with h | h | h
  · rw [h] at hm
    have hzero : connection4 z + primitiveCoupling (fun i => RatFunc.C (a i)) = 0 := hm
    exact (constant_primitive_lift_obstruction z a ha (by rw [hzero]; exact
      rationalLine.zero_mem)).elim
  · rw [h] at hm
    exact (constant_primitive_lift_obstruction z a ha hm).elim
  · exact h

/-- This is the cyclic-span containment used by N4, before choosing a frame. -/
theorem fourRestriction_eq_top_of_nonrational
    (S : Submodule (RatFunc ℂ) SevenCoordinates)
    (hs : ∀ z ∈ S, connection7 z ∈ S) (z : SevenCoordinates) (hz : z ∈ S)
    (hn : z.1.2 ≠ 0 ∨ z.2 ≠ 0) : fourRestriction S = ⊤ := by
  by_cases hp : primitiveProjection S = ⊥
  · have hw : z.2 = 0 := by
      have hm : z.2 ∈ primitiveProjection S := ⟨z.1, hz⟩
      simpa [hp] using hm
    have hv : z.1.2 ≠ 0 := hn.resolve_right (not_not.mpr hw)
    have hm : z.1 ∈ fourRestriction S := by
      change (z.1, 0) ∈ S
      rw [← hw]
      exact hz
    rcases connection4_submodule_classification (fourRestriction S)
        (fourRestriction_stable S hs) with h | h | h
    · rw [h] at hm
      exact (hv (congrArg Prod.snd (show z.1 = 0 from hm))).elim
    · rw [h] at hm
      exact (hv ((mem_rationalLine _).mp hm)).elim
    · exact h
  · exact fourRestriction_eq_top_of_primitiveProjection_ne_bot S hs hp

end Zeta7Germ

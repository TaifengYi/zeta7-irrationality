import Zeta7Proof.ActualFourJetIndependence
import Zeta7Proof.GermConstantVector

/-! The projected relation kernel for the actual ordinary-primitive frame. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open scoped RatFunc LaurentSeries
namespace Zeta7Germ

def primitiveEval (c : ℚ) (w : Fin 3 → RatFunc ℂ) : ℂ⸨X⸩ :=
  embed (w 0) * complexSeries (Zeta7Common.primitiveFrame c 0) +
  embed (w 1) * complexSeries (Zeta7Common.primitiveFrame c 1) +
  embed (w 2) * complexSeries (Zeta7Common.primitiveFrame c 2)

def primitiveMultiplier (w : Fin 3 → RatFunc ℂ) : RatFunc ℂ :=
  w 0 - RatFunc.X * w 1 + RatFunc.X ^ 2 * w 2 / 2

theorem primitiveEval_add (c : ℚ) (v w : Fin 3 → RatFunc ℂ) :
    primitiveEval c (v + w) = primitiveEval c v + primitiveEval c w := by
  simp [primitiveEval]
  ring

theorem primitiveEval_smul (c : ℚ) (a : RatFunc ℂ) (w : Fin 3 → RatFunc ℂ) :
    primitiveEval c (a • w) = embed a * primitiveEval c w := by
  simp [primitiveEval, Pi.smul_apply, smul_eq_mul]
  ring

theorem primitiveEval_derivative (c : ℚ) (w : Fin 3 → RatFunc ℂ) :
    laurentD (primitiveEval c w) = primitiveEval c (fun i => rationalD (w i)) +
      embed (primitiveMultiplier w * R) * actualH c := by
  simp only [primitiveEval, primitiveMultiplier, map_add, Derivation.leibniz, smul_eq_mul,
    ← embed_rationalD, primitiveFrame_laurentD_zero, primitiveFrame_laurentD_one,
    primitiveFrame_laurentD_two, map_mul, map_sub, map_div₀, map_pow, map_ofNat]
  ring

def primitiveRelations (c : ℚ) : Submodule (RatFunc ℂ) (Fin 3 → RatFunc ℂ) where
  carrier := {w | ∃ r : RatFunc ℂ, ∃ v : Fin 3 → RatFunc ℂ,
    embed r + jetEval c v + primitiveEval c w = 0}
  zero_mem' := ⟨0, 0, by simp [jetEval, primitiveEval]⟩
  add_mem' := by
    rintro w z ⟨r, v, hv⟩ ⟨s, t, ht⟩
    refine ⟨r + s, v + t, ?_⟩
    rw [map_add, jetEval_add, primitiveEval_add]
    linear_combination hv + ht
  smul_mem' := by
    rintro a w ⟨r, v, hv⟩
    refine ⟨a * r, a • v, ?_⟩
    rw [map_mul, jetEval_smul, primitiveEval_smul]
    linear_combination embed a * hv

theorem primitiveRelations_stable (c : ℚ) :
    ∀ w ∈ primitiveRelations c, (fun i => rationalD (w i)) ∈ primitiveRelations c := by
  rintro w ⟨r, v, hv⟩
  refine ⟨rationalD r + v 2 * R, connection3 v + ![primitiveMultiplier w * R, 0, 0], ?_⟩
  have hd := congrArg laurentD hv
  rw [map_add, map_add, map_zero, ← embed_rationalD, jetEval_derivative,
    primitiveEval_derivative] at hd
  rw [map_add, jetEval_add]
  have hj : jetEval c ![primitiveMultiplier w * R, 0, 0] =
      embed (primitiveMultiplier w * R) * actualH c := by simp [jetEval]
  rw [hj]
  linear_combination hd

def constantPrimitivePolynomial (a : Fin 3 → ℂ) : Polynomial ℂ :=
  Polynomial.C (a 0) - Polynomial.C (a 1) * Polynomial.X +
    Polynomial.C (a 2 / 2) * Polynomial.X ^ 2

theorem constantPrimitivePolynomial_cast (a : Fin 3 → ℂ) :
    (constantPrimitivePolynomial a : RatFunc ℂ) = primitiveMultiplier (fun i => RatFunc.C (a i)) := by
  simp [constantPrimitivePolynomial, primitiveMultiplier, RatFunc.coePolynomial_eq_algebraMap,
    map_div₀, map_ofNat]
  ring

theorem constantPrimitivePolynomial_degree (a : Fin 3 → ℂ) :
    (constantPrimitivePolynomial a).natDegree ≤ 2 := by
  unfold constantPrimitivePolynomial
  compute_degree!

theorem constantPrimitivePolynomial_ne_zero (a : Fin 3 → ℂ) (ha : a ≠ 0) :
    constantPrimitivePolynomial a ≠ 0 := by
  intro hz
  have h0 := congrArg (fun p : Polynomial ℂ => p.coeff 0) hz
  have h1 := congrArg (fun p : Polynomial ℂ => p.coeff 1) hz
  have h2 := congrArg (fun p : Polynomial ℂ => p.coeff 2) hz
  simp [constantPrimitivePolynomial] at h0 h1 h2
  apply ha
  ext i
  fin_cases i <;> simp_all

theorem primitiveRelations_eq_bot (c : ℚ) : primitiveRelations c = ⊥ := by
  by_contra hne
  obtain ⟨a, ha, hamem⟩ := exists_constant_vector (primitiveRelations c) hne
    (primitiveRelations_stable c)
  obtain ⟨r, v, hv⟩ := hamem
  have hd := congrArg laurentD hv
  rw [map_add, map_add, map_zero, ← embed_rationalD, jetEval_derivative,
    primitiveEval_derivative] at hd
  have hconst : (fun i => rationalD (RatFunc.C (a i))) = (0 : Fin 3 → RatFunc ℂ) := by
    ext i
    exact rationalD_constant _
  rw [hconst] at hd
  have hz : primitiveEval c 0 = 0 := by simp [primitiveEval]
  rw [hz, zero_add] at hd
  let h : RatFunc ℂ := primitiveMultiplier (fun i => RatFunc.C (a i))
  have hrel : embed (rationalD r + v 2 * R) + jetEval c (connection3 v + ![h * R, 0, 0]) = 0 := by
    rw [map_add, jetEval_add]
    have hj : jetEval c ![h * R, 0, 0] = embed (h * R) * actualH c := by simp [jetEval]
    rw [hj]
    exact (by linear_combination hd)
  have hvec := (actual_four_jet_relation c _ _ hrel).2
  have h0 := congrFun hvec 0
  have h1 := congrFun hvec 1
  have h2 := congrFun hvec 2
  simp [connection3] at h0 h1 h2
  have hL : L (v 2) = -h * R := correction_elimination _ _ _ h
    (by linear_combination h0) h1 h2
  have he : L (v 2) = ((-constantPrimitivePolynomial a : Polynomial ℂ) : RatFunc ℂ) * R := by
    rw [RatFunc.coePolynomial_eq_algebraMap, map_neg,
      ← RatFunc.coePolynomial_eq_algebraMap, constantPrimitivePolynomial_cast]
    exact hL
  exact no_rational_inhomogeneous_solution (v 2) (-constantPrimitivePolynomial a)
    (neg_ne_zero.mpr (constantPrimitivePolynomial_ne_zero a ha))
    (by simpa using constantPrimitivePolynomial_degree a) he

theorem actual_seven_frame_relation (c : ℚ) (r : RatFunc ℂ) (v w : Fin 3 → RatFunc ℂ)
    (he : embed r + jetEval c v + primitiveEval c w = 0) : r = 0 ∧ v = 0 ∧ w = 0 := by
  have hw : w ∈ primitiveRelations c := ⟨r, v, he⟩
  rw [primitiveRelations_eq_bot] at hw
  have hw0 : w = 0 := hw
  have hprim : primitiveEval c w = 0 := by simp [hw0, primitiveEval]
  rw [hprim, add_zero] at he
  have hj := actual_four_jet_relation c r v he
  exact ⟨hj.1, hj.2, hw0⟩

end Zeta7Germ

import Zeta7Proof.N4AdaptedRows
import Zeta7Proof.N4DeterminantOrder

/-! The nonzero polynomial determinant of the actual adapted derivative rows. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
open scoped RatFunc LaurentSeries
open Polynomial Matrix
namespace Zeta7Germ

def adaptedMatrix {r : ℕ} (a : Fin r → Fin 3 → ℂ)
    (q : AdaptedIndex r → Polynomial ℂ) : Matrix (AdaptedIndex r) (AdaptedIndex r) (Polynomial ℂ) :=
  fun i j => adaptedRows a q (Fintype.equivFin (AdaptedIndex r) i).val j

theorem adaptedMatrix_det_ne_zero {r : ℕ} (a : Fin r → Fin 3 → ℂ)
    (q : AdaptedIndex r → Polynomial ℂ)
    (hdim : Module.finrank (RatFunc ℂ)
      (cyclicSpan (adaptedMap a (fun i => (q i : RatFunc ℂ)))) = 4 + r) :
    (adaptedMatrix a q).det ≠ 0 := by
  let z := adaptedMap a (fun i => (q i : RatFunc ℂ))
  have hi := clearedIterates_independent z (Fintype.card (AdaptedIndex r))
    (by
      change Fintype.card (AdaptedIndex r) ≤ Module.finrank (RatFunc ℂ)
        (cyclicSpan (adaptedMap a (fun i => (q i : RatFunc ℂ))))
      rw [hdim]
      simp [AdaptedIndex])
  have him := hi.comp (Fintype.equivFin (AdaptedIndex r)) (Fintype.equivFin _).injective
  have he : (fun i : AdaptedIndex r =>
      adaptedMap a (fun j => (adaptedMatrix a q i j : RatFunc ℂ))) =
      (fun i => clearedIterate z (Fintype.equivFin (AdaptedIndex r) i).val) := by
    funext i
    exact adaptedRows_map a q _
  have hmap : LinearIndependent (RatFunc ℂ)
      (fun i : AdaptedIndex r => adaptedMap a (fun j => (adaptedMatrix a q i j : RatFunc ℂ))) := by
    rw [he]
    exact him
  have hrows : LinearIndependent (RatFunc ℂ)
      (fun i j => (adaptedMatrix a q i j : RatFunc ℂ)) := hmap.of_comp
  have hdet : ((adaptedMatrix a q).map (algebraMap (Polynomial ℂ) (RatFunc ℂ))).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.linearIndependent_rows_iff_isUnit.mp hrows)).ne_zero
  intro hz
  apply hdet
  change ((algebraMap (Polynomial ℂ) (RatFunc ℂ)).mapMatrix (adaptedMatrix a q)).det = 0
  rw [← RingHom.map_det, hz, map_zero]

theorem sum_adapted_row_degrees (r d : ℕ) (hr : r ≤ 3) :
    (∑ i : AdaptedIndex r, (d + 1 + 8 * (Fintype.equivFin (AdaptedIndex r) i).val)) ≤ 7 * d + 175 := by
  have he := Equiv.sum_comp (Fintype.equivFin (AdaptedIndex r))
    (fun i : Fin (Fintype.card (AdaptedIndex r)) => d + 1 + 8 * i.val)
  apply le_trans (le_of_eq he)
  have hc : Fintype.card (AdaptedIndex r) = 4 + r := by simp [AdaptedIndex]
  rw [hc]
  interval_cases r <;> norm_num [Fin.sum_univ_succ] <;> omega

theorem adaptedMatrix_degree {r d : ℕ} (a : Fin r → Fin 3 → ℂ) (hr : r ≤ 3)
    (q : AdaptedIndex r → Polynomial ℂ) (hq : ∀ i, (q i).natDegree ≤ d + 1) :
    (adaptedMatrix a q).det.natDegree ≤ 7 * d + 175 := by
  exact (polynomial_det_degree (adaptedMatrix a q)
    (fun i : AdaptedIndex r => d + 1 + 8 * (Fintype.equivFin (AdaptedIndex r) i).val)
    (fun i j => adaptedRows_degree a q hq _ j)).trans
    (sum_adapted_row_degrees r d hr)

def adaptedGerms {r : ℕ} (c : ℚ) (a : Fin r → Fin 3 → ℂ) : AdaptedIndex r → ℂ⸨X⸩ :=
  fun i => sevenEval c (adaptedMap a (Pi.single i 1))

theorem adaptedGerms_constant {r : ℕ} (c : ℚ) (a : Fin r → Fin 3 → ℂ) :
    adaptedGerms c a (.inl 0) = 1 := by
  simp [adaptedGerms, adaptedMap, Pi.single_apply, sevenEval, fourEval, jetEval, primitiveEval]

theorem adaptedGerms_evaluation {r : ℕ} (c : ℚ) (a : Fin r → Fin 3 → ℂ)
    (v : AdaptedIndex r → RatFunc ℂ) :
    (∑ i, embed (v i) * adaptedGerms c a i) = sevenEval c (adaptedMap a v) := by
  classical
  have hv : (∑ i, v i • Pi.single i 1) = v := by
    simpa using (Pi.basisFun (RatFunc ℂ) (AdaptedIndex r)).sum_repr v
  have he := congrArg (fun w => sevenEval c (adaptedMap a w)) hv
  simpa only [map_sum, map_smul, sevenEval_sum, sevenEval_smul, adaptedGerms] using he

theorem adaptedMatrix_evaluation {r : ℕ} (c : ℚ) (a : Fin r → Fin 3 → ℂ)
    (q : AdaptedIndex r → Polynomial ℂ) (i : AdaptedIndex r) :
    (((adaptedMatrix a q).map polynomialLaurent) *ᵥ adaptedGerms c a) i =
      sevenEval c (clearedIterate (adaptedMap a (fun j => (q j : RatFunc ℂ)))
        (Fintype.equivFin (AdaptedIndex r) i).val) := by
  change (∑ j, embed (adaptedMatrix a q i j : RatFunc ℂ) * adaptedGerms c a j) = _
  rw [adaptedGerms_evaluation]
  congr 1
  exact adaptedRows_map a q _

theorem actual_source_polynomial_determinant (c : ℚ) (d : ℕ)
    (b : Zeta7Common.BlockIndex d → ℚ)
    (hn : (actualBlockCoordinates d b).1.2 ≠ 0 ∨ (actualBlockCoordinates d b).2 ≠ 0) :
    ∃ (r : ℕ) (_ : r ≤ 3) (a : Fin r → Fin 3 → ℂ)
      (q : AdaptedIndex r → Polynomial ℂ),
      (adaptedMatrix a q).det ≠ 0 ∧ (adaptedMatrix a q).det.natDegree ≤ 7 * d + 175 ∧
      ∀ i, (((adaptedMatrix a q).map polynomialLaurent) *ᵥ adaptedGerms c a) i =
        sevenEval c (clearedIterate (actualBlockCoordinates d b)
          (Fintype.equivFin (AdaptedIndex r) i).val) := by
  obtain ⟨r, hr, a, q, ha, hq, he, hdim⟩ := actual_source_adapted_frame d b hn
  refine ⟨r, hr, a, q, adaptedMatrix_det_ne_zero a q (by rwa [he]),
    adaptedMatrix_degree a hr q hq, ?_⟩
  intro i
  rw [adaptedMatrix_evaluation, he]

end Zeta7Germ

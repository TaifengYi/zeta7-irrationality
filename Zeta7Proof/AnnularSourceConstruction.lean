import Zeta7Proof.AnnularSourceMinor
import Zeta7Proof.CommonRationalGerms

/-! The explicit integral source construction in A5 / Appendix A4.
The input A contains the already scaled coefficients 7^4 A_j. Constructing
those coefficients from the analytic hypergeometric solution remains separate.
The theorem proves a common, degree-independent source cost for every d.
-/
set_option autoImplicit false
noncomputable section
open Polynomial Matrix
namespace Zeta7AnnularSource
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- Coefficients of t^m times the Laurent truncation from -m through 6. -/
def sourceColumns (A : Fin 6 → ℤ → ℤ_[7]) (d : ℕ) :
    Matrix (Zeta7Common.TailIndex d) (Fin (d - 6)) ℤ_[7] :=
  fun row m => if row.2.val ≤ m.val + 6 then A row.1 ((row.2.val : ℤ) - m.val) else 0

abbrev Remaining (d ell : ℕ) (hell : ell ≤ 6) :=
  {r : Zeta7Common.TailIndex d // r ∉ Set.range (selectedKRow d ell hell)}

/-- The selected rows first, then every other coordinate exactly once. -/
def sourceOrder (d ell : ℕ) (hell : ell ≤ 6) :
    Fin (d - 6) ⊕ Remaining d ell hell ≃ Zeta7Common.TailIndex d :=
  (Equiv.sumCongr (Equiv.ofInjective _ (selectedKRow d ell hell).injective)
    (Equiv.refl _)).trans (Equiv.Set.sumCompl (Set.range (selectedKRow d ell hell)))

theorem sourceOrder_selected (d ell : ℕ) (hell : ell ≤ 6) (i : Fin (d - 6)) :
    sourceOrder d ell hell (.inl i) = selectedKRow d ell hell i := rfl

theorem sourceColumns_minor (A : Fin 6 → ℤ → ℤ_[7]) (f : ℤ_[7][X])
    (hK : A 3 = coeffInt f) (hdeg : f.natDegree ≤ 6)
    (d ell : ℕ) (hell : ell ≤ 6) :
    (sourceColumns A d).submatrix (fun i => sourceOrder d ell hell (.inl i)) id =
      shiftMinor f ell (d - 6) := by
  ext i m
  change (if ell + i.val ≤ m.val + 6 then
    A 3 ((ell + i.val : ℕ) - (m.val : ℤ)) else 0) =
    coeffInt f ((ell : ℤ) + i.val - m.val)
  rw [hK]
  push_cast
  split_ifs with h
  · rfl
  · unfold coeffInt
    rw [ite_eq_left (by omega), Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]

def sourceCompletion (A : Fin 6 → ℤ → ℤ_[7]) (d ell : ℕ) (hell : ell ≤ 6) :
    Matrix (Fin (d - 6) ⊕ Remaining d ell hell)
      (Fin (d - 6) ⊕ Remaining d ell hell) ℤ_[7] :=
  completion (sourceOrder d ell hell) (sourceColumns A d)

theorem sourceCompletion_det (A : Fin 6 → ℤ → ℤ_[7]) (f : ℤ_[7][X])
    (hK : A 3 = coeffInt f) (hdeg : f.natDegree ≤ 6)
    (d ell : ℕ) (hell : ell ≤ 6) :
    (sourceCompletion A d ell hell).det = (shiftMinor f ell (d - 6)).det := by
  rw [sourceCompletion, det_completion, sourceColumns_minor A f hK hdeg]

/-- A4's actual integral completion, with its exact index for all degrees.
Nonvanishing of f is required; it is not seven-germ independence. -/
theorem exists_sourceCompletion_cost (A : Fin 6 → ℤ → ℤ_[7]) (f : ℤ_[7][X])
    (hK : A 3 = coeffInt f) (hdeg : f.natDegree ≤ 6) (hf : f ≠ 0) :
    ∃ (a ell : ℕ) (hell : ell ≤ 6), ∀ d : ℕ,
      (sourceCompletion A d ell hell).det ≠ 0 ∧
      (sourceCompletion A d ell hell).det.valuation = a * (d - 6) := by
  obtain ⟨a, ell, hell, hcost⟩ := exists_minor_cost f hf
  refine ⟨a, ell, hell.trans hdeg, fun d => ?_⟩
  rw [sourceCompletion_det A f hK hdeg]
  exact hcost (d - 6)

/-- Each constructed column keeps its own image; none is replaced by a lift. -/
theorem sourceCompletion_original (A : Fin 6 → ℤ → ℤ_[7])
    (d ell : ℕ) (hell : ell ≤ 6)
    (i : Fin (d - 6) ⊕ Remaining d ell hell) (m : Fin (d - 6)) :
    sourceCompletion A d ell hell i (.inl m) =
      sourceColumns A d (sourceOrder d ell hell i) m :=
  completion_original _ _ _ _

/-- The same target coefficient matrix after the explicit integral source change. -/
theorem target_source_change (A : Fin 6 → ℤ → ℤ_[7]) (f : ℤ_[7][X])
    (hK : A 3 = coeffInt f) (hdeg : f.natDegree ≤ 6)
    (d ell : ℕ) (hell : ell ≤ 6) (row : Zeta7Common.TailIndex d → ℕ) :
    ((Zeta7Common.tailMatrix d Zeta7Common.targetGerms row).submatrix
        (sourceOrder d ell hell) (sourceOrder d ell hell) *
      (sourceCompletion A d ell hell).map (algebraMap ℤ_[7] ℚ_[7])).det =
      (Zeta7Common.tailMatrix d Zeta7Common.targetGerms row).det *
        algebraMap ℤ_[7] ℚ_[7] (shiftMinor f ell (d - 6)).det := by
  rw [Matrix.det_mul, Matrix.det_submatrix_equiv_self]
  congr 1
  change ((algebraMap ℤ_[7] ℚ_[7]).mapMatrix (sourceCompletion A d ell hell)).det = _
  rw [← RingHom.map_det]
  rw [sourceCompletion_det A f hK hdeg]

/-- The identical source change on the t=49x matrix used by A.
Both ordinary primitive germs are rescaled as series; the factors 49 and 49^2
in the source relation belong to A_5 and A_6, not to this matrix. -/
theorem normalised_target_source_change (A : Fin 6 → ℤ → ℤ_[7]) (f : ℤ_[7][X])
    (hK : A 3 = coeffInt f) (hdeg : f.natDegree ≤ 6)
    (d ell : ℕ) (hell : ell ≤ 6) (row : Zeta7Common.TailIndex d → ℕ) :
    ((Zeta7Common.tailMatrix d
        (fun j => PowerSeries.rescale (49 : ℚ_[7])⁻¹ (Zeta7Common.targetGerms j)) row).submatrix
        (sourceOrder d ell hell) (sourceOrder d ell hell) *
      (sourceCompletion A d ell hell).map (algebraMap ℤ_[7] ℚ_[7])).det =
      (Zeta7Common.tailMatrix d
        (fun j => PowerSeries.rescale (49 : ℚ_[7])⁻¹ (Zeta7Common.targetGerms j)) row).det *
        algebraMap ℤ_[7] ℚ_[7] (shiftMinor f ell (d - 6)).det := by
  rw [Matrix.det_mul, Matrix.det_submatrix_equiv_self]
  congr 1
  change ((algebraMap ℤ_[7] ℚ_[7]).mapMatrix (sourceCompletion A d ell hell)).det = _
  rw [← RingHom.map_det, sourceCompletion_det A f hK hdeg]

end Zeta7AnnularSource

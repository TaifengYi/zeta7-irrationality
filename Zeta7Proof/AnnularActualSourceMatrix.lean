import Zeta7Proof.AnnularActualSource
import Zeta7Proof.ActualN4BoundedRows

/-! The constructed source change on the original canonical normalized matrix. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
namespace Zeta7Annulus
local instance AnnularActualSourceMatrix_prime : Fact (Nat.Prime 7) := ⟨by decide⟩
open PowerSeries Zeta7Common Zeta7AnnularSource

def actualNormalizedTargetMatrix (d : ℕ) (c : ℚ) :=
  tailMatrix d (fun j => rescale (49 : ℚ_[7])⁻¹ (targetGerms j)) (actualTailRow d c)

theorem actualNormalizedTargetMatrix_map (d : ℕ) (c : ℚ)
    (hc : (c : ℚ_[7]) = Zeta7Main.eta) :
    actualNormalizedTargetMatrix d c =
      (Zeta7Stage2A.normalizedTailMatrix d
        (fun j n => coeff n (rationalGerms c j)) (actualTailRow d c)).map (algebraMap ℚ ℚ_[7]) := by
  ext i j
  have hle : j.2.val ≤ actualTailRow d c i := by
    have := actualTailRow_position_lower d c i
    have := j.2.isLt
    omega
  simp only [actualNormalizedTargetMatrix, tailMatrix, coeff_X_pow_mul', if_pos hle,
    coeff_rescale, Matrix.map_apply, Zeta7Stage2A.normalizedTailMatrix,
    Zeta7Stage2A.tailMatrix, Zeta7Stage2A.normalizeCoefficients]
  rw [← rationalGerms_map c hc j.1, coeff_map]
  simp only [map_mul, map_inv₀, map_div₀, map_pow, map_ofNat, inv_pow, div_eq_mul_inv]
  ring

theorem actualNormalizedTargetMatrix_det (d : ℕ) (c : ℚ)
    (hc : (c : ℚ_[7]) = Zeta7Main.eta) :
    (actualNormalizedTargetMatrix d c).det = (actualNormalizedDeterminant d c : ℚ_[7]) := by
  rw [actualNormalizedTargetMatrix_map d c hc]
  exact ((algebraMap ℚ ℚ_[7]).map_det _).symm

theorem actualNormalized_source_change (d : ℕ) (c : ℚ)
    (hc : (c : ℚ_[7]) = Zeta7Main.eta) (ell : ℕ) (hell : ell ≤ 6) :
    ((actualNormalizedTargetMatrix d c).submatrix (sourceOrder d ell hell) (sourceOrder d ell hell) *
      (sourceCompletion actualIntegralAnnularCoefficients d ell hell).map (algebraMap ℤ_[7] ℚ_[7])).det =
      (actualNormalizedDeterminant d c : ℚ_[7]) *
        algebraMap ℤ_[7] ℚ_[7] (sourceCompletion actualIntegralAnnularCoefficients d ell hell).det := by
  rw [Matrix.det_mul, Matrix.det_submatrix_equiv_self, actualNormalizedTargetMatrix_det d c hc]
  congr 1
  exact ((algebraMap ℤ_[7] ℚ_[7]).map_det _).symm

/-- The same fixed witnesses serve all degrees and all target-specializing
parameters, retaining the source cost a*(d-6) and the canonical row ordering. -/
theorem actualNormalized_source_completion :
    ∃ (a ell : ℕ) (hell : ell ≤ 6), ∀ (d : ℕ) (c : ℚ),
      (sourceCompletion actualIntegralAnnularCoefficients d ell hell).det ≠ 0 ∧
      (sourceCompletion actualIntegralAnnularCoefficients d ell hell).det.valuation = a * (d - 6) ∧
      ((c : ℚ_[7]) = Zeta7Main.eta →
        ((actualNormalizedTargetMatrix d c).submatrix (sourceOrder d ell hell) (sourceOrder d ell hell) *
          (sourceCompletion actualIntegralAnnularCoefficients d ell hell).map (algebraMap ℤ_[7] ℚ_[7])).det =
          (actualNormalizedDeterminant d c : ℚ_[7]) *
            algebraMap ℤ_[7] ℚ_[7] (sourceCompletion actualIntegralAnnularCoefficients d ell hell).det) := by
  obtain ⟨a, ell, hell, h⟩ := actualAnnularSourceCompletion_cost
  exact ⟨a, ell, hell, fun d c => ⟨(h d).1, (h d).2,
    fun hc => actualNormalized_source_change d c hc ell hell⟩⟩

end Zeta7Annulus

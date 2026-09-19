import Zeta7Proof.AuxiliaryActualRows
import Zeta7Proof.AuxiliaryDeterminantBound

/-! Transfer a single compatible integral source basis to the unchanged actual determinant.
The caps and the basis remain explicit premises; this is not the auxiliary-prime estimate. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
namespace Zeta7Auxiliary
open Zeta7Common
variable {p : ℕ} [Fact p.Prime]

theorem integral_remove_unit_source {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℚ_[p]) (U : Matrix ι ι ℤ_[p]) (hU : IsUnit U.det) (z : ℚ_[p])
    (h : Integral (z * (A * U.map (algebraMap ℤ_[p] ℚ_[p])).det)) :
    Integral (z * A.det) := by
  obtain ⟨v, hv⟩ := hU.exists_right_inv
  have hi := h.mul (integral_coe v)
  have hd : (U.map (algebraMap ℤ_[p] ℚ_[p])).det =
      (algebraMap ℤ_[p] ℚ_[p]) U.det := ((algebraMap ℤ_[p] ℚ_[p]).map_det U).symm
  rw [Matrix.det_mul, hd] at hi
  have hc : (algebraMap ℤ_[p] ℚ_[p]) U.det * (v : ℚ_[p]) = 1 := by
    change (algebraMap ℤ_[p] ℚ_[p]) U.det * (algebraMap ℤ_[p] ℚ_[p]) v = 1
    rw [← map_mul, hv, map_one]
  simpa only [mul_assoc, hc, mul_one] using hi

theorem actualCommonDeterminant_four_caps (d : ℕ) (c : ℚ)
    (U : Matrix (TailIndex d) (TailIndex d) ℤ_[p]) (hU : IsUnit U.det)
    (e : TailIndex d → ℕ) (he : ∀ j, e j ≤ 4)
    (hcap : ∀ i j, Integral ((p : ℚ_[p]) ^ e j *
      (actualPrimeMatrix p d c * U.map (algebraMap ℤ_[p] ℚ_[p])) i j))
    (hgood : ∀ i, actualTailRow d c i < p → ∀ j,
      Integral ((actualPrimeMatrix p d c * U.map (algebraMap ℤ_[p] ℚ_[p])) i j)) :
    -padicValRat p (actualCommonDeterminant d c) ≤
      (thresholdMass (min (6 * d) (7 * d + 176 - p)) e : ℤ) := by
  have hi := determinant_four_caps
    (actualPrimeMatrix p d c * U.map (algebraMap ℤ_[p] ℚ_[p]))
    (actualBadRows p d c) e he hcap (by
      intro i hi j
      apply hgood i _ j
      simpa only [actualBadRows, Finset.mem_filter, Finset.mem_univ, true_and,
        not_le] using hi)
  have hj := integral_remove_unit_source (actualPrimeMatrix p d c) U hU _ hi
  rw [actualPrimeMatrix_det] at hj
  apply (scaled_integral_valuation (actualCommonDeterminant_ne_zero d c) _ hj).trans
  exact_mod_cast thresholdMass_mono e (actualBadRows_card p d c)

end Zeta7Auxiliary

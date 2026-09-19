import Zeta7Proof.AnnularActualLaurentRelation
import Zeta7Proof.AnnularActualSourceMatrix
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-! Exact finite-column and omitted-tail decomposition for the original source columns. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
namespace Zeta7Annulus
local instance AnnularActualColumnIdentity_prime : Fact (Nat.Prime 7) := ⟨by decide⟩
open Zeta7Common Zeta7AnnularSource

def actualRetainedCoefficient (d : ℕ) (j : Fin 6) (m r : ℕ) : ℚ_[7] :=
  ∑ i : Fin d, 7 ^ 4 * actualAnnularCoefficients j ((i.val : ℤ) - m) *
    actualNormalizedTargetCoefficients j ((r : ℤ) - i.val)

theorem actualConvolution_split (d : ℕ) (j : Fin 6) (m r : ℕ) (hm : m + 6 < d) :
    (7 : ℚ_[7]) ^ 4 * bilateralConvolution (actualAnnularCoefficients j)
      (actualNormalizedTargetCoefficients j) ((r : ℤ) - m) =
      actualRetainedCoefficient d j m r + ∑' l : ℕ, actualAnnularTailTerm j m r l := by
  classical
  let f : ℤ → ℚ_[7] := fun i => 7 ^ 4 * actualAnnularCoefficients j (i - m) *
    actualNormalizedTargetCoefficients j ((r : ℤ) - i)
  have hs0 := (actualAnnularCoefficients_decay j (by norm_num : (1 / 49 : ℝ) < 1 / 7)).convolution_summable
    (by norm_num : (0 : ℝ) < 1 / 7)
    (actualNormalizedTargetCoefficients_decay j (by norm_num : (0 : ℝ) < 1 / 7) (by norm_num))
    ((r : ℤ) - m)
  have hs : Summable f := by
    have hi : Function.Injective (fun i : ℤ => i - (m : ℤ)) :=
      (Equiv.subRight (m : ℤ)).injective
    have h := (hs0.mul_left ((7 : ℚ_[7]) ^ 4)).comp_injective hi
    apply h.congr
    intro i
    change 7 ^ 4 * (actualAnnularCoefficients j (i - m) *
      actualNormalizedTargetCoefficients j (r - m - (i - m))) = f i
    rw [show (r : ℤ) - m - (i - m) = r - i by omega]
    exact (mul_assoc _ _ _).symm
  have he : (7 : ℚ_[7]) ^ 4 * bilateralConvolution (actualAnnularCoefficients j)
      (actualNormalizedTargetCoefficients j) ((r : ℤ) - m) = ∑' i : ℤ, f i := by
    rw [bilateralConvolution, ← hs0.tsum_mul_left]
    rw [← (Equiv.subRight (m : ℤ)).tsum_eq]
    apply tsum_congr
    intro i
    change 7 ^ 4 * (actualAnnularCoefficients j (i - m) *
      actualNormalizedTargetCoefficients j (r - m - (i - m))) = f i
    rw [show (r : ℤ) - m - (i - m) = r - i by omega]
    exact (mul_assoc _ _ _).symm
  rw [he, tsum_of_nat_of_neg_add_one
    (hs.comp_injective (Nat.cast_injective))
    (hs.comp_injective (@Int.negSucc.inj))]
  congr 1
  · rw [tsum_eq_sum (s := Finset.range d) (by
      intro i hi
      have hi' : d ≤ i := by simpa only [Finset.mem_range, not_lt] using hi
      dsimp [f]
      rw [actualAnnularCoefficients_above j _ (by omega), mul_zero, zero_mul])]
    exact (Fin.sum_univ_eq_sum_range (fun i => f (i : ℤ)) d).symm
  · apply tsum_congr
    intro l
    dsimp [f, actualAnnularTailTerm]
    congr 2 <;> push_cast <;> congr 1 <;> omega

theorem actualRetainedCoefficient_sum (d m r : ℕ) (hm : m + 6 < d) (hr : d ≤ r) :
    (∑ j : Fin 6, actualRetainedCoefficient d j m r) = -actualAnnularTail m r := by
  have he := congrArg (fun z : ℚ_[7] => 7 ^ 4 * z)
    (actualAnnularLaurentRelation_above ((r : ℤ) - m) (by omega))
  rw [Finset.mul_sum, mul_zero] at he
  simp_rw [actualConvolution_split d _ m r hm] at he
  rw [Finset.sum_add_distrib] at he
  exact eq_neg_of_add_eq_zero_left he

theorem actualSourceColumn_image (d : ℕ) (c : ℚ) (m : Fin (d - 6)) (row : TailIndex d) :
    (actualNormalizedTargetMatrix d c *
      (sourceColumns actualIntegralAnnularCoefficients d).map (algebraMap ℤ_[7] ℚ_[7])) row m =
      -actualAnnularTail m.val (actualTailRow d c row) := by
  classical
  have hm : m.val + 6 < d := by have := m.isLt; omega
  have hr : d ≤ actualTailRow d c row := by
    have := actualTailRow_position_lower d c row; omega
  rw [← actualRetainedCoefficient_sum d m.val (actualTailRow d c row) hm hr]
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  have hir : i.val ≤ actualTailRow d c row := by have := i.isLt; omega
  simp only [actualNormalizedTargetMatrix, tailMatrix, PowerSeries.coeff_X_pow_mul',
    if_pos hir, Matrix.map_apply, sourceColumns]
  by_cases hi : i.val ≤ m.val + 6
  · rw [if_pos hi, PadicInt.algebraMap_apply, actualIntegralAnnularCoefficients_cast]
    change PowerSeries.coeff (actualTailRow d c row - i.val)
      (PowerSeries.rescale (49 : ℚ_[7])⁻¹ (targetGerms j)) *
        (7 ^ 4 * actualAnnularCoefficients j ((i.val : ℤ) - m.val)) = _
    rw [← Int.natCast_sub hir]
    exact mul_comm _ _
  · rw [if_neg hi, map_zero, mul_zero]
    rw [actualAnnularCoefficients_above j _ (by omega), mul_zero, zero_mul]

end Zeta7Annulus

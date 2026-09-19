import Zeta7Proof.AuxiliaryCaps
import Zeta7Proof.ActualN4BoundedRows

/-! The actual finite coefficient map and unchanged canonical determinant at every prime. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
namespace Zeta7Auxiliary
open Zeta7Common PowerSeries
variable (p : ℕ) [Fact p.Prime]

def actualGerms (c : ℚ) (j : Fin 6) : PowerSeries ℚ_[p] :=
  (rationalGerms c j).map (algebraMap ℚ ℚ_[p])

def coefficientMatrix (N d : ℕ) (c : ℚ) : Matrix (Fin N) (TailIndex d) ℚ_[p] :=
  fun n j => coeff n.val (X ^ j.2.val * actualGerms p c j.1)

def actualSourceSeries (d : ℕ) (c : ℚ) (a : TailIndex d → ℤ_[p]) : PowerSeries ℚ_[p] :=
  ∑ j, C (a j : ℚ_[p]) * (X ^ j.2.val * actualGerms p c j.1)

def actualCoefficientMap (N d : ℕ) (c : ℚ) :
    (TailIndex d → ℤ_[p]) →ₗ[ℤ_[p]] (Fin N → ℚ_[p]) where
  toFun a n := ∑ j, (a j : ℚ_[p]) * coefficientMatrix p N d c n j
  map_add' a b := by
    ext n
    simp only [Pi.add_apply, PadicInt.coe_add, add_mul, Finset.sum_add_distrib]
  map_smul' a b := by
    ext n
    simp only [Pi.smul_apply, smul_eq_mul, PadicInt.coe_mul, RingHom.id_apply]
    simp [Algebra.smul_def, Finset.mul_sum, mul_assoc]

theorem actualCoefficientMap_eq_coeff (N d : ℕ) (c : ℚ)
    (a : TailIndex d → ℤ_[p]) (n : Fin N) :
    actualCoefficientMap p N d c a n = coeff n.val (actualSourceSeries p d c a) := by
  simp only [actualCoefficientMap, LinearMap.coe_mk, AddHom.coe_mk,
    actualSourceSeries, map_sum, coeff_C_mul, coefficientMatrix]

theorem actualSourceSeries_cap {N d e : ℕ} (c : ℚ)
    (h : ∀ j, Cap N e (actualGerms p c j)) (a : TailIndex d → ℤ_[p]) :
    Cap N e (actualSourceSeries p d c a) := by
  apply Cap.sum
  intro j _
  exact (((h j.1).shift j.2.val).mono_range (Nat.le_add_right _ _)).const_mul (a j)

theorem actualTailRow_injective (d : ℕ) (c : ℚ) : Function.Injective (actualTailRow d c) := by
  intro i j h
  have he := (Zeta7Jump.fullJumpRow _ (rationalGerms_fullRank c d)).injective h
  exact Sum.inr.inj ((blockOrder d).injective he)

def actualRowEmbedding (d : ℕ) (c : ℚ) : TailIndex d ↪ Fin (7 * d + 176) where
  toFun i := ⟨actualTailRow d c i, actualTailRow_lt d c i⟩
  inj' := by intro i j h; exact actualTailRow_injective d c (congrArg Fin.val h)

def actualPrimeMatrix (d : ℕ) (c : ℚ) : Matrix (TailIndex d) (TailIndex d) ℚ_[p] :=
  tailMatrix d (actualGerms p c) (actualTailRow d c)

theorem actualPrimeMatrix_restriction (d : ℕ) (c : ℚ) :
    actualPrimeMatrix p d c =
      (coefficientMatrix p (7 * d + 176) d c).submatrix (actualRowEmbedding d c) id := rfl

theorem actualPrimeMatrix_det (d : ℕ) (c : ℚ) :
    (actualPrimeMatrix p d c).det = (actualCommonDeterminant d c : ℚ_[p]) := by
  change (tailMatrix d (fun j => (rationalGerms c j).map (algebraMap ℚ ℚ_[p]))
    (actualTailRow d c)).det = _
  rw [det_tailMatrix_map]
  rw [show (tailMatrix d (rationalGerms c) (actualTailRow d c)).det =
      actualCommonDeterminant d c from (commonDeterminant_eq_tail d c (rationalGerms_fullRank c d)).symm]
  rfl

theorem actualPrimeMatrix_det_ne_zero (d : ℕ) (c : ℚ) :
    (actualPrimeMatrix p d c).det ≠ 0 := by
  rw [actualPrimeMatrix_det]
  exact_mod_cast actualCommonDeterminant_ne_zero d c

def actualBadRows (d : ℕ) (c : ℚ) : Finset (TailIndex d) :=
  Finset.univ.filter (fun i => p ≤ actualTailRow d c i)

theorem actualBadRows_card (d : ℕ) (c : ℚ) :
    (actualBadRows p d c).card ≤ min (6 * d) (7 * d + 176 - p) := by
  apply le_min
  · exact (Finset.card_le_univ _).trans_eq (by simp [TailIndex])
  · have hinj := actualTailRow_injective d c
    rw [← Finset.card_image_of_injective _ hinj]
    have hsub : (actualBadRows p d c).image (actualTailRow d c) ⊆ Finset.Ico p (7 * d + 176) := by
      intro n hn
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hn
      exact Finset.mem_Ico.mpr ⟨(Finset.mem_filter.mp hi).2, actualTailRow_lt d c i⟩
    exact (Finset.card_le_card hsub).trans_eq (Nat.card_Ico _ _)

end Zeta7Auxiliary

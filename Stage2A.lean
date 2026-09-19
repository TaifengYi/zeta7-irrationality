import Mathlib
import Zeta7Proof.ExactAlgebra

/-!
# Stage 2A: exact determinant normalization and annular bookkeeping

Compiler status: NOT YET COMPILER-TESTED. Run this file directly in the
existing project pinned to Lean v4.34.0-rc2 and send back the complete output.

This is an additive checkpoint: it does not modify any Stage 1 source.
It supplies proof scripts for finite algebra underlying Sections 3.4 and 4.4
of the new proposed manuscript. It does NOT supply the analytic annular
relation, its coefficient bounds, integral saturation, any asymptotic
valuation bound, numerical enclosures, or a definition of the zeta target.

All generic hypotheses are displayed in theorem signatures. In particular,
nonzero determinant assumptions below are not constructions of the proposed
vanishing-flag determinant. No theorem here asserts irrationality.
-/

set_option autoImplicit false

namespace Zeta7Stage2A

/-! ## 1. The actual coefficient change under t = 49 x -/

/-- Coefficients of g(t/49), expressed as a transformation of a sequence. -/
def normalizeCoefficients (a : ℕ → ℚ) (n : ℕ) : ℚ :=
  a n / (49 : ℚ) ^ n

/-- The hypothesis prevents natural-number subtraction from truncating. -/
theorem shifted_coefficient_rescaling
    (a : ℕ → ℚ) (r k : ℕ) (hkr : k ≤ r) :
    normalizeCoefficients a (r - k) =
      (49 : ℚ) ^ k * a (r - k) / (49 : ℚ) ^ r := by
  have hp : (49 : ℚ) ^ r = (49 : ℚ) ^ (r - k) * (49 : ℚ) ^ k := by
    rw [← pow_add, Nat.sub_add_cancel hkr]
  unfold normalizeCoefficients
  rw [hp]
  field_simp <;> ring

section SquareMatrices

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Row and column factors of the normalized coefficient matrix. -/
def normalizeMatrix (M : Matrix ι ι ℚ) (row col : ι → ℕ) : Matrix ι ι ℚ :=
  fun i j => (49 : ℚ) ^ col j * M i j / (49 : ℚ) ^ row i

theorem normalizeMatrix_eq_diagonal
    (M : Matrix ι ι ℚ) (row col : ι → ℕ) :
    normalizeMatrix M row col =
      Matrix.diagonal (fun i => (1 : ℚ) / (49 : ℚ) ^ row i) *
        M * Matrix.diagonal (fun j => (49 : ℚ) ^ col j) := by
  ext i j
  simp only [normalizeMatrix, Matrix.diagonal_mul, Matrix.mul_diagonal]
  ring

/-- An exact determinant equality, not yet a p-adic valuation statement. -/
theorem det_normalizeMatrix
    (M : Matrix ι ι ℚ) (row col : ι → ℕ) :
    (normalizeMatrix M row col).det =
      (∏ i, (1 : ℚ) / (49 : ℚ) ^ row i) * M.det *
        (∏ j, (49 : ℚ) ^ col j) := by
  rw [normalizeMatrix_eq_diagonal]
  simp only [Matrix.det_mul, Matrix.det_diagonal]

/-- Rescaling preserves nonvanishing; it does not establish it initially. -/
theorem det_normalizeMatrix_ne_zero
    (M : Matrix ι ι ℚ) (row col : ι → ℕ) (hM : M.det ≠ 0) :
    (normalizeMatrix M row col).det ≠ 0 := by
  have h49 : (49 : ℚ) ≠ 0 := by norm_num
  have hrow : (∏ i, (1 : ℚ) / (49 : ℚ) ^ row i) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    exact div_ne_zero one_ne_zero (pow_ne_zero _ h49)
  have hcol : (∏ j, (49 : ℚ) ^ col j) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    exact pow_ne_zero _ h49
  rw [det_normalizeMatrix]
  exact mul_ne_zero (mul_ne_zero hrow hM) hcol

/-- Source changes must be paid for by dividing by their determinant. -/
theorem det_after_source_change
    (M U : Matrix ι ι ℚ) (hU : U.det ≠ 0) :
    M.det = (M * U).det / U.det := by
  rw [eq_div_iff hU, Matrix.det_mul]

end SquareMatrices

/-! ## 2. Apply the rescaling to the actual six-block matrix shape -/

abbrev TailIndex (d : ℕ) := Fin 6 × Fin d

def tailMatrix (d : ℕ) (g : Fin 6 → ℕ → ℚ)
    (row : TailIndex d → ℕ) : Matrix (TailIndex d) (TailIndex d) ℚ :=
  fun i j => g j.1 (row i - j.2.val)

def normalizedTailMatrix (d : ℕ) (g : Fin 6 → ℕ → ℚ)
    (row : TailIndex d → ℕ) : Matrix (TailIndex d) (TailIndex d) ℚ :=
  tailMatrix d (fun j => normalizeCoefficients (g j)) row

theorem normalizedTailMatrix_eq
    (d : ℕ) (g : Fin 6 → ℕ → ℚ) (row : TailIndex d → ℕ)
    (hrow : ∀ i, d ≤ row i) :
    normalizedTailMatrix d g row =
      normalizeMatrix (tailMatrix d g row) row (fun j => j.2.val) := by
  ext i j
  change normalizeCoefficients (g j.1) (row i - j.2.val) =
    (49 : ℚ) ^ j.2.val * g j.1 (row i - j.2.val) / (49 : ℚ) ^ row i
  apply shifted_coefficient_rescaling
  exact le_trans (Nat.le_of_lt j.2.isLt) (hrow i)

/-- This applies to arbitrary rational germs and selected tail rows. -/
theorem det_normalizedTailMatrix
    (d : ℕ) (g : Fin 6 → ℕ → ℚ) (row : TailIndex d → ℕ)
    (hrow : ∀ i, d ≤ row i) :
    (normalizedTailMatrix d g row).det =
      (∏ i, (1 : ℚ) / (49 : ℚ) ^ row i) * (tailMatrix d g row).det *
        (∏ j : TailIndex d, (49 : ℚ) ^ j.2.val) := by
  rw [normalizedTailMatrix_eq d g row hrow, det_normalizeMatrix]

/-! ## 3. The polynomial identity block does not change the determinant -/

theorem identity_block_det
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (A : Matrix ι κ ℚ) (M : Matrix κ κ ℚ) :
    (Matrix.fromBlocks (1 : Matrix ι ι ℚ) A
      (0 : Matrix κ ι ℚ) M).det = M.det := by
  rw [Matrix.det_fromBlocks_zero₂₁]
  simp

/-! ## 4. Exact count of the extra annular column weights -/

/-- There are d-6 constructed columns, with weights 0,2,...,2(d-7). -/
theorem annular_weight_sum (d : ℕ) (hd : 6 ≤ d) :
    2 * (∑ m ∈ Finset.range (d - 6), (m : ℤ)) =
      (d : ℤ) ^ 2 - 13 * (d : ℤ) + 42 := by
  have hcast : ((d - 6 : ℕ) : ℤ) = (d : ℤ) - 6 := by omega
  rw [Zeta7Exact.twice_sum_range, hcast]
  ring

/-- Combines exact row bookkeeping and column weights, not their valuations. -/
theorem baseline_plus_annular_weights (d : ℕ) (hd : 6 ≤ d) :
    2 * (((∑ k ∈ Finset.range (7 * d), (k : ℤ)) -
      (∑ k ∈ Finset.range d, (k : ℤ))) -
      6 * (∑ k ∈ Finset.range d, (k : ℤ))) +
      2 * (∑ m ∈ Finset.range (d - 6), (m : ℤ)) =
        43 * (d : ℤ) ^ 2 - 13 * (d : ℤ) + 42 := by
  rw [Zeta7Exact.baseline_tail_row_sum, annular_weight_sum d hd]
  ring

/-! ## 5. The normalized rational functions in the annular relation -/

def annularQ (t : ℚ) : ℚ := 49 + 13 * t + t ^ 2

theorem annularQ_rescaling (t : ℚ) :
    49 * Zeta7Exact.P (t / 49) = annularQ t := by
  simp only [Zeta7Exact.P, annularQ]
  ring

theorem annularQ_reciprocal (t : ℚ) (ht : t ≠ 0) :
    t ^ 2 * Zeta7Exact.P (1 / t) = annularQ t := by
  simp only [Zeta7Exact.P, annularQ]
  field_simp <;> ring

/-! Print both the main theorem types and their foundational dependencies. -/

#print det_normalizedTailMatrix
#print det_after_source_change
#print axioms shifted_coefficient_rescaling
#print axioms normalizeMatrix_eq_diagonal
#print axioms det_normalizeMatrix
#print axioms det_normalizeMatrix_ne_zero
#print axioms det_after_source_change
#print axioms normalizedTailMatrix_eq
#print axioms det_normalizedTailMatrix
#print axioms identity_block_det
#print axioms annular_weight_sum
#print axioms baseline_plus_annular_weights
#print axioms annularQ_rescaling
#print axioms annularQ_reciprocal

end Zeta7Stage2A

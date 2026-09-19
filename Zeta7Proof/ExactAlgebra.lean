import Mathlib

/-!
# Exact algebraic certificates for the level-seven candidate argument

This file contains only unconditional identities over `ℚ`. It deliberately
does not define the Kubota--Leopoldt zeta value and does not assert any
asymptotic determinant estimate.
-/

set_option autoImplicit false

namespace Zeta7Exact

def P (x : ℚ) : ℚ := 1 + 13 * x + 49 * x ^ 2

def N (x : ℚ) : ℚ := 1 + 245 * x + 2401 * x ^ 2

def T (x : ℚ) : ℚ :=
  1 - 490 * x - 21609 * x ^ 2 - 235298 * x ^ 3 - 823543 * x ^ 4

/-- The exact modular polynomial identity used to recover `j - 1728`. -/
theorem modular_polynomial_identity (x : ℚ) :
    P x * (N x) ^ 3 - (T x) ^ 2 = 1728 * x := by
  simp only [P, N, T]
  ring

/-- The quadratic `P` has no rational zero; in fact it is positive. -/
theorem P_pos (x : ℚ) : 0 < P x := by
  have hsquare : 0 ≤ (98 * x + 13) ^ 2 := sq_nonneg (98 * x + 13)
  have hid : 196 * P x = (98 * x + 13) ^ 2 + 27 := by
    simp only [P]
    ring
  nlinarith

theorem P_ne_zero (x : ℚ) : P x ≠ 0 := ne_of_gt (P_pos x)

def obstructionNumerator (x : ℚ) : ℚ :=
  9 + 433 * x + 5145 * x ^ 2 + 19208 * x ^ 3

theorem obstruction_pivot :
    obstructionNumerator (-1 / 10) = -1029 / 500 := by
  norm_num [obstructionNumerator]

theorem obstruction_pivot_ne_zero : obstructionNumerator (-1 / 10) ≠ 0 := by
  norm_num [obstructionNumerator]

/-- The five-diagonal bracket in `P L_y(P y^n)`. -/
def bandBracket (n y : ℚ) : ℚ :=
  n ^ 3 +
    (2 * n + 1) * (13 * n ^ 2 + 13 * n + 9) * y +
    (n + 1) * (267 * n ^ 2 + 534 * n + 433) * y ^ 2 +
    49 * (2 * n + 3) * (13 * n ^ 2 + 39 * n + 35) * y ^ 3 +
    2401 * (n + 2) ^ 3 * y ^ 4

theorem band_minus_two (y : ℚ) :
    bandBracket (-2) y = -8 - 105 * y - 433 * y ^ 2 - 441 * y ^ 3 := by
  simp only [bandBracket]
  ring

def annularResonance (y : ℚ) : ℚ :=
  -8 / y ^ 2 - 105 / y - 433 - 441 * y

theorem annular_correction_pivot :
    annularResonance (-10 / 49) = -1029 / 50 := by
  norm_num [annularResonance]

theorem annular_correction_pivot_ne_zero :
    annularResonance (-10 / 49) ≠ 0 := by
  norm_num [annularResonance]

def affineValue (intercept slope z : ℚ) : ℚ := intercept + slope * z

/-- Every adjacent pair of the nine affine pieces agrees at its breakpoint. -/
theorem profile_continuous_at_breakpoints :
    affineValue 15 (8 / 3) (1 / 2) = affineValue 14 (14 / 3) (1 / 2) ∧
    affineValue 14 (14 / 3) (3 / 4) = affineValue 15 (10 / 3) (3 / 4) ∧
    affineValue 15 (10 / 3) 1 = affineValue 19 (-2 / 3) 1 ∧
    affineValue 19 (-2 / 3) (12 / 7) = affineValue 23 (-3) (12 / 7) ∧
    affineValue 23 (-3) 2 = affineValue 29 (-6) 2 ∧
    affineValue 29 (-6) (7 / 3) = affineValue 22 (-3) (7 / 3) ∧
    affineValue 22 (-3) 3 = affineValue 28 (-5) 3 ∧
    affineValue 28 (-5) (7 / 2) = affineValue 21 (-3) (7 / 2) := by
  norm_num [affineValue]

theorem profile_vanishes_at_seven : affineValue 21 (-3) 7 = 0 := by
  norm_num [affineValue]

def affineArea (left right intercept slope : ℚ) : ℚ :=
  intercept * (right - left) + slope * (right ^ 2 - left ^ 2) / 2

def profileArea : ℚ :=
  affineArea 0 (1 / 2) 15 (8 / 3) +
  affineArea (1 / 2) (3 / 4) 14 (14 / 3) +
  affineArea (3 / 4) 1 15 (10 / 3) +
  affineArea 1 (12 / 7) 19 (-2 / 3) +
  affineArea (12 / 7) 2 23 (-3) +
  affineArea 2 (7 / 3) 29 (-6) +
  affineArea (7 / 3) 3 22 (-3) +
  affineArea 3 (7 / 2) 28 (-5) +
  affineArea (7 / 2) 7 21 (-3)

theorem profile_area_exact : profileArea = 12325 / 168 := by
  norm_num [profileArea, affineArea]

theorem six_masses_sum :
    (1 / 25 + 2 / 25 + 7 / 50 + 17 / 100 + 6 / 25 + 33 / 100 : ℚ) = 1 := by
  norm_num

/-- The assigned interval lengths are exactly seven times their masses. -/
theorem assigned_partition_lengths :
    (7 / 25 - 0 : ℚ) = 7 * (1 / 25) ∧
    (21 / 25 - 7 / 25 : ℚ) = 7 * (2 / 25) ∧
    (91 / 50 - 21 / 25 : ℚ) = 7 * (7 / 50) ∧
    (301 / 100 - 91 / 50 : ℚ) = 7 * (17 / 100) ∧
    (469 / 100 - 301 / 100 : ℚ) = 7 * (6 / 25) ∧
    (7 - 469 / 100 : ℚ) = 7 * (33 / 100) := by
  norm_num

theorem twice_sum_range (n : ℕ) :
    2 * (∑ k ∈ Finset.range n, (k : ℤ)) = (n : ℤ) * ((n : ℤ) - 1) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [Finset.sum_range_succ]
      push_cast
      nlinarith [ih]

/--
The rows `d, ..., 7d-1`, minus six copies of the column degrees
`0, ..., d-1`, contribute exactly `42 d²` after the factor two from `49 = 7²`.
-/
theorem baseline_tail_row_sum (d : ℕ) :
    2 * (((∑ k ∈ Finset.range (7 * d), (k : ℤ)) -
      (∑ k ∈ Finset.range d, (k : ℤ))) -
      6 * (∑ k ∈ Finset.range d, (k : ℤ))) = 42 * (d : ℤ) ^ 2 := by
  have hbig := twice_sum_range (7 * d)
  have hsmall := twice_sum_range d
  push_cast at hbig
  nlinarith

#print axioms modular_polynomial_identity
#print axioms P_pos
#print axioms obstruction_pivot
#print axioms band_minus_two
#print axioms annular_correction_pivot
#print axioms profile_continuous_at_breakpoints
#print axioms profile_area_exact
#print axioms assigned_partition_lengths
#print axioms baseline_tail_row_sum

end Zeta7Exact

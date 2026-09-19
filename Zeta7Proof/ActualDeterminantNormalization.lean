import Zeta7Proof.ActualSevenGermIndependence

/-! Exact normalization and the unconditional coordinate contribution for
the existing canonical determinant. No upper bound on the jump rows is used. -/
noncomputable section
set_option autoImplicit false
open PowerSeries
namespace Zeta7Common
local instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

def actualTailRow (d : ℕ) (c : ℚ) : TailIndex d → ℕ :=
  selectedTailRow d c (rationalGerms_fullRank c d)

def actualTailExcess (d : ℕ) (c : ℚ) (i : TailIndex d) : ℕ :=
  actualTailRow d c i - (d + (i.2.val + d * i.1.val))

theorem actualTailRow_position_lower (d : ℕ) (c : ℚ) (i : TailIndex d) :
    d + (i.2.val + d * i.1.val) ≤ actualTailRow d c i := by
  exact Zeta7Jump.fullJumpRow_lower _ (rationalGerms_fullRank c d) (blockOrder d (.inr i))

theorem actualTailRow_eq_position_add_excess (d : ℕ) (c : ℚ) (i : TailIndex d) :
    actualTailRow d c i = d + (i.2.val + d * i.1.val) + actualTailExcess d c i := by
  unfold actualTailExcess
  have := actualTailRow_position_lower d c i
  omega

def actualNormalizedDeterminant (d : ℕ) (c : ℚ) : ℚ :=
  (Zeta7Stage2A.normalizedTailMatrix d
    (fun j n => coeff n (rationalGerms c j)) (actualTailRow d c)).det

theorem actualNormalizedDeterminant_eq (d : ℕ) (c : ℚ) :
    actualNormalizedDeterminant d c =
      ((49 : ℚ) ^ (∑ i, actualTailRow d c i))⁻¹ * actualCommonDeterminant d c *
        (49 : ℚ) ^ (∑ i : TailIndex d, i.2.val) := by
  have he := commonDeterminant_normalization d c (rationalGerms_fullRank c d)
  simp only [one_div, Finset.prod_inv_distrib, Finset.prod_pow_eq_pow_sum] at he
  exact he

theorem actualNormalizedDeterminant_ne_zero (d : ℕ) (c : ℚ) :
    actualNormalizedDeterminant d c ≠ 0 := by
  rw [actualNormalizedDeterminant_eq]
  exact mul_ne_zero (mul_ne_zero (inv_ne_zero (pow_ne_zero _ (by norm_num)))
    (actualCommonDeterminant_ne_zero d c)) (pow_ne_zero _ (by norm_num))

theorem actualNormalization_valuation (d : ℕ) (c : ℚ) :
    padicValRat 7 (actualCommonDeterminant d c) =
      2 * ((∑ i, (actualTailRow d c i : ℤ)) - (∑ i : TailIndex d, (i.2.val : ℤ))) +
        padicValRat 7 (actualNormalizedDeterminant d c) := by
  have h49 : padicValRat 7 (49 : ℚ) = 2 := by
    rw [show (49 : ℚ) = 7 ^ 2 by norm_num, padicValRat.pow]
    have h7 : padicValRat 7 (7 : ℚ) = 1 := by
      simpa using padicValRat.self (by norm_num : 1 < 7)
    rw [h7]
    norm_num
  have hv := congrArg (padicValRat 7) (actualNormalizedDeterminant_eq d c)
  rw [padicValRat.mul (mul_ne_zero (inv_ne_zero (pow_ne_zero _ (by norm_num)))
      (actualCommonDeterminant_ne_zero d c)) (pow_ne_zero _ (by norm_num)),
    padicValRat.mul (inv_ne_zero (pow_ne_zero _ (by norm_num)))
      (actualCommonDeterminant_ne_zero d c), padicValRat.inv,
    padicValRat.pow, padicValRat.pow, h49] at hv
  push_cast at hv
  linarith

theorem tail_position_sum (d : ℕ) :
    2 * ((∑ i : TailIndex d, ((d + (i.2.val + d * i.1.val) : ℕ) : ℤ)) -
      (∑ i : TailIndex d, (i.2.val : ℤ))) = 42 * (d : ℤ) ^ 2 := by
  rw [← Finset.sum_sub_distrib]
  have he (i : TailIndex d) :
      ((d + (i.2.val + d * i.1.val) : ℕ) : ℤ) - (i.2.val : ℤ) =
        (d : ℤ) * (1 + (i.1.val : ℤ)) := by push_cast; ring
  simp only [he, Fintype.sum_prod_type]
  simp [Fin.sum_univ_succ]
  ring

theorem actual_coordinate_contribution (d : ℕ) (c : ℚ) :
    2 * ((∑ i, (actualTailRow d c i : ℤ)) - (∑ i : TailIndex d, (i.2.val : ℤ))) =
      42 * (d : ℤ) ^ 2 + 2 * (∑ i, (actualTailExcess d c i : ℤ)) := by
  simp_rw [actualTailRow_eq_position_add_excess, Nat.cast_add, Nat.cast_mul]
  rw [Finset.sum_add_distrib]
  have hb := tail_position_sum d
  push_cast at hb
  linear_combination hb

/-- Exact signed valuation identity for this determinant and these rows.
The excess is nonnegative, but its uniform upper bound still requires N4. -/
theorem actualCommonDeterminant_valuation_normalized (d : ℕ) (c : ℚ) :
    padicValRat 7 (actualCommonDeterminant d c) = 42 * (d : ℤ) ^ 2 +
      2 * (∑ i, (actualTailExcess d c i : ℤ)) +
        padicValRat 7 (actualNormalizedDeterminant d c) := by
  rw [actualNormalization_valuation, actual_coordinate_contribution]

theorem actualCommonDeterminant_valuation_baseline (d : ℕ) (c : ℚ) :
    42 * (d : ℤ) ^ 2 + padicValRat 7 (actualNormalizedDeterminant d c) ≤
      padicValRat 7 (actualCommonDeterminant d c) := by
  rw [actualCommonDeterminant_valuation_normalized]
  have h : 0 ≤ ∑ i, (actualTailExcess d c i : ℤ) := Finset.sum_nonneg (by intros; positivity)
  linarith

end Zeta7Common

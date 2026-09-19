import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Phase II, first certificate: `Real.log 7 < 2`

This is the standalone numerical input used at the very end of the contradiction, where the
difference of the claimed lower and upper limits is `S - δ · log 7` with `δ = 1/1000`; the
bound `log 7 < 2` turns `δ · log 7` into `< 0.002`.

The proof is kernel checked. It uses no `native_decide`, no `sorry` and no new axiom: it goes
through Mathlib's rational enclosure `Real.exp_one_gt_d9` for `e`, so the only arithmetic the
kernel performs is on rationals.
-/

noncomputable section
set_option autoImplicit false

namespace Zeta7Cert

open Real

/-- `e² > 7`, from the rational lower bound `e > 2.7182818283`. -/
theorem seven_lt_exp_two : (7 : ℝ) < Real.exp 2 := by
  have h : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have hpos : (0 : ℝ) < 2.7182818283 := by norm_num
  have hsq : (7 : ℝ) < Real.exp 1 ^ 2 := by nlinarith
  have hpow : Real.exp 1 ^ (2 : ℕ) = Real.exp ((2 : ℕ) : ℝ) := Real.exp_one_pow 2
  have : Real.exp ((2 : ℕ) : ℝ) = Real.exp 2 := by norm_num
  rw [← this, ← hpow]
  exact hsq

/-- **`log 7 < 2`.** -/
theorem log_seven_lt_two : Real.log 7 < 2 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 7)]
  exact seven_lt_exp_two

end Zeta7Cert

import Zeta7Proof.AuxiliaryActualGermCaps
import Zeta7Proof.AuxiliaryActualDeterminantBound

/-! Discharge low-row integrality for every integral source change of the actual matrix. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
namespace Zeta7Auxiliary
open PowerSeries Zeta7Common
variable {p : ℕ} [Fact p.Prime]

theorem actualPrimeMatrix_low_integral (d : ℕ) (c : ℚ) (hc : ¬ p ∣ c.den)
    (i j : TailIndex d) (hi : actualTailRow d c i < p) :
    Integral (actualPrimeMatrix p d c i j) := by
  have hh := ((actual_germs_cap_zero c hc j.1).shift j.2.val)
    (actualTailRow d c i) (hi.trans_le (Nat.le_add_right _ _))
  simpa only [pow_zero, one_mul, actualPrimeMatrix, tailMatrix, actualGerms] using hh

theorem actualPrimeMatrix_changed_low_integral (d : ℕ) (c : ℚ) (hc : ¬ p ∣ c.den)
    (U : Matrix (TailIndex d) (TailIndex d) ℤ_[p])
    (i j : TailIndex d) (hi : actualTailRow d c i < p) :
    Integral ((actualPrimeMatrix p d c * U.map (algebraMap ℤ_[p] ℚ_[p])) i j) := by
  rw [Matrix.mul_apply]
  apply integral_sum
  intro k _
  exact (actualPrimeMatrix_low_integral d c hc i k hi).mul (integral_coe (U k j))

theorem actualCommonDeterminant_bound_of_compatible_caps (d : ℕ) (c : ℚ)
    (hc : ¬ p ∣ c.den)
    (U : Matrix (TailIndex d) (TailIndex d) ℤ_[p]) (hU : IsUnit U.det)
    (e : TailIndex d → ℕ) (he : ∀ j, e j ≤ 4)
    (hcap : ∀ i j, Integral ((p : ℚ_[p]) ^ e j *
      (actualPrimeMatrix p d c * U.map (algebraMap ℤ_[p] ℚ_[p])) i j)) :
    -padicValRat p (actualCommonDeterminant d c) ≤
      (thresholdMass (min (6 * d) (7 * d + 176 - p)) e : ℤ) :=
  actualCommonDeterminant_four_caps d c U hU e he hcap
    (fun i hi j => actualPrimeMatrix_changed_low_integral d c hc U i j hi)

theorem actualCommonDeterminant_integral_large_prime (d : ℕ) (c : ℚ)
    (hc : ¬ p ∣ c.den) (hp : 7 * d + 176 ≤ p) :
    Integral (actualCommonDeterminant d c : ℚ_[p]) := by
  have hentry : ∀ i j, Integral (actualPrimeMatrix p d c i j) := by
    intro i j
    exact actualPrimeMatrix_low_integral d c hc i j ((actualTailRow_lt d c i).trans_le hp)
  have hh := determinant_four_caps (actualPrimeMatrix p d c) ∅ (fun _ => 0)
    (by simp) (by simpa only [pow_zero, one_mul] using hentry) (fun i _ j => hentry i j)
  simpa [thresholdMass, actualPrimeMatrix_det] using hh

theorem actualCommonDeterminant_valuation_large_prime (d : ℕ) (c : ℚ)
    (hc : ¬ p ∣ c.den) (hp : 7 * d + 176 ≤ p) :
    0 ≤ padicValRat p (actualCommonDeterminant d c) := by
  have hh := scaled_integral_valuation (p := p) (actualCommonDeterminant_ne_zero d c) 0
    (by simpa using actualCommonDeterminant_integral_large_prime d c hc hp)
  omega

end Zeta7Auxiliary

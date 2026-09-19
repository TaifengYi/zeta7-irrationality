import Zeta7Proof.AuxiliaryHasseReduction
import Zeta7Proof.ActualTargetClearedEquation

/-! The actual reduced B satisfies its Hasse Frobenius and logarithmic-derivative equations. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
namespace Zeta7Auxiliary
open PowerSeries Zeta7Common
variable (p : ℕ) [Fact p.Prime]

theorem reducedP_constant : constantCoeff (reducedP p) = 1 := by
  rw [reducedP_value]
  simp [map_ofNat]

theorem reducedP_mul_inv : reducedP p * (reducedP p)⁻¹ = 1 :=
  PowerSeries.mul_inv_cancel _ (by rw [reducedP_constant]; exact one_ne_zero)

def hasseGammaSeries (hp : 5 ≤ p) : PowerSeries (ZMod p) :=
  (reducedQuotient p hp : PowerSeries (ZMod p))^2 * ((reducedP p)⁻¹)^(2*((p-1)/3))

theorem hasseGammaSeries_constant (hp : 5 ≤ p) :
    constantCoeff (hasseGammaSeries p hp) = 1 := by
  simp only [hasseGammaSeries, map_mul, map_pow, Polynomial.constantCoeff_coe,
    reducedQuotient_constant, constantCoeff_inv, reducedP_constant, inv_one, one_pow, one_mul]

theorem reducedB_frobenius (hp : 5 ≤ p) :
    reducedB p = hasseGammaSeries p hp *
      expand p (Fact.out : p.Prime).ne_zero (reducedB p) := by
  have h := congrArg (fun z : PowerSeries (ZMod p) => ((reducedP p)⁻¹)^(2*((p-1)/3))*z)
    (reducedB_expansion_cleared p hp)
  have hinv : (reducedP p)⁻¹ * reducedP p = 1 := by
    rw [mul_comm, reducedP_mul_inv]
  calc
    _ = ((reducedP p)⁻¹)^(2*((p-1)/3)) *
        ((reducedP p)^(2*((p-1)/3))*reducedB p) := by
      rw [← mul_assoc, ← mul_pow, hinv, one_pow, one_mul]
    _ = _ := h
    _ = _ := by unfold hasseGammaSeries; ring

theorem euler_frobenius_zero (F : PowerSeries (ZMod p)) :
    euler (expand p (Fact.out : p.Prime).ne_zero F) = 0 := by
  ext j
  rw [euler_coeff, coeff_expand, map_zero]
  split_ifs with hj
  · rw [(ZMod.natCast_eq_zero_iff j p).mpr hj, zero_mul]
  · exact mul_zero _

theorem reducedB_constant : constantCoeff (reducedB p) = 1 := by
  have hi : constantCoeff (integralB p) = 1 := by
    apply Subtype.ext
    rw [← coeff_zero_eq_constantCoeff, integralB, integerSeriesLift, coeff_mk]
    change ((coeff 0 Zeta7Main.BSeries : ℚ) : ℚ_[p]) = 1
    rw [coeff_zero_eq_constantCoeff, BSeries_constant, Rat.cast_one]
  change PadicInt.toZMod (constantCoeff (integralB p)) = 1
  rw [hi, map_one]

theorem reducedB_logarithmic_derivative (hp : 5 ≤ p) :
    euler (reducedB p) * (reducedB p)⁻¹ =
      euler (hasseGammaSeries p hp) * (hasseGammaSeries p hp)⁻¹ := by
  have hd : euler (reducedB p) = euler (hasseGammaSeries p hp) *
      expand p (Fact.out : p.Prime).ne_zero (reducedB p) := by
    nth_rw 1 [reducedB_frobenius p hp]
    rw [euler_mul_general, euler_frobenius_zero, mul_zero, add_zero]
  have hB := PowerSeries.mul_inv_cancel (reducedB p)
    (by rw [reducedB_constant]; exact one_ne_zero)
  have hG := PowerSeries.mul_inv_cancel (hasseGammaSeries p hp)
    (by rw [hasseGammaSeries_constant]; exact one_ne_zero)
  apply mul_left_cancel₀ (a := reducedB p * hasseGammaSeries p hp)
    (mul_ne_zero (by intro h; rw [h, zero_mul] at hB; exact zero_ne_one hB)
      (by intro h; rw [h, zero_mul] at hG; exact zero_ne_one hG))
  calc
    _ = hasseGammaSeries p hp * euler (reducedB p) := by
      linear_combination (hasseGammaSeries p hp * euler (reducedB p)) * hB
    _ = reducedB p * euler (hasseGammaSeries p hp) := by
      rw [hd]
      calc
        _ = (hasseGammaSeries p hp *
          expand p (Fact.out : p.Prime).ne_zero (reducedB p)) *
            euler (hasseGammaSeries p hp) := by ring
        _ = _ := by rw [← reducedB_frobenius p hp]
    _ = _ := by
      linear_combination -(reducedB p * euler (hasseGammaSeries p hp)) * hG

theorem reducedQuotient_degree_lt_prime (hp : 11 ≤ p) :
    (reducedQuotient p (by omega)).natDegree < p := by
  rw [reducedQuotient_degree p hp]
  omega

end Zeta7Auxiliary

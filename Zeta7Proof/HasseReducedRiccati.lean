import Zeta7Proof.AuxiliaryHasseFrobenius

/-! Denominator-cleared Riccati identity for the original B in characteristic p. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
namespace Zeta7Auxiliary
open PowerSeries Zeta7Common Zeta7Main

def hasseP {K : Type*} [CommRing K] : PowerSeries K := 1+13*X+49*X^2
def hasseW {K : Type*} [CommRing K] : PowerSeries K := 8*X*(1+16*X+49*X^2)
def clearedRiccati {K : Type*} [CommRing K] (B : PowerSeries K) : PowerSeries K :=
  hasseP^2*(2*B*euler (euler B)-(euler B)^2)-hasseW*B^2

theorem map_clearedRiccati {K L : Type*} [CommRing K] [CommRing L]
    (φ : K →+* L) (B : PowerSeries K) :
    (clearedRiccati B).map φ = clearedRiccati (B.map φ) := by
  simp only [clearedRiccati, hasseP, hasseW, map_mul, map_pow, map_sub,
    map_add, map_one, map_ofNat, map_X, map_euler]

theorem originalB_clearedRiccati : clearedRiccati BSeries = 0 := by
  have hD : euler (euler BSeries) =
      BSeries * logarithmicB^2 + BSeries*euler logarithmicB := by
    nth_rw 1 [euler_B]
    rw [euler_mul, euler_B]; ring
  have hV := coordinatePotential_eq_rationalPotential
  unfold coordinatePotential at hV
  unfold clearedRiccati
  rw [show (hasseP : PowerSeries ℚ) = shortP from shortP_value.symm]
  unfold hasseW
  rw [hD, euler_B]
  linear_combination shortP^2*BSeries^2*hV + BSeries^2*rationalPotential_cleared

variable (p : ℕ) [Fact p.Prime]

theorem integralB_clearedRiccati : clearedRiccati (integralB p) = 0 := by
  apply PowerSeries.map_injective (algebraMap ℤ_[p] ℚ_[p]) Subtype.val_injective
  rw [map_clearedRiccati, integerSeriesLift_map, ← map_clearedRiccati,
    originalB_clearedRiccati, map_zero, map_zero]

theorem reducedB_clearedRiccati : clearedRiccati (reducedB p) = 0 := by
  rw [reducedB, ← map_clearedRiccati, integralB_clearedRiccati, map_zero]

def hasseRootSeries (hp : 5 ≤ p) : PowerSeries (ZMod p) :=
  (reducedQuotient p hp : PowerSeries (ZMod p)) * (reducedP p)⁻¹^((p-1)/3)

theorem hasseRootSeries_sq (hp : 5 ≤ p) : (hasseRootSeries p hp)^2 = hasseGammaSeries p hp := by
  simp only [hasseRootSeries, hasseGammaSeries, mul_pow, ← pow_mul]
  rw [Nat.mul_comm ((p-1)/3) 2]

theorem hasseRootSeries_constant (hp : 5 ≤ p) : constantCoeff (hasseRootSeries p hp) = 1 := by
  simp only [hasseRootSeries, map_mul, map_pow, constantCoeff_inv, reducedP_constant,
    Polynomial.constantCoeff_coe, reducedQuotient_constant, inv_one, one_pow, mul_one]

theorem hasseRootSeries_ne_zero (hp : 5 ≤ p) : hasseRootSeries p hp ≠ 0 := by
  intro h
  have := hasseRootSeries_constant p hp
  rw [h, map_zero] at this
  exact zero_ne_one this

theorem reducedB_root_factor (hp : 5 ≤ p) : reducedB p =
    (hasseRootSeries p hp)^2 * expand p (Fact.out : p.Prime).ne_zero (reducedB p) := by
  rw [hasseRootSeries_sq]
  exact reducedB_frobenius p hp

theorem hasseRootSeries_equation (hp : 5 ≤ p) :
    4*(reducedP p)^2*euler (euler (hasseRootSeries p hp)) =
      hasseW*hasseRootSeries p hp := by
  let Y := hasseRootSeries p hp
  let F := expand p (Fact.out : p.Prime).ne_zero (reducedB p)
  have hF : euler F = 0 := euler_frobenius_zero p _
  have hd : euler (reducedB p) = 2*Y*euler Y*F := by
    nth_rw 1 [reducedB_root_factor p hp]
    change euler (Y^2*F)=_
    simp only [pow_two, euler_mul_general, hF]; ring
  have hdd : euler (euler (reducedB p)) = 2*((euler Y)^2+Y*euler (euler Y))*F := by
    rw [hd]
    have ht : euler (2:PowerSeries (ZMod p)) = 0 := by
      rw [show (2:PowerSeries (ZMod p)) = C 2 from (map_ofNat C 2).symm]
      simp [euler]
    simp only [euler_mul_general, ht, hF]; ring
  have h := reducedB_clearedRiccati p
  unfold clearedRiccati at h
  rw [hdd, hd] at h
  have hb : reducedB p = Y^2*F := reducedB_root_factor p hp
  rw [hb] at h
  have hY : Y ≠ 0 := hasseRootSeries_ne_zero p hp
  have hF0 : F ≠ 0 := by
    intro hz
    have hz0 := congrArg constantCoeff hz
    simp only [F, constantCoeff_expand, reducedB_constant, map_zero] at hz0
    exact one_ne_zero hz0
  have he : Y^3*F^2*(4*hasseP^2*euler (euler Y)-hasseW*Y)=0 := by
    linear_combination h
  have hh := (mul_eq_zero.mp he).resolve_left
    (mul_ne_zero (pow_ne_zero _ hY) (pow_ne_zero _ hF0))
  simpa only [reducedP_value, hasseP] using sub_eq_zero.mp hh

end Zeta7Auxiliary

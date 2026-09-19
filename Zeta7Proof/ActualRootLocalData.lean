import Zeta7Proof.GermPoleObstruction

/-! The actual Laurent expansions at each root of P. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open scoped LaurentSeries RatFunc
open PowerSeries
namespace Zeta7Germ

def shiftedX (a : ℂ) : ℂ⟦X⟧ := C a + X
def rootDen (a : ℂ) : ℂ⟦X⟧ := C (13 + 98 * a) + C 49 * X
def rootNumerator (a : ℂ) : ℂ⟦X⟧ :=
  C 8 * shiftedX a * (1 + C 16 * shiftedX a + C 49 * shiftedX a ^ 2)
def rootW (a : ℂ) : ℂ⟦X⟧ := rootNumerator a * (rootDen a)⁻¹ ^ 2
def rootRRegular (a : ℂ) : ℂ⟦X⟧ :=
  shiftedX a * (1 + C 10 * shiftedX a) * (rootDen a)⁻¹

theorem root_slope_ne_zero (a : ℂ) (ha : 1 + 13 * a + 49 * a ^ 2 = 0) :
    13 + 98 * a ≠ 0 := by
  have h := (singular_root_algebra a ha).2.2
  intro hz
  norm_num [hz] at h

theorem root_factorization (a : ℂ) (ha : 1 + 13 * a + 49 * a ^ 2 = 0) :
    1 + C 13 * shiftedX a + C 49 * shiftedX a ^ 2 = X * rootDen a := by
  have h := congrArg (C (R := ℂ)) ha
  simp only [map_add, map_mul, map_pow, map_one, map_ofNat, map_zero] at h
  simp only [shiftedX, rootDen, map_add, map_mul, map_ofNat]
  linear_combination h

theorem rootDen_constant (a : ℂ) : constantCoeff (rootDen a) = 13 + 98 * a := by
  simp [rootDen]

theorem rootDen_mul_inv (a : ℂ) (ha : 1 + 13 * a + 49 * a ^ 2 = 0) :
    rootDen a * (rootDen a)⁻¹ = 1 := by
  apply PowerSeries.mul_inv_cancel
  rw [rootDen_constant]
  exact root_slope_ne_zero a ha

theorem coe_powerSeries_inv (f : ℂ⟦X⟧) (hf : constantCoeff f ≠ 0) :
    ((f⁻¹ : ℂ⟦X⟧) : ℂ⸨X⸩) = (f : ℂ⸨X⸩)⁻¹ := by
  have hf0 : f ≠ 0 := fun h => hf (by rw [h, map_zero])
  have he0 : (f : ℂ⸨X⸩) ≠ 0 := by
    intro h
    exact hf0 (HahnSeries.ofPowerSeries_injective (h.trans (map_zero _).symm))
  apply mul_left_cancel₀ he0
  rw [mul_inv_cancel₀ he0, ← PowerSeries.coe_mul, PowerSeries.mul_inv_cancel _ hf,
    PowerSeries.coe_one]

theorem localExpansion_X (a : ℂ) :
    localExpansion a RatFunc.X = (shiftedX a : ℂ⸨X⸩) := by
  simp [localExpansion, RatFunc.laurent_X, embed_X, embed_C, shiftedX, add_comm]

theorem localExpansion_P_root (a : ℂ) (ha : 1 + 13 * a + 49 * a ^ 2 = 0) :
    localExpansion a P = ((X * rootDen a : ℂ⟦X⟧) : ℂ⸨X⸩) := by
  rw [← root_factorization a ha]
  simp [P, localExpansion_X, map_ofNat]

theorem rootW_constant (a : ℂ) (ha : 1 + 13 * a + 49 * a ^ 2 = 0) :
    constantCoeff (rootW a) = -8 * a ^ 2 / 9 := by
  have hroot := singular_root_algebra a ha
  simp only [rootW, rootNumerator, map_mul, map_add, map_pow, map_one,
    constantCoeff_C, constantCoeff_inv, rootDen_constant, shiftedX, constantCoeff_X,
    add_zero]
  rw [hroot.2.1, inv_pow, hroot.2.2]
  norm_num
  ring

theorem localExpansion_V_root (a : ℂ) (ha : 1 + 13 * a + 49 * a ^ 2 = 0) :
    localExpansion a V = HahnSeries.single (-2 : ℤ) 1 * (rootW a : ℂ⸨X⸩) := by
  have hd : constantCoeff (rootDen a) ≠ 0 := by
    rw [rootDen_constant]
    exact root_slope_ne_zero a ha
  rw [V, map_div₀, map_pow, localExpansion_P_root a ha]
  simp only [map_mul, map_add, map_one, map_ofNat, localExpansion_X, map_pow]
  simp only [rootW, rootNumerator, PowerSeries.coe_mul, map_pow,
    coe_powerSeries_inv _ hd, PowerSeries.coe_add, PowerSeries.coe_one,
    PowerSeries.coe_C, map_ofNat, HahnSeries.ofPowerSeries_X]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_pow, mul_pow, HahnSeries.inv_single,
    inv_one, HahnSeries.single_pow]
  norm_num
  ring

theorem localExpansion_R_root (a : ℂ) (ha : 1 + 13 * a + 49 * a ^ 2 = 0) :
    localExpansion a R = HahnSeries.single (-1 : ℤ) 1 * (rootRRegular a : ℂ⸨X⸩) := by
  have hd : constantCoeff (rootDen a) ≠ 0 := by
    rw [rootDen_constant]
    exact root_slope_ne_zero a ha
  rw [R, map_div₀, localExpansion_P_root a ha]
  simp only [map_mul, map_add, map_one, map_ofNat, localExpansion_X]
  simp only [rootRRegular, PowerSeries.coe_mul, coe_powerSeries_inv _ hd,
    PowerSeries.coe_add, PowerSeries.coe_one, PowerSeries.coe_C, map_ofNat,
    HahnSeries.ofPowerSeries_X, div_eq_mul_inv, mul_inv_rev,
    HahnSeries.inv_single, inv_one]
  ring

theorem lowerBound_shifted_powerSeries (f : ℂ⟦X⟧) (m : ℤ) :
    lowerBound (HahnSeries.single m 1 * (f : ℂ⸨X⸩)) m := by
  intro k hk
  rw [HahnSeries.coeff_single_mul, PowerSeries.coeff_coe]
  simp [show k - m < 0 by omega]

theorem actual_V_root_lowerBound (a : ℂ) (ha : 1 + 13 * a + 49 * a ^ 2 = 0) :
    lowerBound (localExpansion a V) (-2) := by
  rw [localExpansion_V_root a ha]
  exact lowerBound_shifted_powerSeries _ _

theorem actual_V_root_coeff (a : ℂ) (ha : 1 + 13 * a + 49 * a ^ 2 = 0) :
    (localExpansion a V).coeff (-2) = -8 * a ^ 2 / 9 := by
  rw [localExpansion_V_root a ha, HahnSeries.coeff_single_mul]
  simpa [PowerSeries.coeff_coe, coeff_zero_eq_constantCoeff] using rootW_constant a ha

theorem actual_V_root_coeff_ne_zero (a : ℂ) (ha : 1 + 13 * a + 49 * a ^ 2 = 0) :
    (localExpansion a V).coeff (-2) ≠ 0 := by
  rw [actual_V_root_coeff a ha]
  exact div_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2
    (singular_root_algebra a ha).1)) (by norm_num)

theorem actual_DV_root_lowerBound (a : ℂ) (ha : 1 + 13 * a + 49 * a ^ 2 = 0) :
    lowerBound (localExpansion a (rationalD V)) (-3) := by
  rw [localExpansion_rationalD]
  exact lowerBound_localD a (actual_V_root_lowerBound a ha)

theorem actual_DV_root_coeff (a : ℂ) (ha : 1 + 13 * a + 49 * a ^ 2 = 0) :
    (localExpansion a (rationalD V)).coeff (-3) = 16 * a ^ 3 / 9 := by
  rw [localExpansion_rationalD]
  have h := localD_leading a (actual_V_root_lowerBound a ha)
  rw [actual_V_root_coeff a ha] at h
  convert h using 1 <;> norm_num <;> ring

theorem actual_R_root_lowerBound (a : ℂ) (ha : 1 + 13 * a + 49 * a ^ 2 = 0) :
    lowerBound (localExpansion a R) (-1) := by
  rw [localExpansion_R_root a ha]
  exact lowerBound_shifted_powerSeries _ _

end Zeta7Germ

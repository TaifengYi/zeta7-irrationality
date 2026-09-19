import Zeta7Proof.GermInfinityCalculus

/-! A rational Riccati solution must decay at infinity. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open scoped RatFunc LaurentSeries
open HahnSeries
namespace Zeta7Germ

def infinityRiccati (v u : ℂ⸨X⸩) : ℂ⸨X⸩ :=
  laurentD (laurentD u) - 3 * u * laurentD u + u ^ 3 - v * u + laurentD v / 2

theorem infinityExpansion_riccati (u : RatFunc ℂ) :
    infinityExpansion (riccati u) = infinityRiccati (infinityExpansion V) (infinityExpansion u) := by
  simp [riccati, infinityRiccati, infinityExpansion_rationalD, map_ofNat]
  ring

theorem infinityRiccati_pole {v u : ℂ⸨X⸩} {n : ℤ}
    (hn : n < 0) (hu : lowerBound u n) (hv : lowerBound v 1) :
    (infinityRiccati v u).coeff (3 * n) = u.coeff n ^ 3 := by
  have hD2 := lowerBound_euler (lowerBound_euler hu)
  have huD := lowerBound_mul hu (lowerBound_euler hu)
  have hvu := lowerBound_mul hv hu
  have hDv := lowerBound_euler hv
  simp only [infinityRiccati, mul_assoc, coeff_sub, coeff_add,
    laurent_coeff_three, laurent_coeff_half]
  rw [hD2 _ (by omega), huD _ (by omega), hvu _ (by omega), hDv _ (by omega),
    lowerBound_pow_leading hu]
  ring

theorem actual_riccati_infinity_regular (u : RatFunc ℂ) (he : riccati u = 0) :
    lowerBound (infinityExpansion u) 0 := by
  intro k hk
  by_contra hc
  have hn : (infinityExpansion u).order < 0 :=
    lt_of_le_of_lt (order_le_of_coeff_ne_zero hc) hk
  have hu : lowerBound (infinityExpansion u) (infinityExpansion u).order :=
    fun _ hi => coeff_eq_zero_of_lt_order hi
  have hl := infinityRiccati_pole hn hu infinity_V_lowerBound
  have hz := congrArg infinityExpansion he
  rw [infinityExpansion_riccati, map_zero] at hz
  rw [hz, coeff_zero] at hl
  have hu0 : (infinityExpansion u).coeff (infinityExpansion u).order ≠ 0 :=
    mt coeff_order_eq_zero.mp (ne_zero_of_coeff_ne_zero hc)
  exact pow_ne_zero 3 hu0 hl.symm

theorem actual_riccati_infinity_constant (u : RatFunc ℂ) (he : riccati u = 0) :
    (infinityExpansion u).coeff 0 = 0 := by
  have hu := actual_riccati_infinity_regular u he
  have hprod := lowerBound_mul_leading hu (lowerBound_euler hu)
  have hcub := lowerBound_pow_leading hu
  have hvu := lowerBound_mul infinity_V_lowerBound hu
  have hvd := lowerBound_euler infinity_V_lowerBound
  have hz := congrArg infinityExpansion he
  rw [infinityExpansion_riccati, map_zero] at hz
  have hc := congrArg (fun f : ℂ⸨X⸩ => f.coeff 0) hz
  norm_num only [zero_add, mul_zero] at hprod hcub
  simp only [infinityRiccati, mul_assoc, coeff_sub, coeff_add,
    laurent_coeff_three, laurent_coeff_half, hprod, hcub,
    hvu 0 (by norm_num), hvd 0 (by norm_num), laurentD_coeff_zero,
    zero_mul, mul_zero, zero_add, sub_zero, zero_div, add_zero, coeff_zero] at hc
  exact (pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0)).mp hc

theorem actual_riccati_infinity_decay (u : RatFunc ℂ) (he : riccati u = 0) :
    lowerBound (infinityExpansion u) 1 := by
  intro k hk
  by_cases hn : k < 0
  · exact actual_riccati_infinity_regular u he k hn
  · have : k = 0 := by omega
    subst k
    exact actual_riccati_infinity_constant u he

def riccatiRho (u : RatFunc ℂ) : RatFunc ℂ := u / RatFunc.X

theorem actual_rho_infinity_decay (u : RatFunc ℂ) (he : riccati u = 0) :
    lowerBound (infinityExpansion (riccatiRho u)) 2 := by
  intro k hk
  rw [riccatiRho, map_div₀, infinityExpansion_X]
  simp only [div_eq_mul_inv,
    HahnSeries.inv_single, neg_neg, inv_one, HahnSeries.coeff_mul_single]
  rw [actual_riccati_infinity_decay u he (k - 1) (by omega), zero_mul]

end Zeta7Germ

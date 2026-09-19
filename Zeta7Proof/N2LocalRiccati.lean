import Zeta7Proof.ActualFinitePoleExclusion

/-! Local pole restrictions for the actual rational Riccati equation. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open scoped RatFunc LaurentSeries
open HahnSeries
namespace Zeta7Germ

def localRiccati (a : ℂ) (v u : ℂ⸨X⸩) : ℂ⸨X⸩ :=
  localD a (localD a u) + 3 * u * localD a u + u ^ 3 - v * u - localD a v / 2

theorem localExpansion_riccati (a : ℂ) (u : RatFunc ℂ) :
    localExpansion a (riccati u) = localRiccati a (localExpansion a V) (localExpansion a u) := by
  simp [riccati, localRiccati, localExpansion_rationalD, map_ofNat]

theorem laurent_coeff_nat_mul (r : ℕ) (f : ℂ⸨X⸩) (n : ℤ) :
    ((r : ℂ⸨X⸩) * f).coeff n = (r : ℂ) * f.coeff n := by
  rw [← map_natCast (HahnSeries.C (Γ := ℤ) (R := ℂ)), C_apply, coeff_single_zero_mul]

theorem laurent_coeff_three (f : ℂ⸨X⸩) (n : ℤ) :
    ((3 : ℂ⸨X⸩) * f).coeff n = 3 * f.coeff n := laurent_coeff_nat_mul 3 f n

theorem laurent_coeff_half (f : ℂ⸨X⸩) (n : ℤ) : (f / 2).coeff n = f.coeff n / 2 := by
  have hh : (2 : ℂ⸨X⸩)⁻¹ = HahnSeries.C (1 / 2 : ℂ) := by
    rw [map_div₀, map_one, map_ofNat, one_div]
  simp only [div_eq_mul_inv, hh, C_apply, coeff_mul_single_zero]
  ring

theorem lowerBound_pow_leading {f : ℂ⸨X⸩} {n : ℤ} (hf : lowerBound f n) :
    (f ^ 3).coeff (3 * n) = f.coeff n ^ 3 := by
  have h2 := lowerBound_mul hf hf
  have h3 := lowerBound_mul_leading h2 hf
  rw [lowerBound_mul_leading hf hf] at h3
  simpa [pow_succ, show n + n + n = 3 * n by omega] using h3

theorem localRiccati_high_pole (a : ℂ) {v u : ℂ⸨X⸩} {n : ℤ}
    (hn : n < -1) (hu : lowerBound u n) (hv : lowerBound v (-2)) :
    (localRiccati a v u).coeff (3 * n) = u.coeff n ^ 3 := by
  have hD2 := lowerBound_localD a (lowerBound_localD a hu)
  have huD := lowerBound_mul hu (lowerBound_localD a hu)
  have hvu := lowerBound_mul hv hu
  have hDv := lowerBound_localD a hv
  simp only [localRiccati, mul_assoc, coeff_sub, coeff_add,
    laurent_coeff_three, laurent_coeff_half]
  rw [hD2 _ (by omega), huD _ (by omega), hvu _ (by omega), hDv _ (by omega),
    lowerBound_pow_leading hu]
  ring

theorem localRiccati_zero_pole {v u : ℂ⸨X⸩} {n : ℤ}
    (hn : n < 0) (hu : lowerBound u n) (hv : lowerBound v 1) :
    (localRiccati 0 v u).coeff (3 * n) = u.coeff n ^ 3 := by
  have hD2 := lowerBound_euler (lowerBound_euler hu)
  have huD := lowerBound_mul hu (lowerBound_euler hu)
  have hvu := lowerBound_mul hv hu
  have hDv := lowerBound_euler hv
  simp only [localRiccati, localD_zero, mul_assoc, coeff_sub, coeff_add,
    laurent_coeff_three, laurent_coeff_half]
  rw [hD2 _ (by omega), huD _ (by omega), hvu _ (by omega), hDv _ (by omega),
    lowerBound_pow_leading hu]
  ring

theorem actual_riccati_local_bound (u : RatFunc ℂ) (he : riccati u = 0) (a : ℂ) :
    lowerBound (localExpansion a u) (-1) := by
  have hv : lowerBound (localExpansion a V) (-2) := by
    by_cases hp : 1 + 13 * a + 49 * a ^ 2 = 0
    · exact actual_V_root_lowerBound a hp
    · intro k hk
      exact actual_V_regular_lowerBound a hp k (by omega)
  intro k hk
  by_contra hc
  have hn : (localExpansion a u).order < -1 :=
    lt_of_le_of_lt (order_le_of_coeff_ne_zero hc) hk
  have hu : lowerBound (localExpansion a u) (localExpansion a u).order :=
    fun _ hi => coeff_eq_zero_of_lt_order hi
  have hl := localRiccati_high_pole a hn hu hv
  have hz := congrArg (localExpansion a) he
  rw [localExpansion_riccati, map_zero] at hz
  rw [hz, coeff_zero] at hl
  have hu0 : (localExpansion a u).coeff (localExpansion a u).order ≠ 0 :=
    mt coeff_order_eq_zero.mp (ne_zero_of_coeff_ne_zero hc)
  exact pow_ne_zero 3 hu0 hl.symm

theorem actual_riccati_zero_regular (u : RatFunc ℂ) (he : riccati u = 0) :
    lowerBound (localExpansion 0 u) 0 := by
  intro k hk
  by_contra hc
  have hn : (localExpansion 0 u).order < 0 :=
    lt_of_le_of_lt (order_le_of_coeff_ne_zero hc) hk
  have hu : lowerBound (localExpansion 0 u) (localExpansion 0 u).order :=
    fun _ hi => coeff_eq_zero_of_lt_order hi
  have hl := localRiccati_zero_pole hn hu actual_V_zero_lowerBound
  have hz := congrArg (localExpansion 0) he
  rw [localExpansion_riccati, map_zero] at hz
  rw [hz, coeff_zero] at hl
  have hu0 : (localExpansion 0 u).coeff (localExpansion 0 u).order ≠ 0 :=
    mt coeff_order_eq_zero.mp (ne_zero_of_coeff_ne_zero hc)
  exact pow_ne_zero 3 hu0 hl.symm

theorem localRiccati_simple_coefficient (a : ℂ) {v u : ℂ⸨X⸩}
    (hu : lowerBound u (-1)) (hv : lowerBound v (-2)) :
    (localRiccati a v u).coeff (-3) = u.coeff (-1) ^ 3 - 3 * a * u.coeff (-1) ^ 2 +
      2 * a ^ 2 * u.coeff (-1) - v.coeff (-2) * u.coeff (-1) + a * v.coeff (-2) := by
  have h1 := localD_two_leading a hu
  have h2 := lowerBound_mul_leading hu (lowerBound_localD a hu)
  have h3 := lowerBound_pow_leading hu
  have h4 := lowerBound_mul_leading hv hu
  have h5 := localD_leading a hv
  rw [localD_leading a hu] at h2
  norm_num only [Int.reduceSub, Int.reduceAdd, Int.reduceMul, Int.cast_neg,
    Int.cast_one, Int.cast_ofNat] at h1 h2 h3 h4 h5
  simp only [localRiccati, mul_assoc, coeff_sub, coeff_add,
    laurent_coeff_three, laurent_coeff_half, h1, h2, h3, h4, h5]
  ring

theorem actual_riccati_root_residue (u : RatFunc ℂ) (he : riccati u = 0)
    (a : ℂ) (ha : 1 + 13 * a + 49 * a ^ 2 = 0) :
    let k := (localExpansion a u).coeff (-1) / a
    k = 1 ∨ k = 2 / 3 ∨ k = 4 / 3 := by
  dsimp only
  apply (indicial_roots _).mp
  have hl := localRiccati_simple_coefficient a (actual_riccati_local_bound u he a)
    (actual_V_root_lowerBound a ha)
  have hz := congrArg (localExpansion a) he
  rw [localExpansion_riccati, map_zero] at hz
  rw [hz, coeff_zero, actual_V_root_coeff a ha] at hl
  have ha0 := (singular_root_algebra a ha).1
  apply mul_left_cancel₀ (pow_ne_zero 3 ha0)
  rw [mul_zero]
  dsimp [indicial]
  field_simp [ha0]
  linear_combination -9 * hl

theorem actual_riccati_ordinary_residue (u : RatFunc ℂ) (he : riccati u = 0)
    (a : ℂ) (ha : a ≠ 0) (hp : 1 + 13 * a + 49 * a ^ 2 ≠ 0) :
    let k := (localExpansion a u).coeff (-1) / a
    k = 0 ∨ k = 1 ∨ k = 2 := by
  dsimp only
  have hv := actual_V_regular_lowerBound a hp
  have hl := localRiccati_simple_coefficient a (actual_riccati_local_bound u he a)
    (fun k hk => hv k (by omega))
  have hz := congrArg (localExpansion a) he
  rw [localExpansion_riccati, map_zero] at hz
  rw [hz, coeff_zero, hv (-2) (by norm_num)] at hl
  let k := (localExpansion a u).coeff (-1) / a
  have hk : k * (k - 1) * (k - 2) = 0 := by
    dsimp [k]
    field_simp [ha]
    linear_combination -hl
  rcases mul_eq_zero.mp hk with hk | hk
  · rcases mul_eq_zero.mp hk with hk | hk
    · exact Or.inl hk
    · exact Or.inr (Or.inl (sub_eq_zero.mp hk))
  · exact Or.inr (Or.inr (sub_eq_zero.mp hk))

theorem laurentD_coeff_zero (f : ℂ⸨X⸩) : (laurentD f).coeff 0 = 0 := by
  change ((0 : ℤ) : ℂ) * f.coeff 0 = 0
  simp

theorem actual_riccati_zero_constant (u : RatFunc ℂ) (he : riccati u = 0) :
    (localExpansion 0 u).coeff 0 = 0 := by
  have hu := actual_riccati_zero_regular u he
  have hprod := lowerBound_mul_leading hu (lowerBound_euler hu)
  have hcub := lowerBound_pow_leading hu
  have hvu := lowerBound_mul actual_V_zero_lowerBound hu
  have hvd := lowerBound_euler actual_V_zero_lowerBound
  have hz := congrArg (localExpansion 0) he
  rw [localExpansion_riccati, map_zero] at hz
  have hc := congrArg (fun f : ℂ⸨X⸩ => f.coeff 0) hz
  norm_num only [zero_add, mul_zero] at hprod hcub
  simp only [localRiccati, localD_zero, mul_assoc, coeff_sub, coeff_add,
    laurent_coeff_three, laurent_coeff_half, hprod, hcub,
    hvu 0 (by norm_num), hvd 0 (by norm_num), laurentD_coeff_zero,
    Int.cast_zero, zero_mul, mul_zero, zero_add, sub_zero, zero_div, coeff_zero] at hc
  exact (pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0)).mp hc

end Zeta7Germ

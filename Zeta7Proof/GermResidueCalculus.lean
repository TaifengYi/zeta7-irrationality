import Zeta7Proof.GermInfinityCalculus

/-! Algebraic partial fractions and the residue sum, using rational Laurent expansions. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open scoped RatFunc LaurentSeries
open PowerSeries
namespace Zeta7Germ

theorem lowerBound_sub {f g : ℂ⸨X⸩} {n : ℤ} (hf : lowerBound f n) (hg : lowerBound g n) :
    lowerBound (f - g) n := by
  intro k hk
  simp [HahnSeries.coeff_sub, hf k hk, hg k hk]

theorem lowerBound_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ⸨X⸩) (n : ℤ)
    (hf : ∀ i ∈ s, lowerBound (f i) n) : lowerBound (∑ i ∈ s, f i) n := by
  intro k hk
  simp only [HahnSeries.coeff_sum]
  exact Finset.sum_eq_zero (fun i hi => hf i hi k hk)

theorem local_regular_of_denom_ne_zero (f : RatFunc ℂ) (a : ℂ)
    (ha : f.denom.eval a ≠ 0) : lowerBound (localExpansion a f) 0 := by
  let pn : ℂ⟦X⟧ := (Polynomial.taylor a f.num : Polynomial ℂ)
  let pd : ℂ⟦X⟧ := (Polynomial.taylor a f.denom : Polynomial ℂ)
  have hd : constantCoeff pd ≠ 0 := by
    simpa [pd, Polynomial.taylor_coeff_zero] using ha
  have he : localExpansion a f = ((pn * pd⁻¹ : ℂ⟦X⟧) : ℂ⸨X⸩) := by
    conv_lhs => rw [← RatFunc.num_div_denom f]
    simp only [← RatFunc.coePolynomial_eq_algebraMap, map_div₀,
      localExpansion_polynomial, embed_polynomial]
    rw [PowerSeries.coe_mul, coe_powerSeries_inv _ hd]
    rfl
  rw [he]
  exact lowerBound_powerSeries _

def simpleFraction (a r : ℂ) : RatFunc ℂ := RatFunc.C r / (RatFunc.X - RatFunc.C a)

theorem localExpansion_C (a r : ℂ) : localExpansion a (RatFunc.C r) = HahnSeries.C r := by
  simp [localExpansion, embed_C]

theorem simpleFraction_local_self (a r : ℂ) :
    localExpansion a (simpleFraction a r) = HahnSeries.single (-1 : ℤ) r := by
  simp [simpleFraction, localExpansion_X, localExpansion_C, shiftedX,
    div_eq_mul_inv, HahnSeries.C_apply, HahnSeries.inv_single, HahnSeries.single_mul_single]

theorem simpleFraction_local_other (a b r : ℂ) (hab : a ≠ b) :
    localExpansion a (simpleFraction b r) =
      ((C r * (C (a - b) + X)⁻¹ : ℂ⟦X⟧) : ℂ⸨X⸩) := by
  have hd : constantCoeff (C (a - b) + X) ≠ 0 := by simpa using sub_ne_zero.mpr hab
  rw [PowerSeries.coe_mul, coe_powerSeries_inv _ hd]
  simp [simpleFraction, localExpansion_X, localExpansion_C, shiftedX, div_eq_mul_inv]
  ring

theorem simpleFraction_local_bound (a b r : ℂ) :
    lowerBound (localExpansion a (simpleFraction b r)) (-1) := by
  by_cases hab : a = b
  · subst b
    rw [simpleFraction_local_self]
    intro k hk
    simp [HahnSeries.coeff_single, show k ≠ (-1 : ℤ) by omega]
  · rw [simpleFraction_local_other a b r hab]
    intro k hk
    exact lowerBound_powerSeries _ k (by omega)

theorem simpleFraction_local_residue (a b r : ℂ) :
    (localExpansion a (simpleFraction b r)).coeff (-1) = if a = b then r else 0 := by
  by_cases hab : a = b
  · subst b
    simp [simpleFraction_local_self]
  · rw [if_neg hab, simpleFraction_local_other a b r hab]
    exact lowerBound_powerSeries _ (-1) (by norm_num)

theorem simpleFraction_infinity (a r : ℂ) :
    infinityExpansion (simpleFraction a r) =
      HahnSeries.single (1 : ℤ) 1 * ((C r * (1 - C a * X)⁻¹ : ℂ⟦X⟧) : ℂ⸨X⸩) := by
  have hd : constantCoeff (1 - C a * X : ℂ⟦X⟧) ≠ 0 := by simp
  have he : simpleFraction a r = RatFunc.C r * RatFunc.X⁻¹ /
      (1 - RatFunc.C a * RatFunc.X⁻¹) := by
    dsimp [simpleFraction]
    field_simp [RatFunc.X_ne_zero]
  rw [he, map_div₀, map_mul, map_sub, map_mul, map_one, map_inv₀,
    infinityExpansion_X, infinityExpansion_C, infinityExpansion_C]
  rw [PowerSeries.coe_mul, coe_powerSeries_inv _ hd]
  simp only [div_eq_mul_inv, HahnSeries.inv_single, neg_neg, inv_one,
    PowerSeries.coe_C, PowerSeries.coe_sub, PowerSeries.coe_one, PowerSeries.coe_mul,
    HahnSeries.ofPowerSeries_X]
  ring

theorem simpleFraction_infinity_bound (a r : ℂ) :
    lowerBound (infinityExpansion (simpleFraction a r)) 1 := by
  rw [simpleFraction_infinity]
  exact lowerBound_shifted_powerSeries _ _

theorem simpleFraction_infinity_coeff (a r : ℂ) :
    (infinityExpansion (simpleFraction a r)).coeff 1 = r := by
  rw [simpleFraction_infinity, HahnSeries.coeff_single_mul]
  simp [PowerSeries.coeff_coe, PowerSeries.coeff_zero_eq_constantCoeff]

def finitePoles (f : RatFunc ℂ) : Finset ℂ := f.denom.roots.toFinset
def residue (a : ℂ) (f : RatFunc ℂ) : ℂ := (localExpansion a f).coeff (-1)

theorem regular_outside_finitePoles (f : RatFunc ℂ) (a : ℂ) (ha : a ∉ finitePoles f) :
    lowerBound (localExpansion a f) 0 := by
  apply local_regular_of_denom_ne_zero
  intro hz
  apply ha
  simp [finitePoles, Polynomial.mem_roots f.denom_ne_zero, Polynomial.IsRoot, hz]

theorem residue_zero_outside_finitePoles (f : RatFunc ℂ) (a : ℂ) (ha : a ∉ finitePoles f) :
    residue a f = 0 := regular_outside_finitePoles f a ha (-1) (by norm_num)

def principalFractions (f : RatFunc ℂ) : RatFunc ℂ :=
  ∑ a ∈ finitePoles f, simpleFraction a (residue a f)

theorem principalFractions_local_residue (f : RatFunc ℂ) (a : ℂ) :
    residue a (principalFractions f) = residue a f := by
  classical
  simp only [residue, principalFractions, map_sum, HahnSeries.coeff_sum, simpleFraction_local_residue]
  by_cases ha : a ∈ finitePoles f
  · simp [eq_comm, ha]
  · simp [eq_comm, ha, show (localExpansion a f).coeff (-1) = 0 from
      residue_zero_outside_finitePoles f a ha]

theorem principalFractions_remainder_polynomial (f : RatFunc ℂ)
    (hf : ∀ a : ℂ, lowerBound (localExpansion a f) (-1)) :
    ∃ p : Polynomial ℂ, f - principalFractions f = (p : RatFunc ℂ) := by
  apply polynomial_of_denom_no_roots
  intro a
  apply denom_no_root_of_local_regular
  intro k hk
  rw [map_sub, HahnSeries.coeff_sub]
  by_cases hk1 : k < -1
  · rw [hf a k hk1]
    have hb : lowerBound (localExpansion a (principalFractions f)) (-1) := by
      simp only [principalFractions, map_sum]
      exact lowerBound_sum _ _ _ (fun b _ => simpleFraction_local_bound a b _)
    rw [hb k hk1, sub_self]
  · have : k = -1 := by omega
    subst k
    exact sub_eq_zero.mpr (principalFractions_local_residue f a).symm

theorem partial_fractions_of_simple_poles_and_decay (f : RatFunc ℂ)
    (hf : ∀ a : ℂ, lowerBound (localExpansion a f) (-1))
    (hi : lowerBound (infinityExpansion f) 1) : f = principalFractions f := by
  obtain ⟨p, hp⟩ := principalFractions_remainder_polynomial f hf
  have hsum : lowerBound (infinityExpansion (principalFractions f)) 1 := by
    simp only [principalFractions, map_sum]
    exact lowerBound_sum _ _ _ (fun a _ => simpleFraction_infinity_bound a _)
  have hdiff := lowerBound_sub hi hsum
  rw [← map_sub, hp] at hdiff
  have hz := polynomial_zero_of_infinity_decay p hdiff
  exact sub_eq_zero.mp (by simpa [hz] using hp)

theorem residue_sum_eq_zero (f : RatFunc ℂ)
    (hf : ∀ a : ℂ, lowerBound (localExpansion a f) (-1))
    (hi : lowerBound (infinityExpansion f) 2) : ∑ a ∈ finitePoles f, residue a f = 0 := by
  have he := partial_fractions_of_simple_poles_and_decay f hf (fun k hk => hi k (by omega))
  have hc := congrArg (fun g : RatFunc ℂ => (infinityExpansion g).coeff 1) he
  rw [hi 1 (by norm_num)] at hc
  simpa [principalFractions, map_sum, HahnSeries.coeff_sum, simpleFraction_infinity_coeff] using hc.symm

end Zeta7Germ

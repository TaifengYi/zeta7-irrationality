import Zeta7Proof.AuxiliaryFourthLayerK

/-! The exceptional primitive carries of the actual `J1, J2` in terms of the paper's short
series `U, W` and the coefficients of `hasseCarryPolynomial`, together with the complete
fourth-layer congruences for `J1` and `J2`. Every division is by a proved unit. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
namespace Zeta7Auxiliary
open PowerSeries Zeta7Main Zeta7Common
open scoped LaurentSeries

variable {p : ℕ} [Fact p.Prime]

/-! ### The reduced forcing and the carry polynomial as a series identity -/

abbrev integralR (p : ℕ) [Fact p.Prime] : PowerSeries ℤ_[p] :=
  integerSeriesLift p rationalForcing rationalForcing_integer

def reducedR (p : ℕ) [Fact p.Prime] : PowerSeries (ZMod p) :=
  (integralR p).map PadicInt.toZMod

theorem reducedP_mul_reducedR : reducedP p * reducedR p = X * (1 + 10 * X) := by
  have hi : integralP p * integralR p = X * (1 + 10 * X) := by
    apply PowerSeries.map_injective (algebraMap ℤ_[p] ℚ_[p]) Subtype.val_injective
    rw [map_mul, integerSeriesLift_map, integerSeriesLift_map, ← map_mul,
      rationalForcing_cleared]
    simp [map_ofNat]
  have h := congrArg (PowerSeries.map (PadicInt.toZMod (p := p))) hi
  simpa [reducedP, reducedR, map_ofNat] using h

theorem reducedR_eq : reducedR p = X * (1 + 10 * X) * (reducedP p)⁻¹ := by
  calc
    reducedR p = ((reducedP p)⁻¹ * reducedP p) * reducedR p := by
      rw [mul_comm (reducedP p)⁻¹, reducedP_mul_inv, one_mul]
    _ = _ := by rw [mul_assoc, reducedP_mul_reducedR]; ring

/-- Series form of `hasseCarryPolynomial_fraction`, transported through the Laurent embedding:
`R̄ Γ = A · P̄(X)^{-p}`. -/
theorem reducedR_gamma (hp : 11 ≤ p) :
    reducedR p * hasseGammaSeries p (by omega) =
      (hasseCarryPolynomial p hp : PowerSeries (ZMod p)) * ((reducedP p)⁻¹)^p := by
  have h := congrArg Zeta7FiniteCalculus.embed (hasseCarryPolynomial_fraction p hp)
  have he (f : Polynomial (ZMod p)) : Zeta7FiniteCalculus.embed (primePolynomialMap p f) =
      primeLaurentMap p (f : PowerSeries (ZMod p)) := Zeta7FiniteCalculus.embed_polynomial f
  simp only [map_mul, map_div₀, map_pow, he, hassePolyP_coe_reducedP,
    hasseGammaRational_embed] at h
  refine HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := ZMod p)
    (?_ : primeLaurentMap p _ = primeLaurentMap p _)
  rw [reducedR_eq, map_mul, map_mul, map_mul, map_mul, map_pow, reducedP_laurent_inverse]
  rw [div_eq_mul_inv, div_eq_mul_inv, ← inv_pow] at h
  have h1 : ((Polynomial.X : Polynomial (ZMod p)) : PowerSeries (ZMod p)) = X :=
    Polynomial.coe_X
  have h2 : ((1 + 10 * Polynomial.X : Polynomial (ZMod p)) : PowerSeries (ZMod p)) =
      1 + 10 * X := by simp
  rw [h1, h2] at h
  exact h

def hasseCarrySeries (p : ℕ) [Fact p.Prime] (hp : 11 ≤ p) : PowerSeries (ZMod p) :=
  (hasseCarryPolynomial p hp : PowerSeries (ZMod p))

/-- The short series `P̄⁻¹ F`. -/
def carryShort (p : ℕ) [Fact p.Prime] : PowerSeries (ZMod p) :=
  (reducedP p)⁻¹ * hasseShortSeries p

/-! ### The actual third layer of DK -/

theorem rationalForcing_cap_zero (N : ℕ) :
    Cap N 0 (rationalForcing.map (algebraMap ℚ ℚ_[p])) :=
  rationalForcing_integer.cap_zero N

theorem map_integralR : (integralR p).map (algebraMap ℤ_[p] ℚ_[p]) =
    rationalForcing.map (algebraMap ℚ ℚ_[p]) := integerSeriesLift_map p _ _

/-- **P3 third layer of DK**, as `A · (P̄⁻¹F)(X^p)`. -/
theorem actualDKThird_carry (hp : 11 ≤ p) (c : ℚ) (hc : ¬p ∣ c.den)
    (N : ℕ) (hN : N ≤ p^2) (n : ℕ) (hn : n < N) :
    actualDKThird c hc N hN n hn =
      coeff n (hasseCarrySeries p hp * expand p (Fact.out : p.Prime).ne_zero (carryShort p)) := by
  have hp7 : p ≠ 7 := by omega
  have hnp : n < p^2 := hn.trans_le hN
  have hRS := (rationalForcing_cap_zero (p := p) N).mul (singularH_cap_zero N hN)
  have hRR := (rationalForcing_cap_zero (p := p) N).mul (regularH_cap_zero c hc N)
  rw [← map_mul] at hRS hRR
  have hy : Integral (coeff n ((rationalForcing * singularH p).map (algebraMap ℚ ℚ_[p]))) := by
    simpa only [Nat.add_zero, _root_.pow_zero, one_mul] using hRS n hn
  have hz : Integral ((p : ℚ_[p])^2 *
      coeff n ((rationalForcing * regularH p c).map (algebraMap ℚ ℚ_[p]))) :=
    ((integral_nat p).pow 2).mul (by simpa only [Nat.add_zero, _root_.pow_zero, one_mul] using hRR n hn)
  have hq : (p : PowerSeries ℚ)^3 * euler (quadratic rationalPotential (rationalH c)) =
      rationalForcing * singularH p + (p : PowerSeries ℚ)^3 * (rationalForcing * regularH p c) := by
    have hs := rationalH_scaled_depletion hp7 c
    rw [show C ((p : ℚ)^3) = (p : PowerSeries ℚ)^3 by rw [map_pow, map_natCast]] at hs
    rw [rationalH_quadratic_derivative]
    linear_combination rationalForcing * hs
  have he := congrArg (fun f : PowerSeries ℚ => coeff n (f.map (algebraMap ℚ ℚ_[p]))) hq
  simp only [map_mul, map_add, map_pow, map_natCast] at he
  rw [coeff_natCast_pow_mul, coeff_natCast_pow_mul] at he
  have he' : (p : ℚ_[p])^3 * coeff n (euler ((quadratic rationalPotential (rationalH c)).map
      (algebraMap ℚ ℚ_[p]))) =
      coeff n ((rationalForcing * singularH p).map (algebraMap ℚ ℚ_[p])) +
        (p : ℚ_[p]) * ((p : ℚ_[p])^2 *
          coeff n ((rationalForcing * regularH p c).map (algebraMap ℚ ℚ_[p]))) := by
    rw [← map_euler, map_mul (PowerSeries.map (algebraMap ℚ ℚ_[p]))
      rationalForcing (singularH p), map_mul (PowerSeries.map (algebraMap ℚ ℚ_[p]))
      rationalForcing (regularH p c)]
    linear_combination he
  unfold actualDKThird layerAt
  rw [layerCoefficient_eq_residue]
  refine (integralResidue_congr_mod_prime _ hy hz he').trans ?_
  have hlift : ((coeff n (integralR p * integralShortSingular p) : ℤ_[p]) : ℚ_[p]) =
      coeff n ((rationalForcing * singularH p).map (algebraMap ℚ ℚ_[p])) := by
    rw [map_mul (PowerSeries.map (algebraMap ℚ ℚ_[p])) rationalForcing (singularH p)]
    rw [show ((coeff n (integralR p * integralShortSingular p) : ℤ_[p]) : ℚ_[p]) =
      coeff n ((integralR p * integralShortSingular p).map (algebraMap ℤ_[p] ℚ_[p])) by
        rw [coeff_map]; rfl]
    rw [map_mul (PowerSeries.map (algebraMap ℤ_[p] ℚ_[p])), map_integralR]
    exact (coeff_mul_congr _ n (fun k hk => (singularH_coeff_eq_short k (by omega)))).symm
  rw [integralResidue_eq_of_lift hy _ hlift, ← coeff_map, map_mul, reducedShortSingular_eq,
    ← mul_assoc]
  change coeff n (reducedR p * hasseGammaSeries p (by omega) * _) = _
  rw [reducedR_gamma hp, zmod_series_frobenius, mul_assoc, ← map_mul]
  unfold hasseCarrySeries carryShort
  apply coeff_mul_congr
  intro k hk
  refine coeff_expand_congr_short (fun j hj => ?_) k (by omega)
  exact coeff_mul_congr _ j (fun i hi => (hasseShortSeries_coeff_lt_reduced i (by omega)).symm)

/-! ### Coefficient extraction for a carry polynomial of degree at most `2p` -/

theorem dvd_residue_cases {k r m t : ℕ} (hr1 : 1 ≤ r) (hrp : r < p) (hk : k ≤ 2*p)
    (h : k + r + p*t = m*p) : k = p - r ∨ k = 2*p - r := by
  have hp0 := (Fact.out : p.Prime).pos
  have htm : t < m := by
    by_contra hc
    have : m*p ≤ p*t := by rw [mul_comm]; exact Nat.mul_le_mul_left p (not_lt.mp hc)
    omega
  have hs : p * (m - t) = k + r := by
    rw [Nat.mul_sub, mul_comm p m]; omega
  generalize m - t = s at hs
  have hs1 : 1 ≤ s := by
    rcases Nat.eq_zero_or_pos s with h0 | h0
    · subst h0; omega
    · exact h0
  have hs3 : s < 3 := by
    by_contra hc
    have : p*3 ≤ p*s := Nat.mul_le_mul_left p (by omega)
    omega
  interval_cases s <;> omega

theorem coeff_carry_extract {R : Type*} [CommRing R] (A : Polynomial R)
    (hA : A.natDegree ≤ 2*p) (f : PowerSeries R) (m r : ℕ) (hm : 0 < m)
    (hr1 : 1 ≤ r) (hrp : r < p) :
    coeff (m*p - r) ((A : PowerSeries R) * expand p (Fact.out : p.Prime).ne_zero f) =
      A.coeff (p - r) * coeff (m-1) f +
        (if 2 ≤ m then A.coeff (2*p - r) * coeff (m-2) f else 0) := by
  have hp0 := (Fact.out : p.Prime).pos
  have hmp : p ≤ m*p := Nat.le_mul_of_pos_left p hm
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [Polynomial.coeff_coe]
  have hzero : ∀ k ∈ Finset.range (m*p - r).succ, k ≠ p - r ∧ k ≠ 2*p - r →
      A.coeff k * coeff (m*p - r - k) (expand p (Fact.out : p.Prime).ne_zero f) = 0 := by
    intro k hk hne
    have hk' := Finset.mem_range_succ_iff.mp hk
    by_cases hkd : k ≤ 2*p
    · rw [coeff_expand_of_not_dvd, mul_zero]
      rintro ⟨t, ht⟩
      generalize hu : p*t = u at ht
      generalize hv : m*p = v at hk' hmp ht
      have := dvd_residue_cases (m := m) (t := t) hr1 hrp hkd (by omega)
      omega
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]
  have hfirst : m*p - r - (p - r) = p*(m-1) := by
    rw [Nat.mul_sub, mul_one, mul_comm p m]; omega
  by_cases hm2 : 2 ≤ m
  · have hsecond : m*p - r - (2*p - r) = p*(m-2) := by
      rw [Nat.mul_sub, mul_comm p m, mul_comm p 2]
      have : 2*p ≤ m*p := Nat.mul_le_mul_right p hm2
      omega
    rw [Finset.sum_eq_add_of_mem (p - r) (2*p - r)
      (Finset.mem_range_succ_iff.mpr (by omega))
      (Finset.mem_range_succ_iff.mpr (by
        have : 2*p ≤ m*p := Nat.mul_le_mul_right p hm2
        omega)) (by omega) hzero, if_pos hm2, hfirst, hsecond, coeff_expand_mul,
      coeff_expand_mul]
  · have hm1 : m = 1 := by omega
    subst hm1
    rw [if_neg hm2, add_zero, Finset.sum_eq_single_of_mem (p - r)
      (Finset.mem_range_succ_iff.mpr (by omega))
      (fun k hk hne => hzero k hk ⟨hne, by
        have := Finset.mem_range_succ_iff.mp hk
        omega⟩), hfirst, coeff_expand_mul]

/-! ### The short series `U`, `W` and the carry series `C1`, `C2` -/

/-- `U = D_t⁻¹(t P̄⁻¹F)` with zero constant, divisions only at `0 < m < p`. -/
def carryU (p : ℕ) [Fact p.Prime] : PowerSeries (ZMod p) :=
  mk fun m => if 0 < m ∧ m < p then coeff (m-1) (carryShort p) / (m : ZMod p) else 0

/-- `W = D_t⁻¹(t² P̄⁻¹F)` with zero constant, divisions only at `2 ≤ m < p`. -/
def carryW (p : ℕ) [Fact p.Prime] : PowerSeries (ZMod p) :=
  mk fun m => if 2 ≤ m ∧ m < p then coeff (m-2) (carryShort p) / (m : ZMod p) else 0

def carryCoeff (hp : 11 ≤ p) (j : ℕ) : ZMod p := (hasseCarryPolynomial p hp).coeff j

def carryC1 (p : ℕ) [Fact p.Prime] (hp : 11 ≤ p) : PowerSeries (ZMod p) :=
  -(C (carryCoeff hp (p-1)) * carryU p) - C (carryCoeff hp (2*p-1)) * carryW p

def carryC2 (p : ℕ) [Fact p.Prime] (hp : 11 ≤ p) : PowerSeries (ZMod p) :=
  C (2⁻¹ : ZMod p) * (C (carryCoeff hp (p-2)) * carryU p + C (carryCoeff hp (2*p-2)) * carryW p)

theorem carryU_coeff (m : ℕ) (hm : 0 < m) (hmp : m < p) :
    coeff m (carryU p) = coeff (m-1) (carryShort p) / (m : ZMod p) := by
  rw [carryU, coeff_mk, if_pos ⟨hm, hmp⟩]

theorem carryW_coeff (m : ℕ) (hm : 0 < m) (hmp : m < p) :
    coeff m (carryW p) =
      if 2 ≤ m then coeff (m-2) (carryShort p) / (m : ZMod p) else 0 := by
  rw [carryW, coeff_mk]
  by_cases h2 : 2 ≤ m
  · rw [if_pos ⟨h2, hmp⟩, if_pos h2]
  · rw [if_neg (fun h => h2 h.1), if_neg h2]

theorem carryU_coeff_zero : coeff 0 (carryU p) = 0 := by
  rw [carryU, coeff_mk, if_neg (fun h => lt_irrefl 0 h.1)]

theorem carryW_coeff_zero : coeff 0 (carryW p) = 0 := by
  rw [carryW, coeff_mk, if_neg (fun h => by omega)]

theorem carryU_coeff_ge (m : ℕ) (hm : p ≤ m) : coeff m (carryU p) = 0 := by
  rw [carryU, coeff_mk, if_neg (fun h => by omega)]

theorem carryW_coeff_ge (m : ℕ) (hm : p ≤ m) : coeff m (carryW p) = 0 := by
  rw [carryW, coeff_mk, if_neg (fun h => by omega)]

theorem carryC1_coeff_zero (hp : 11 ≤ p) : coeff 0 (carryC1 p hp) = 0 := by
  rw [carryC1, map_sub, map_neg, coeff_C_mul, coeff_C_mul, carryU_coeff_zero,
    carryW_coeff_zero]
  ring

theorem carryC2_coeff_zero (hp : 11 ≤ p) : coeff 0 (carryC2 p hp) = 0 := by
  rw [carryC2, coeff_C_mul, map_add, coeff_C_mul, coeff_C_mul, carryU_coeff_zero,
    carryW_coeff_zero]
  ring

theorem short_index_lt (N m : ℕ) (hN : N ≤ p^2) (hn : m*p < N) : m < p := by
  have hp0 := (Fact.out : p.Prime).pos
  by_contra h
  have : p*p ≤ m*p := Nat.mul_le_mul_right p (not_lt.mp h)
  rw [pow_two] at hN
  omega

theorem natCast_unit_of_short {m : ℕ} (hm : 0 < m) (hmp : m < p) : (m : ZMod p) ≠ 0 :=
  (ZMod.natCast_eq_zero_iff m p).not.mpr (Nat.not_dvd_of_pos_of_lt hm hmp)

theorem two_unit (hp : 11 ≤ p) : (2 : ZMod p) ≠ 0 := by
  exact_mod_cast natCast_unit_of_short (p := p) (m := 2) (by omega) (by omega)

theorem layer_short_bound {N m r : ℕ} (hN : N ≤ p^2) (hn : m*p + r < N) (hm : 0 < m) :
    m < p := short_index_lt N m hN (by omega)

/-- **Exceptional J1 carry** at `mp` via `U, W`. -/
theorem actualJ1_fourth_carry_UW (hp : 11 ≤ p) (c : ℚ) (hc : ¬p ∣ c.den)
    (N : ℕ) (hN : N ≤ p^2) (m : ℕ) (hm : 0 < m) (hn : m*p < N) :
    actualJ1Fourth c hc N hN (m*p) hn = coeff m (carryC1 p hp) := by
  have hmp := short_index_lt N m hN hn
  have hmZ := natCast_unit_of_short hm hmp
  rw [actualJ1_fourth_carry c hc N hN m hm hn, actualDKThird_carry hp,
    hasseCarrySeries, coeff_carry_extract _ (hasseCarryPolynomial_degree p hp) _ m 1 hm
      le_rfl (by omega)]
  simp only [carryC1, map_sub, map_neg, coeff_C_mul, carryU_coeff m hm hmp,
    carryW_coeff m hm hmp, carryCoeff]
  split_ifs <;> field_simp <;> ring

/-- **Exceptional J2 carry** at `mp` via `U, W`. -/
theorem actualJ2_fourth_carry_UW (hp : 11 ≤ p) (c : ℚ) (hc : ¬p ∣ c.den)
    (N : ℕ) (hN : N ≤ p^2) (m : ℕ) (hm : 0 < m) (hn : m*p < N) :
    actualJ2Fourth (by omega) c hc N hN (m*p) hn = coeff m (carryC2 p hp) := by
  have hmp := short_index_lt N m hN hn
  have hmZ := natCast_unit_of_short hm hmp
  have h2 := two_unit hp
  rw [actualJ2_fourth_carry (by omega) c hc N hN m hm hn, actualDKThird_carry hp,
    hasseCarrySeries, coeff_carry_extract _ (hasseCarryPolynomial_degree p hp) _ m 2 hm
      (by omega) (by omega)]
  simp only [carryC2, map_add, coeff_C_mul, carryU_coeff m hm hmp,
    carryW_coeff m hm hmp, carryCoeff]
  split_ifs <;> field_simp <;> ring

/-- **Exceptional J2 carry** at `mp+1` via `U, W`. -/
theorem actualJ2_fourth_carry_succ_UW (hp : 11 ≤ p) (c : ℚ) (hc : ¬p ∣ c.den)
    (N : ℕ) (hN : N ≤ p^2) (m : ℕ) (hm : 0 < m) (hn : m*p+1 < N) :
    actualJ2Fourth (by omega) c hc N hN (m*p+1) hn = coeff m (carryC1 p hp) := by
  have hmp := layer_short_bound hN hn hm
  have hmZ := natCast_unit_of_short hm hmp
  rw [actualJ2_fourth_carry_succ (by omega) c hc N hN m hm hn, actualDKThird_carry hp,
    hasseCarrySeries, coeff_carry_extract _ (hasseCarryPolynomial_degree p hp) _ m 1 hm
      le_rfl (by omega)]
  simp only [carryC1, map_sub, map_neg, coeff_C_mul, carryU_coeff m hm hmp,
    carryW_coeff m hm hmp, carryCoeff]
  split_ifs <;> field_simp <;> ring

end Zeta7Auxiliary

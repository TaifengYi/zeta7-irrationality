import Zeta7Proof.AuxiliaryCarryFormulas

/-! Completion of P3 for the actual germs: `K0 = U + 10 W`, the initial terms of `U, W`,
and the full fourth-layer congruences
`p⁴J1 ≡ X K0(X^p) + C1(X^p)` and `p⁴J2 ≡ X² K0(X^p)/2 + X C1(X^p) + C2(X^p)`
in every coefficient `n < N ≤ p^2`, for primes `p ≥ 11` with `p ∤ c.den`. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
namespace Zeta7Auxiliary
open PowerSeries Zeta7Main Zeta7Common

variable {p : ℕ} [Fact p.Prime]

/-! ### Low coefficients of substitutions -/

theorem coeff_zero_subst_of_constant {R : Type*} [CommRing R] (f g : PowerSeries R)
    (hg : constantCoeff g = 0) : coeff 0 (f.subst g) = coeff 0 f := by
  rw [coeff_subst_congr hg 0 (B := C (coeff 0 f)) (fun k hk => by
    obtain rfl : k = 0 := by omega
    rw [coeff_zero_C])]
  rw [subst_C, coeff_zero_eq_constantCoeff_apply]
  exact MvPowerSeries.constantCoeff_C _

theorem coeff_one_subst_of_constant {R : Type*} [CommRing R] (f g : PowerSeries R)
    (hg : constantCoeff g = 0) : coeff 1 (f.subst g) = coeff 1 f * coeff 1 g := by
  rw [coeff_subst' (HasSubst.of_constantCoeff_zero' hg), finsum_eq_single _ 1]
  · rw [pow_one, smul_eq_mul]
  · intro d hd
    rcases Nat.lt_or_gt_of_ne hd with h | h
    · obtain rfl : d = 0 := by omega
      simp
    · rw [coeff_pow_eq_zero_of_lt hg h, smul_zero]

theorem qSeries_linear : coeff 1 qSeries = 1 := by
  have h := congrArg (coeff 1) q_subst_x
  rw [coeff_one_subst_of_constant _ _ xSeries_constant, xSeries_linear, mul_one,
    coeff_X] at h
  simpa using h

theorem GSeries_coeff_one : coeff 1 GSeries = 1 := by
  rw [GSeries_coeff, Nat.divisors_one, Finset.filter_singleton, if_pos (by decide)]
  simp

theorem rationalH_zero_coeff_zero : coeff 0 (rationalH 0) = 0 := by
  rw [rationalH, map_zero, add_zero, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_one, coeff_zero_subst_of_constant _ _ qSeries_constant,
    coeff_zero_eq_constantCoeff_apply GSeries, GSeries_constant, mul_zero]

theorem rationalH_zero_coeff_one : coeff 1 (rationalH 0) = 1 := by
  rw [rationalH, map_zero, add_zero, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ, Finset.sum_range_one]
  simp only [Nat.sub_zero, Nat.sub_self]
  rw [coeff_one_subst_of_constant _ _ qSeries_constant, GSeries_coeff_one, qSeries_linear,
    coeff_zero_subst_of_constant _ _ qSeries_constant, coeff_zero_eq_constantCoeff_apply GSeries,
    GSeries_constant, coeff_zero_eq_constantCoeff_apply BSeries, BSeries_constant]
  ring

theorem layer_of_rat_value {N : ℕ} {F : PowerSeries ℚ} (h : Cap N 0 (F.map (algebraMap ℚ ℚ_[p])))
    (j : ℕ) (hj : j < N) (a : ℕ) (ha : coeff j F = a) :
    layerCoefficient h ⟨j, hj⟩ = (a : ZMod p) := by
  rw [layerCoefficient_eq_residue, ← integralResidue_nat (p := p) a]
  apply integralResidue_congr
  change (p : ℚ_[p])^0 * coeff j (F.map (algebraMap ℚ ℚ_[p])) = _
  rw [_root_.pow_zero, one_mul, coeff_map, ha, map_natCast]

theorem hasseShortSeries_coeff_zero : coeff 0 (hasseShortSeries p) = 0 := by
  rw [hasseShortSeries_coeff_lt 0 (Fact.out : p.Prime).pos,
    layer_of_rat_value _ 0 _ 0 (by rw [rationalH_zero_coeff_zero]; simp), Nat.cast_zero]

theorem hasseShortSeries_coeff_one : coeff 1 (hasseShortSeries p) = 1 := by
  rw [hasseShortSeries_coeff_lt 1 (Fact.out : p.Prime).one_lt,
    layer_of_rat_value _ 1 _ 1 (by rw [rationalH_zero_coeff_one]; simp), Nat.cast_one]

theorem reducedP_inv_constant : constantCoeff ((reducedP p)⁻¹) = 1 := by
  rw [constantCoeff_inv, reducedP_constant, inv_one]

theorem carryShort_coeff_zero : coeff 0 (carryShort p) = 0 := by
  rw [carryShort, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_one]
  simp [hasseShortSeries_coeff_zero]

theorem carryShort_coeff_one : coeff 1 (carryShort p) = 1 := by
  rw [carryShort, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ, Finset.sum_range_one]
  simp only [Nat.sub_zero, Nat.sub_self]
  rw [hasseShortSeries_coeff_one, hasseShortSeries_coeff_zero,
    coeff_zero_eq_constantCoeff_apply, reducedP_inv_constant]
  ring

/-- `U` begins `t²/2`. -/
theorem carryU_initial (hp : 11 ≤ p) :
    coeff 0 (carryU p) = 0 ∧ coeff 1 (carryU p) = 0 ∧ coeff 2 (carryU p) = 1/2 := by
  refine ⟨carryU_coeff_zero, ?_, ?_⟩
  · rw [carryU_coeff 1 (by omega) (by omega), Nat.sub_self, carryShort_coeff_zero, zero_div]
  · rw [carryU_coeff 2 (by omega) (by omega), show 2 - 1 = 1 from rfl, carryShort_coeff_one]
    norm_num

/-- `W` begins `t³/3`. -/
theorem carryW_initial (hp : 11 ≤ p) :
    coeff 0 (carryW p) = 0 ∧ coeff 1 (carryW p) = 0 ∧ coeff 2 (carryW p) = 0 ∧
      coeff 3 (carryW p) = 1/3 := by
  refine ⟨carryW_coeff_zero, ?_, ?_, ?_⟩
  · rw [carryW_coeff 1 (by omega) (by omega), if_neg (by omega)]
  · rw [carryW_coeff 2 (by omega) (by omega), if_pos le_rfl, Nat.sub_self,
      carryShort_coeff_zero, zero_div]
  · rw [carryW_coeff 3 (by omega) (by omega), if_pos (by omega),
      show 3 - 2 = 1 from rfl, carryShort_coeff_one]
    norm_num

/-! ### `K0 = U + 10 W` -/

theorem reducedR_mul_short (m : ℕ) :
    coeff m (reducedR p * hasseShortSeries p) =
      (if 1 ≤ m then coeff (m-1) (carryShort p) else 0) +
        10 * (if 2 ≤ m then coeff (m-2) (carryShort p) else 0) := by
  have h : reducedR p * hasseShortSeries p =
      X^1 * carryShort p + C 10 * (X^2 * carryShort p) := by
    rw [reducedR_eq, carryShort, show (C (10 : ZMod p) : PowerSeries (ZMod p)) = 10 from
      map_ofNat C 10]
    ring
  rw [h, map_add, coeff_C_mul, coeff_X_pow_mul', coeff_X_pow_mul']

theorem rationalK_zero_derivative_residue (m : ℕ) (hm : m < p) :
    (m : ZMod p) * layerCoefficient (rationalK_cap_zero (p := p) 0 zero_den_not_dvd) ⟨m, hm⟩ =
      coeff m (reducedR p * hasseShortSeries p) := by
  have hRH := (rationalForcing_cap_zero (p := p) p).mul
    (rationalH_cap_zero (p := p) 0 zero_den_not_dvd)
  rw [← map_mul] at hRH
  have hy : Integral (coeff m ((rationalForcing * rationalH 0).map (algebraMap ℚ ℚ_[p]))) := by
    simpa only [Nat.add_zero, _root_.pow_zero, one_mul] using hRH m hm
  rw [layerCoefficient_eq_residue]
  rw [integralResidue_nat_mul_eq _ hy m (by
    rw [_root_.pow_zero, one_mul, ← rationalH_quadratic_derivative, map_euler, euler_coeff])]
  have hlift : ((coeff m (integralR p * integralShortH p) : ℤ_[p]) : ℚ_[p]) =
      coeff m ((rationalForcing * rationalH 0).map (algebraMap ℚ ℚ_[p])) := by
    rw [show ((coeff m (integralR p * integralShortH p) : ℤ_[p]) : ℚ_[p]) =
      coeff m ((integralR p * integralShortH p).map (algebraMap ℤ_[p] ℚ_[p])) by
        rw [coeff_map]; rfl]
    rw [map_mul (PowerSeries.map (algebraMap ℤ_[p] ℚ_[p])), map_integralR,
      map_mul (PowerSeries.map (algebraMap ℚ ℚ_[p]))]
    exact (coeff_mul_congr _ m (fun k hk => rationalH_zero_coeff_eq_short k (by omega))).symm
  rw [integralResidue_eq_of_lift hy _ hlift, ← coeff_map, map_mul]
  change coeff m (reducedR p * reducedShortH p) = _
  exact coeff_mul_congr _ m (fun k hk => (hasseShortSeries_coeff_lt_reduced k (by omega)).symm)

/-- **P3: `K0 = U + 10 W`.** -/
theorem hasseShortK_eq_carry (hp : 11 ≤ p) :
    hasseShortK p (by omega) = carryU p + C 10 * carryW p := by
  ext m
  rw [map_add, coeff_C_mul]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [hasseShortK_coeff_zero, carryU_coeff_zero, carryW_coeff_zero]; ring
  by_cases hmp : m < p
  · have hmZ := natCast_unit_of_short hm hmp
    rw [hasseShortK_coeff_lt (by omega) m hmp, carryU_coeff m hm hmp, carryW_coeff m hm hmp]
    have h := rationalK_zero_derivative_residue m hmp
    rw [reducedR_mul_short, if_pos (show 1 ≤ m by omega)] at h
    apply mul_left_cancel₀ hmZ
    rw [h]
    split_ifs <;> field_simp <;> ring
  · rw [hasseShortK_coeff_ge (by omega) m (not_lt.mp hmp), carryU_coeff_ge m (not_lt.mp hmp),
      carryW_coeff_ge m (not_lt.mp hmp)]
    ring

/-! ### The full congruences for `J1` and `J2` -/

theorem coeff_X_mul_of_pos {R : Type*} [CommRing R] (f : PowerSeries R) {n : ℕ} (hn : 0 < n) :
    coeff n (X * f) = coeff (n-1) f := by
  rw [← pow_one (X : PowerSeries R), coeff_X_pow_mul', if_pos (show 1 ≤ n by omega)]

theorem natCast_eq_one_of_dvd_pred {n : ℕ} (hn : 0 < n) (h : p ∣ n - 1) : (n : ZMod p) = 1 := by
  have : n = (n-1) + 1 := by omega
  rw [this, Nat.cast_add, (ZMod.natCast_eq_zero_iff _ p).mpr h, Nat.cast_one, zero_add]

theorem natCast_eq_two_of_dvd {n : ℕ} (hn : 2 ≤ n) (h : p ∣ n - 2) : (n : ZMod p) = 2 := by
  have : n = (n-2) + 2 := by omega
  rw [this, Nat.cast_add, (ZMod.natCast_eq_zero_iff _ p).mpr h, zero_add]
  norm_num

theorem actualJ1Fourth_congr (c : ℚ) (hc : ¬p ∣ c.den) (N : ℕ) (hN : N ≤ p^2)
    {n n' : ℕ} (h : n = n') (hn : n < N) (hn' : n' < N) :
    actualJ1Fourth c hc N hN n hn = actualJ1Fourth c hc N hN n' hn' := by subst h; rfl

theorem actualJ2Fourth_congr (hp : 2 < p) (c : ℚ) (hc : ¬p ∣ c.den) (N : ℕ) (hN : N ≤ p^2)
    {n n' : ℕ} (h : n = n') (hn : n < N) (hn' : n' < N) :
    actualJ2Fourth hp c hc N hN n hn = actualJ2Fourth hp c hc N hN n' hn' := by subst h; rfl

theorem coeff_zero_expand {R : Type*} [CommRing R] (f : PowerSeries R) :
    coeff 0 (expand p (Fact.out : p.Prime).ne_zero f) = coeff 0 f := by
  simpa using coeff_expand_mul p (Fact.out : p.Prime).ne_zero f 0

theorem expand_coeff_pred_zero {R : Type*} [CommRing R] (f : PowerSeries R) {n k : ℕ}
    (hk : 0 < k) (hkp : k < p) (hkn : k ≤ n) (hn : p ∣ n) :
    coeff (n - k) (expand p (Fact.out : p.Prime).ne_zero f) = 0 :=
  coeff_expand_of_not_dvd _ _ _ (not_dvd_sub_of_dvd hk hkp hkn hn)

/-- **P3: `p⁴J1 ≡ X K0(X^p) + C1(X^p)`** coefficientwise below `N`. -/
theorem actualJ1_fourth_frobenius (hp : 11 ≤ p) (c : ℚ) (hc : ¬p ∣ c.den)
    (N : ℕ) (hN : N ≤ p^2) (n : ℕ) (hn : n < N) :
    actualJ1Fourth c hc N hN n hn =
      coeff n (X * expand p (Fact.out : p.Prime).ne_zero (hasseShortK p (by omega)) +
        expand p (Fact.out : p.Prime).ne_zero (carryC1 p hp)) := by
  have hp0 := (Fact.out : p.Prime).pos
  rw [map_add]
  by_cases hpn : p ∣ n
  · obtain ⟨m, rfl⟩ := hpn
    rw [coeff_expand_mul]
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · rw [(actual_primitive_fourth_initial (by omega) c hc N hN).1 _ (by simp) hn,
        mul_zero, coeff_zero_eq_constantCoeff_apply, map_mul, constantCoeff_X, zero_mul,
        carryC1_coeff_zero, add_zero]
    · rw [actualJ1Fourth_congr c hc N hN (mul_comm p m) hn (by rwa [mul_comm]),
        actualJ1_fourth_carry_UW hp c hc N hN m hm (by rwa [mul_comm]),
        coeff_X_mul_of_pos _ (by positivity),
        expand_coeff_pred_zero _ (by omega) (by omega) (by nlinarith) (dvd_mul_right p m),
        zero_add]
  · have hn0 : 0 < n := Nat.pos_of_ne_zero (fun h => hpn (h ▸ dvd_zero p))
    rw [coeff_expand_of_not_dvd _ _ _ hpn, add_zero, coeff_X_mul_of_pos _ hn0,
      actualJ1_fourth_regular c hc N hN n hn hpn,
      actualK_fourth_frobenius hp c hc N hN (n-1) (by omega)]
    by_cases hpm : p ∣ n - 1
    · rw [natCast_eq_one_of_dvd_pred hn0 hpm, div_one]
    · rw [coeff_expand_of_not_dvd _ _ _ hpm, zero_div]

/-- **P3: `p⁴J2 ≡ X² K0(X^p)/2 + X C1(X^p) + C2(X^p)`** coefficientwise below `N`. -/
theorem actualJ2_fourth_frobenius (hp : 11 ≤ p) (c : ℚ) (hc : ¬p ∣ c.den)
    (N : ℕ) (hN : N ≤ p^2) (n : ℕ) (hn : n < N) :
    actualJ2Fourth (by omega) c hc N hN n hn =
      coeff n (C (2⁻¹ : ZMod p) * (X^2 * expand p (Fact.out : p.Prime).ne_zero
          (hasseShortK p (by omega))) +
        X * expand p (Fact.out : p.Prime).ne_zero (carryC1 p hp) +
        expand p (Fact.out : p.Prime).ne_zero (carryC2 p hp)) := by
  have hp0 := (Fact.out : p.Prime).pos
  have hK0 := hasseShortK_coeff_zero (p := p) (by omega)
  rw [map_add, map_add, coeff_C_mul, coeff_X_pow_mul']
  by_cases hn3 : n < 3
  · rw [(actual_primitive_fourth_initial (by omega) c hc N hN).2 n hn3 hn]
    have h1 : ¬p ∣ 1 := Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
    have h2 : ¬p ∣ 2 := Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
    interval_cases n
    · rw [if_neg (by omega), coeff_zero_X_mul, coeff_zero_expand, carryC2_coeff_zero]
      ring
    · rw [if_neg (by omega), coeff_X_mul_of_pos _ (by omega), Nat.sub_self, coeff_zero_expand,
        carryC1_coeff_zero, coeff_expand_of_not_dvd _ _ _ h1]
      ring
    · rw [if_pos le_rfl, Nat.sub_self, coeff_zero_expand, hK0,
        coeff_X_mul_of_pos _ (by omega), show 2 - 1 = 1 from rfl,
        coeff_expand_of_not_dvd _ _ _ h1, coeff_expand_of_not_dvd _ _ _ h2]
      ring
  have hn3' : 3 ≤ n := by omega
  rw [if_pos (by omega), coeff_X_mul_of_pos _ (by omega)]
  by_cases hpn : p ∣ n
  · obtain ⟨m, rfl⟩ := hpn
    have hm : 0 < m := by
      rcases Nat.eq_zero_or_pos m with rfl | h
      · omega
      · exact h
    rw [actualJ2Fourth_congr (by omega) c hc N hN (mul_comm p m) hn (by rwa [mul_comm]),
      actualJ2_fourth_carry_UW hp c hc N hN m hm (by rwa [mul_comm]),
      expand_coeff_pred_zero _ (by omega) (by omega) (by omega) (dvd_mul_right p m),
      expand_coeff_pred_zero _ (by omega) (by omega) (by omega) (dvd_mul_right p m),
      coeff_expand_mul]
    ring
  by_cases hpm : p ∣ n - 1
  · obtain ⟨m, hm'⟩ := hpm
    have hm : 0 < m := by
      rcases Nat.eq_zero_or_pos m with rfl | h
      · omega
      · exact h
    have hnm : n = m*p + 1 := by rw [mul_comm]; omega
    rw [actualJ2Fourth_congr (by omega) c hc N hN hnm hn (by omega),
      actualJ2_fourth_carry_succ_UW hp c hc N hN m hm (by omega),
      hm', coeff_expand_mul, coeff_expand_of_not_dvd _ _ _ hpn,
      show n - 2 = n - 1 - 1 by omega, hm',
      expand_coeff_pred_zero _ (by omega) (by omega) (by nlinarith) (dvd_mul_right p m)]
    ring
  · rw [actualJ2_fourth_regular (by omega) c hc N hN n hn hpn hpm,
      actualK_fourth_frobenius hp c hc N hN (n-2) (by omega),
      coeff_expand_of_not_dvd _ _ _ hpn,
      coeff_expand_of_not_dvd _ _ _ hpm]
    by_cases hpl : p ∣ n - 2
    · rw [natCast_eq_two_of_dvd (by omega) hpl,
        natCast_eq_one_of_dvd_pred (by omega) (by rwa [show n - 1 - 1 = n - 2 by omega])]
      have h2 := two_unit hp
      field_simp
      ring
    · rw [coeff_expand_of_not_dvd _ _ _ hpl]
      ring

end Zeta7Auxiliary

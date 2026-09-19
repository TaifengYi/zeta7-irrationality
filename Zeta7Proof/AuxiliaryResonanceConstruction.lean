import Zeta7Proof.AuxiliaryResonanceBand

/-! P5: explicit construction of the positive and negative resonance numerators over `ℤ_[p]`,
by triangular recursion on the five-band coefficient formula with unit pivots, followed by the
constant correction at `x = -1/10`. All statements are exact identities over `ℤ_[p]`. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
namespace Zeta7Auxiliary
open PowerSeries Zeta7Common

variable {p : ℕ} [Fact p.Prime]

/-! ### Units of `ℤ_[p]` -/

theorem isUnit_of_toZMod_ne_zero (z : ℤ_[p]) (h : PadicInt.toZMod z ≠ 0) : IsUnit z := by
  by_contra hnu
  apply h
  have hm : z ∈ IsLocalRing.maximalIdeal ℤ_[p] := hnu
  rw [← PadicInt.ker_toZMod] at hm
  exact hm

theorem map_bandWeight {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (j : ℕ) (n : R) :
    φ (bandWeight j n) = bandWeight j (φ n) := by
  rcases j with _ | _ | _ | _ | _ | j <;> simp [bandWeight, map_ofNat]

theorem zmod_natCast_ne_zero {n : ℕ} (h : ¬p ∣ n) : (n : ZMod p) ≠ 0 :=
  (ZMod.natCast_eq_zero_iff n p).not.mpr h

theorem zmod_seven_ne_zero (hp : 11 ≤ p) : (7 : ZMod p) ≠ 0 := by
  have := zmod_natCast_ne_zero (p := p) (n := 7) (Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega))
  exact_mod_cast this

/-- The top pivot `2401 (m+2)³` is a unit for `m + 2 < p`. -/
theorem topPivot_isUnit (hp : 11 ≤ p) (m : ℕ) (hm : m + 2 < p) :
    IsUnit (bandWeight 4 (m : ℤ_[p])) := by
  apply isUnit_of_toZMod_ne_zero
  rw [map_bandWeight, map_natCast]
  simp only [bandWeight]
  have h7 := zmod_seven_ne_zero hp
  have hm2 : ((m : ZMod p) + 2) ≠ 0 := by
    have := zmod_natCast_ne_zero (p := p) (n := m + 2)
      (Nat.not_dvd_of_pos_of_lt (by omega) hm)
    exact_mod_cast this
  have h2401 : (2401 : ZMod p) = 7^4 := by norm_num
  rw [h2401]
  exact mul_ne_zero (pow_ne_zero _ h7) (pow_ne_zero _ hm2)

/-- The bottom pivot `(m - p)³` is a unit for `0 < m < p`. -/
theorem bottomPivot_isUnit (m : ℕ) (hm0 : 0 < m) (hm : m < p) :
    IsUnit (bandWeight 0 ((m : ℤ_[p]) - p)) := by
  apply isUnit_of_toZMod_ne_zero
  rw [map_bandWeight, map_sub, map_natCast, map_natCast, ZMod.natCast_self, sub_zero]
  simp only [bandWeight]
  exact pow_ne_zero _ (zmod_natCast_ne_zero (Nat.not_dvd_of_pos_of_lt hm0 hm))

/-! ### The positive resonance -/

def posCore (p : ℕ) [Fact p.Prime] (m : ℕ) : ℤ_[p] :=
  if hm : p - 2 < m then 0
  else if m = p - 2 then 1
  else if m = 0 then 0
  else -(bandWeight 0 ((m+4 : ℕ) : ℤ_[p]) * posCore p (m+4) +
        bandWeight 1 ((m+3 : ℕ) : ℤ_[p]) * posCore p (m+3) +
        bandWeight 2 ((m+2 : ℕ) : ℤ_[p]) * posCore p (m+2) +
        bandWeight 3 ((m+1 : ℕ) : ℤ_[p]) * posCore p (m+1)) *
      Ring.inverse (bandWeight 4 (m : ℤ_[p]))
termination_by p - m
decreasing_by all_goals omega

theorem posCore_gt (m : ℕ) (hm : p - 2 < m) : posCore p m = 0 := by
  rw [posCore, dif_pos hm]

theorem posCore_top : posCore p (p - 2) = 1 := by
  rw [posCore, dif_neg (by omega), if_pos rfl]

theorem posCore_zero (hp : 11 ≤ p) : posCore p 0 = 0 := by
  rw [posCore, dif_neg (by omega), if_neg (by omega), if_pos rfl]

theorem posCore_eq (hp : 11 ≤ p) (m : ℕ) (hm0 : 0 < m) (hm : m < p - 2) :
    bandWeight 0 ((m+4 : ℕ) : ℤ_[p]) * posCore p (m+4) +
      bandWeight 1 ((m+3 : ℕ) : ℤ_[p]) * posCore p (m+3) +
      bandWeight 2 ((m+2 : ℕ) : ℤ_[p]) * posCore p (m+2) +
      bandWeight 3 ((m+1 : ℕ) : ℤ_[p]) * posCore p (m+1) +
      bandWeight 4 (m : ℤ_[p]) * posCore p m = 0 := by
  have hu := topPivot_isUnit hp m (by omega)
  have hval : posCore p m = -(bandWeight 0 ((m+4 : ℕ) : ℤ_[p]) * posCore p (m+4) +
        bandWeight 1 ((m+3 : ℕ) : ℤ_[p]) * posCore p (m+3) +
        bandWeight 2 ((m+2 : ℕ) : ℤ_[p]) * posCore p (m+2) +
        bandWeight 3 ((m+1 : ℕ) : ℤ_[p]) * posCore p (m+1)) *
      Ring.inverse (bandWeight 4 (m : ℤ_[p])) := by
    rw [posCore, dif_neg (by omega), if_neg (by omega), if_neg (by omega)]
  rw [hval]
  have hinv := Ring.mul_inverse_cancel _ hu
  linear_combination (-(bandWeight 0 ((m+4 : ℕ) : ℤ_[p]) * posCore p (m+4) +
        bandWeight 1 ((m+3 : ℕ) : ℤ_[p]) * posCore p (m+3) +
        bandWeight 2 ((m+2 : ℕ) : ℤ_[p]) * posCore p (m+2) +
        bandWeight 3 ((m+1 : ℕ) : ℤ_[p]) * posCore p (m+1))) * hinv

/-- The positive numerator with constant coefficient `c₀`. -/
def posSeries (p : ℕ) [Fact p.Prime] (c0 : ℤ_[p]) : PowerSeries ℤ_[p] :=
  mk fun m => if m = 0 then c0 else posCore p m

theorem coeff_posSeries (c0 : ℤ_[p]) (m : ℕ) :
    coeff m (posSeries p c0) = if m = 0 then c0 else posCore p m := by
  rw [posSeries, coeff_mk]

theorem bandWeight_zero_zero {R : Type*} [CommRing R] : bandWeight 0 (0 : R) = 0 := by
  simp [bandWeight]

theorem sum_range_five {R : Type*} [AddCommMonoid R] (F : ℕ → R) :
    ∑ j ∈ Finset.range 5, F j = F 0 + F 1 + F 2 + F 3 + F 4 := by
  simp [Finset.sum_range_succ]

/-- The positive band vanishes in the middle range `5 ≤ k ≤ p + 1`. -/
theorem posBand_middle (hp : 11 ≤ p) (c0 : ℤ_[p]) (k : ℕ) (hk5 : 5 ≤ k) (hk : k ≤ p + 1) :
    coeff k (bandSeries 0 (posSeries p c0)) = 0 := by
  rw [coeff_bandSeries, sum_range_five]
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 4 := ⟨k - 4, by omega⟩
  simp only [if_pos (show (0:ℕ) ≤ m + 4 by omega), if_pos (show 1 ≤ m + 4 by omega),
    if_pos (show 2 ≤ m + 4 by omega), if_pos (show 3 ≤ m + 4 by omega),
    if_pos (show 4 ≤ m + 4 by omega), sub_zero, coeff_posSeries,
    if_neg (show m + 4 ≠ 0 by omega), if_neg (show m + 3 ≠ 0 by omega),
    if_neg (show m + 2 ≠ 0 by omega), if_neg (show m + 1 ≠ 0 by omega),
    if_neg (show m ≠ 0 by omega),
    show m + 4 - 0 = m + 4 by omega, show m + 4 - 1 = m + 3 by omega,
    show m + 4 - 2 = m + 2 by omega, show m + 4 - 3 = m + 1 by omega,
    show m + 4 - 4 = m by omega]
  exact posCore_eq hp m (by omega) (by omega)

theorem posBand_top (hp : 11 ≤ p) (c0 : ℤ_[p]) :
    coeff (p + 2) (bandSeries 0 (posSeries p c0)) = 2401 * (p : ℤ_[p])^3 := by
  rw [coeff_bandSeries, sum_range_five]
  simp only [if_pos (show (0:ℕ) ≤ p + 2 by omega), if_pos (show 1 ≤ p + 2 by omega),
    if_pos (show 2 ≤ p + 2 by omega), if_pos (show 3 ≤ p + 2 by omega),
    if_pos (show 4 ≤ p + 2 by omega), sub_zero, coeff_posSeries,
    if_neg (show p + 2 - 0 ≠ 0 by omega), if_neg (show p + 2 - 1 ≠ 0 by omega),
    if_neg (show p + 2 - 2 ≠ 0 by omega), if_neg (show p + 2 - 3 ≠ 0 by omega),
    show p + 2 - 0 = p + 2 by omega, show p + 2 - 1 = p + 1 by omega,
    show p + 2 - 2 = p by omega, show p + 2 - 3 = p - 1 by omega,
    show p + 2 - 4 = p - 2 by omega]
  rw [posCore_gt (p := p) (p + 2) (by omega), posCore_gt (p := p) (p + 1) (by omega),
    posCore_gt (p := p) p (by omega), posCore_gt (p := p) (p - 1) (by omega),
    if_neg (show p - 2 ≠ 0 by omega), posCore_top]
  simp only [if_neg (show p ≠ 0 by omega), if_neg (show p - 1 ≠ 0 by omega), mul_zero, zero_mul,
    add_zero, zero_add, mul_one, bandWeight]
  rw [Nat.cast_sub (by omega : 2 ≤ p)]
  push_cast
  ring

theorem posBand_high (c0 : ℤ_[p]) (k : ℕ) (hk : p + 2 < k) :
    coeff k (bandSeries 0 (posSeries p c0)) = 0 := by
  rw [coeff_bandSeries]
  refine Finset.sum_eq_zero fun j hj => ?_
  have hj5 := Finset.mem_range.mp hj
  have hp2 := (Fact.out : p.Prime).two_le
  split_ifs
  · rw [coeff_posSeries, if_neg (show k - j ≠ 0 by omega),
      posCore_gt (p := p) (k - j) (by omega), mul_zero]
  · rfl

theorem bandSeries_add {R : Type*} [CommRing R] (s : R) (f g : PowerSeries R) :
    bandSeries s (f + g) = bandSeries s f + bandSeries s g := by
  simp only [bandSeries, thetaS_add]
  ring

theorem thetaS_C_mul {R : Type*} [CommRing R] (s c : R) (f : PowerSeries R) :
    thetaS s (C c * f) = C c * thetaS s f := by
  rw [thetaS_mul, euler_C_gen, zero_mul, zero_add]

theorem bandSeries_C_mul {R : Type*} [CommRing R] (s c : R) (f : PowerSeries R) :
    bandSeries s (C c * f) = C c * bandSeries s f := by
  simp only [bandSeries, thetaS_C_mul]
  ring

theorem bandSeries_zero_C {R : Type*} [CommRing R] (c : R) :
    bandSeries 0 (C c) = C c * bandB0 := by
  have h := bandSeries_C_mul (0 : R) c 1
  rw [mul_one] at h
  rw [h]
  have h0 : thetaS (0 : R) 0 = 0 := by simp [thetaS, euler]
  have h1 : thetaS (0 : R) 1 = 0 := by rw [thetaS, euler_one_gen, map_zero, zero_mul, sub_zero]
  simp only [bandSeries, h1, h0]
  ring

theorem posSeries_split (c0 : ℤ_[p]) : posSeries p c0 = posSeries p 0 + C c0 := by
  ext m
  rw [map_add, coeff_posSeries, coeff_posSeries, coeff_C]
  split_ifs <;> simp_all

/-- The explicit constant-term weights of `band(1)`. -/
def bandOneLow (R : Type*) [CommRing R] : Polynomial R :=
  Polynomial.C 9 + Polynomial.C 433 * Polynomial.X + Polynomial.C 5145 * Polynomial.X^2 +
    Polynomial.C 19208 * Polynomial.X^3

theorem isUnit_ten (hp : 11 ≤ p) : IsUnit (10 : ℤ_[p]) := by
  apply isUnit_of_toZMod_ne_zero
  rw [map_ofNat]
  have := zmod_natCast_ne_zero (p := p) (n := 10) (by
    intro h
    have h2 := (Nat.Prime.dvd_mul (Fact.out : p.Prime)).mp (show p ∣ 2 * 5 from h)
    rcases h2 with h2 | h2
    · exact absurd (Nat.le_of_dvd (by norm_num) h2) (by omega)
    · exact absurd (Nat.le_of_dvd (by norm_num) h2) (by omega))
  exact_mod_cast this

/-- The point `-1/10`. -/
def tenthPt (p : ℕ) [Fact p.Prime] : ℤ_[p] := -Ring.inverse (10 : ℤ_[p])

theorem ten_mul_tenthPt (hp : 11 ≤ p) : (10 : ℤ_[p]) * tenthPt p = -1 := by
  rw [tenthPt, mul_neg, Ring.mul_inverse_cancel _ (isUnit_ten hp)]

theorem bandOneLow_unit (hp : 11 ≤ p) : IsUnit ((bandOneLow ℤ_[p]).eval (tenthPt p)) := by
  have h1000 : (1000 : ℤ_[p]) * (bandOneLow ℤ_[p]).eval (tenthPt p) = -2058 := by
    have ht := ten_mul_tenthPt (p := p) hp
    simp only [bandOneLow, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C]
    linear_combination (1920800 * tenthPt p ^ 2 + 322420 * tenthPt p + 11058) * ht
  have hu : IsUnit (-2058 : ℤ_[p]) := by
    apply isUnit_of_toZMod_ne_zero
    rw [map_neg, map_ofNat, neg_ne_zero]
    have := zmod_natCast_ne_zero (p := p) (n := 2058) (by
      intro h
      have hf : 2058 = 2 * 3 * 7 * 7 * 7 := by norm_num
      rw [hf] at h
      have hp' := (Fact.out : p.Prime)
      rcases hp'.dvd_mul.mp h with h | h
      · rcases hp'.dvd_mul.mp h with h | h
        · rcases hp'.dvd_mul.mp h with h | h
          · rcases hp'.dvd_mul.mp h with h | h
            · exact absurd (Nat.le_of_dvd (by norm_num) h) (by omega)
            · exact absurd (Nat.le_of_dvd (by norm_num) h) (by omega)
          · exact absurd (Nat.le_of_dvd (by norm_num) h) (by omega)
        · exact absurd (Nat.le_of_dvd (by norm_num) h) (by omega)
      · exact absurd (Nat.le_of_dvd (by norm_num) h) (by omega))
    exact_mod_cast this
  rw [← h1000] at hu
  exact isUnit_of_mul_isUnit_right hu

/-- The low band coefficients of the uncorrected positive numerator. -/
def posLowRest (p : ℕ) [Fact p.Prime] : Polynomial ℤ_[p] :=
  Polynomial.C (coeff 1 (bandSeries 0 (posSeries p 0))) +
    Polynomial.C (coeff 2 (bandSeries 0 (posSeries p 0))) * Polynomial.X +
    Polynomial.C (coeff 3 (bandSeries 0 (posSeries p 0))) * Polynomial.X^2 +
    Polynomial.C (coeff 4 (bandSeries 0 (posSeries p 0))) * Polynomial.X^3

/-- The constant correction of the positive resonance. -/
def posConst (p : ℕ) [Fact p.Prime] : ℤ_[p] :=
  -((posLowRest p).eval (tenthPt p)) * Ring.inverse ((bandOneLow ℤ_[p]).eval (tenthPt p))

/-- The corrected low polynomial, vanishing at `-1/10`. -/
def posLow (p : ℕ) [Fact p.Prime] : Polynomial ℤ_[p] :=
  posLowRest p + Polynomial.C (posConst p) * bandOneLow ℤ_[p]

theorem posLow_root (hp : 11 ≤ p) : (posLow p).eval (tenthPt p) = 0 := by
  have hu := Ring.inverse_mul_cancel _ (bandOneLow_unit (p := p) hp)
  simp only [posLow, posConst, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
  linear_combination -((posLowRest p).eval (tenthPt p)) * hu

/-- The positive forcing polynomial `h⁺`. -/
def posH (p : ℕ) [Fact p.Prime] : Polynomial ℤ_[p] :=
  Polynomial.C (Ring.inverse (10 : ℤ_[p])) *
    (posLow p /ₘ (Polynomial.X - Polynomial.C (tenthPt p)))

theorem one_add_ten_mul_inv (hp : 11 ≤ p) :
    ((1 + 10 * Polynomial.X) * Polynomial.C (Ring.inverse (10 : ℤ_[p])) : Polynomial ℤ_[p]) =
      Polynomial.X - Polynomial.C (tenthPt p) := by
  have h := Ring.mul_inverse_cancel _ (isUnit_ten (p := p) hp)
  have hC : (10 : Polynomial ℤ_[p]) * Polynomial.C (Ring.inverse (10 : ℤ_[p])) = 1 := by
    rw [show (10 : Polynomial ℤ_[p]) = Polynomial.C 10 from (map_ofNat Polynomial.C 10).symm,
      ← map_mul, h, map_one]
  rw [tenthPt, map_neg, sub_neg_eq_add]
  linear_combination Polynomial.X * hC

theorem posLow_factor (hp : 11 ≤ p) : posLow p = (1 + 10 * Polynomial.X) * posH p := by
  have hroot := (Polynomial.mul_divByMonic_eq_iff_isRoot (p := posLow p) (a := tenthPt p)).mpr
    (posLow_root hp)
  rw [posH, ← mul_assoc, one_add_ten_mul_inv hp, hroot]

theorem posLow_natDegree : (posLow p).natDegree ≤ 3 := by
  unfold posLow posLowRest bandOneLow
  compute_degree

theorem posH_natDegree : (posH p).natDegree ≤ 2 := by
  unfold posH
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  rw [Polynomial.natDegree_divByMonic _ (Polynomial.monic_X_sub_C _),
    Polynomial.natDegree_X_sub_C]
  have := posLow_natDegree (p := p)
  omega

/-- The positive resonance numerator `a⁺`. -/
def posA (p : ℕ) [Fact p.Prime] : PowerSeries ℤ_[p] := posSeries p (posConst p)

theorem coeff_posA_top (hp : 11 ≤ p) : coeff (p - 2) (posA p) = 1 := by
  rw [posA, coeff_posSeries, if_neg (by omega), posCore_top]

theorem coeff_posA_high (m : ℕ) (hm : p - 2 < m) : coeff m (posA p) = 0 := by
  rw [posA, coeff_posSeries, if_neg (by omega), posCore_gt m hm]

theorem coeff_posA_zero : coeff 0 (posA p) = posConst p := by
  rw [posA, coeff_posSeries, if_pos rfl]

theorem coeff_X_mul_gen {R : Type*} [CommRing R] (g : PowerSeries R) (k : ℕ) :
    coeff k (X * g) = if k = 0 then 0 else coeff (k - 1) g := by
  rcases k with _ | k
  · simp
  · simp [coeff_succ_X_mul]

theorem coeff_band_zero_index {R : Type*} [CommRing R] (f : PowerSeries R) :
    coeff 0 (bandSeries 0 f) = 0 := by
  rw [coeff_bandSeries, sum_range_five]
  simp [bandWeight]

theorem posLow_coeff (n : ℕ) (hn : n < 4) :
    (posLow p).coeff n = coeff (n + 1) (bandSeries 0 (posSeries p 0)) +
      posConst p * coeff (n + 1) (bandB0 : PowerSeries ℤ_[p]) := by
  have hB := bandB_expand (R := ℤ_[p]) 0 (by norm_num)
  simp only at hB
  rw [hB, map_sum]
  simp only [coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_range]
  interval_cases n <;>
    simp [posLow, posLowRest, bandOneLow, bandTable, Polynomial.coeff_X_pow, Polynomial.coeff_X,
      Polynomial.coeff_C] <;> ring

/-- **Positive resonance, exact form over `ℤ_[p]`:**
`band(a⁺) = X (1 + 10X) h⁺ + 2401 p³ X^{p+2}`. -/
theorem posA_band (hp : 11 ≤ p) :
    bandSeries 0 (posA p) =
      X * ((1 + 10 * X) * (posH p : PowerSeries ℤ_[p])) +
        C (2401 * (p : ℤ_[p])^3) * X^(p + 2) := by
  have hfac : ((1 + 10 * X) * (posH p : PowerSeries ℤ_[p])) = (posLow p : PowerSeries ℤ_[p]) := by
    rw [posLow_factor hp]
    simp
  rw [hfac]
  ext k
  rw [map_add, coeff_X_mul_gen, coeff_C_mul, coeff_X_pow, Polynomial.coeff_coe]
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rw [coeff_band_zero_index]
    simp
  by_cases hk4 : k ≤ 4
  · rw [if_neg (by omega), if_neg (by omega), mul_zero, add_zero, posA, posSeries_split,
      bandSeries_add, map_add, bandSeries_zero_C, coeff_C_mul]
    obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
    rw [show n + 1 - 1 = n by omega, posLow_coeff n (by omega)]
  · rw [if_neg (by omega), Polynomial.coeff_eq_zero_of_natDegree_lt
      (lt_of_le_of_lt posLow_natDegree (by omega)), zero_add]
    rcases Nat.lt_or_ge k (p + 2) with hlt | hge
    · rw [if_neg (by omega), mul_zero, posA]
      exact posBand_middle hp _ k (by omega) (by omega)
    · rcases Nat.eq_or_lt_of_le hge with heq | hgt
      · subst heq
        rw [if_pos rfl, mul_one, posA, posBand_top hp]
      · rw [if_neg (by omega), mul_zero, posA]
        exact posBand_high _ k hgt

end Zeta7Auxiliary

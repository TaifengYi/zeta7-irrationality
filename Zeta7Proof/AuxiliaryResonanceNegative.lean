import Zeta7Proof.AuxiliaryResonanceConstruction

/-! P5: the negative resonance numerator. In the coordinate `ã = x^p a⁻`, the Laurent
exponent of index `m` is `m - p`; the band is `bandSeries p`. The recursion ascends through
`1 ≤ m ≤ p - 1` with the unit bottom pivots `(m - p)³`; the constant correction is applied at
index `p`. The degree-`p` band coefficient `negCP` is identified with `p³ e_p` in the
skew-adjointness module. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
namespace Zeta7Auxiliary
open PowerSeries Zeta7Common

variable {p : ℕ} [Fact p.Prime]

def negCore (p : ℕ) [Fact p.Prime] (m : ℕ) : ℤ_[p] :=
  if m = 0 then 1
  else if p ≤ m then 0
  else -((if h1 : 1 ≤ m then bandWeight 1 (((m - 1 : ℕ) : ℤ_[p]) - p) * negCore p (m - 1) else 0) +
      (if h2 : 2 ≤ m then bandWeight 2 (((m - 2 : ℕ) : ℤ_[p]) - p) * negCore p (m - 2) else 0) +
      (if h3 : 3 ≤ m then bandWeight 3 (((m - 3 : ℕ) : ℤ_[p]) - p) * negCore p (m - 3) else 0) +
      (if h4 : 4 ≤ m then bandWeight 4 (((m - 4 : ℕ) : ℤ_[p]) - p) * negCore p (m - 4) else 0)) *
    Ring.inverse (bandWeight 0 ((m : ℤ_[p]) - p))
termination_by m
decreasing_by all_goals omega

theorem negCore_zero : negCore p 0 = 1 := by
  rw [negCore, if_pos rfl]

theorem negCore_ge (m : ℕ) (hm : p ≤ m) : negCore p m = 0 := by
  have := (Fact.out : p.Prime).pos
  rw [negCore, if_neg (by omega), if_pos hm]

theorem negCore_eq (m : ℕ) (hm0 : 0 < m) (hm : m < p) :
    bandWeight 0 (((m : ℕ) : ℤ_[p]) - p) * negCore p m +
      (if 1 ≤ m then bandWeight 1 (((m - 1 : ℕ) : ℤ_[p]) - p) * negCore p (m - 1) else 0) +
      (if 2 ≤ m then bandWeight 2 (((m - 2 : ℕ) : ℤ_[p]) - p) * negCore p (m - 2) else 0) +
      (if 3 ≤ m then bandWeight 3 (((m - 3 : ℕ) : ℤ_[p]) - p) * negCore p (m - 3) else 0) +
      (if 4 ≤ m then bandWeight 4 (((m - 4 : ℕ) : ℤ_[p]) - p) * negCore p (m - 4) else 0) = 0 := by
  have hu := bottomPivot_isUnit (p := p) m hm0 hm
  have hval : negCore p m =
      -((if 1 ≤ m then bandWeight 1 (((m - 1 : ℕ) : ℤ_[p]) - p) * negCore p (m - 1) else 0) +
        (if 2 ≤ m then bandWeight 2 (((m - 2 : ℕ) : ℤ_[p]) - p) * negCore p (m - 2) else 0) +
        (if 3 ≤ m then bandWeight 3 (((m - 3 : ℕ) : ℤ_[p]) - p) * negCore p (m - 3) else 0) +
        (if 4 ≤ m then bandWeight 4 (((m - 4 : ℕ) : ℤ_[p]) - p) * negCore p (m - 4) else 0)) *
      Ring.inverse (bandWeight 0 ((m : ℤ_[p]) - p)) := by
    rw [negCore, if_neg (by omega), if_neg (by omega)]
    simp only [dite_eq_ite]
  rw [hval]
  have hinv := Ring.inverse_mul_cancel _ hu
  linear_combination
    (-((if 1 ≤ m then bandWeight 1 (((m - 1 : ℕ) : ℤ_[p]) - p) * negCore p (m - 1) else 0) +
      (if 2 ≤ m then bandWeight 2 (((m - 2 : ℕ) : ℤ_[p]) - p) * negCore p (m - 2) else 0) +
      (if 3 ≤ m then bandWeight 3 (((m - 3 : ℕ) : ℤ_[p]) - p) * negCore p (m - 3) else 0) +
      (if 4 ≤ m then bandWeight 4 (((m - 4 : ℕ) : ℤ_[p]) - p) * negCore p (m - 4) else 0))) * hinv

/-- The shifted negative numerator with correction constant `c₁` at index `p`. -/
def negSeries (p : ℕ) [Fact p.Prime] (c1 : ℤ_[p]) : PowerSeries ℤ_[p] :=
  mk fun m => if m = p then c1 else negCore p m

theorem coeff_negSeries (c1 : ℤ_[p]) (m : ℕ) :
    coeff m (negSeries p c1) = if m = p then c1 else negCore p m := by
  rw [negSeries, coeff_mk]

theorem negBand_zero (c1 : ℤ_[p]) :
    coeff 0 (bandSeries (p : ℤ_[p]) (negSeries p c1)) = -(p : ℤ_[p])^3 := by
  have hp := (Fact.out : p.Prime).pos
  rw [coeff_bandSeries, sum_range_five]
  simp only [show ¬ (1 ≤ 0) by omega, show ¬ (2 ≤ 0) by omega, show ¬ (3 ≤ 0) by omega,
    show ¬ (4 ≤ 0) by omega, if_false, le_refl, if_true, add_zero, coeff_negSeries,
    if_neg (show 0 - 0 ≠ p by omega), Nat.sub_self, negCore_zero, mul_one, Nat.cast_zero, zero_sub]
  simp [bandWeight]
  ring

theorem negBand_middle (c1 : ℤ_[p]) (k : ℕ) (hk0 : 0 < k) (hk : k < p) :
    coeff k (bandSeries (p : ℤ_[p]) (negSeries p c1)) = 0 := by
  rw [coeff_bandSeries, sum_range_five]
  have h := negCore_eq (p := p) k hk0 hk
  have e : ∀ j, j ≤ 4 → coeff (k - j) (negSeries p c1) = negCore p (k - j) := fun j _ => by
    rw [coeff_negSeries, if_neg (by omega)]
  rw [e 0 (by omega), e 1 (by omega), e 2 (by omega), e 3 (by omega), e 4 (by omega),
    if_pos (Nat.zero_le k), Nat.sub_zero]
  linear_combination h

/-- The degree-`p` band coefficient, independent of the correction constant. -/
def negCP (p : ℕ) [Fact p.Prime] : ℤ_[p] :=
  bandWeight 1 (((p - 1 : ℕ) : ℤ_[p]) - p) * negCore p (p - 1) +
    bandWeight 2 (((p - 2 : ℕ) : ℤ_[p]) - p) * negCore p (p - 2) +
    bandWeight 3 (((p - 3 : ℕ) : ℤ_[p]) - p) * negCore p (p - 3) +
    bandWeight 4 (((p - 4 : ℕ) : ℤ_[p]) - p) * negCore p (p - 4)

theorem negBand_p (hp : 11 ≤ p) (c1 : ℤ_[p]) :
    coeff p (bandSeries (p : ℤ_[p]) (negSeries p c1)) = negCP p := by
  rw [coeff_bandSeries, sum_range_five]
  simp only [coeff_negSeries, if_pos (show (0:ℕ) ≤ p by omega), if_pos (show 1 ≤ p by omega),
    if_pos (show 2 ≤ p by omega), if_pos (show 3 ≤ p by omega), if_pos (show 4 ≤ p by omega),
    Nat.sub_zero, if_pos rfl, if_neg (show p - 1 ≠ p by omega), if_neg (show p - 2 ≠ p by omega),
    if_neg (show p - 3 ≠ p by omega), if_neg (show p - 4 ≠ p by omega), sub_self]
  rw [negCP, bandWeight_zero_zero, zero_mul, zero_add]

theorem negBand_high (c1 : ℤ_[p]) (k : ℕ) (hk : p + 4 < k) :
    coeff k (bandSeries (p : ℤ_[p]) (negSeries p c1)) = 0 := by
  rw [coeff_bandSeries]
  refine Finset.sum_eq_zero fun j hj => ?_
  have hj5 := Finset.mem_range.mp hj
  split_ifs
  · rw [coeff_negSeries, if_neg (show k - j ≠ p by omega), negCore_ge (p := p) (k - j) (by omega),
      mul_zero]
  · rfl

/-- Conjugation by `x^n` shifts the band. -/
theorem bandSeries_X_pow_mul {R : Type*} [CommRing R] (s : R) (n : ℕ) (g : PowerSeries R) :
    bandSeries (s + n) (X^n * g) = X^n * bandSeries s g := by
  have hθ : ∀ f : PowerSeries R, thetaS (s + n) (X^n * f) = X^n * thetaS s f := by
    intro f
    rw [thetaS_mul, euler_X_pow_gen, thetaS, thetaS,
      show (n : PowerSeries R) = C (n : R) from (map_natCast C n).symm, map_add]
    ring
  simp only [bandSeries, hθ]
  ring

theorem negSeries_split (c1 : ℤ_[p]) :
    negSeries p c1 = negSeries p 0 + C c1 * X^p := by
  ext m
  rw [map_add, coeff_negSeries, coeff_negSeries, coeff_C_mul, coeff_X_pow]
  split_ifs <;> simp_all [negCore_ge]

theorem bandSeries_p_const (c1 : ℤ_[p]) :
    bandSeries (p : ℤ_[p]) (C c1 * X^p) = C c1 * (X^p * bandB0) := by
  have h := bandSeries_X_pow_mul (0 : ℤ_[p]) p (C c1)
  rw [zero_add, bandSeries_zero_C] at h
  rw [mul_comm (C c1), h]
  ring

/-- The low band coefficients of the uncorrected negative numerator. -/
def negLowRest (p : ℕ) [Fact p.Prime] : Polynomial ℤ_[p] :=
  Polynomial.C (coeff (p + 1) (bandSeries (p : ℤ_[p]) (negSeries p 0))) +
    Polynomial.C (coeff (p + 2) (bandSeries (p : ℤ_[p]) (negSeries p 0))) * Polynomial.X +
    Polynomial.C (coeff (p + 3) (bandSeries (p : ℤ_[p]) (negSeries p 0))) * Polynomial.X^2 +
    Polynomial.C (coeff (p + 4) (bandSeries (p : ℤ_[p]) (negSeries p 0))) * Polynomial.X^3

def negConst (p : ℕ) [Fact p.Prime] : ℤ_[p] :=
  -((negLowRest p).eval (tenthPt p)) * Ring.inverse ((bandOneLow ℤ_[p]).eval (tenthPt p))

def negLow (p : ℕ) [Fact p.Prime] : Polynomial ℤ_[p] :=
  negLowRest p + Polynomial.C (negConst p) * bandOneLow ℤ_[p]

theorem negLow_root (hp : 11 ≤ p) : (negLow p).eval (tenthPt p) = 0 := by
  have hu := Ring.inverse_mul_cancel _ (bandOneLow_unit (p := p) hp)
  simp only [negLow, negConst, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
  linear_combination -((negLowRest p).eval (tenthPt p)) * hu

/-- The negative forcing polynomial `h⁻`. -/
def negH (p : ℕ) [Fact p.Prime] : Polynomial ℤ_[p] :=
  Polynomial.C (Ring.inverse (10 : ℤ_[p])) *
    (negLow p /ₘ (Polynomial.X - Polynomial.C (tenthPt p)))

theorem negLow_factor (hp : 11 ≤ p) : negLow p = (1 + 10 * Polynomial.X) * negH p := by
  have hroot := (Polynomial.mul_divByMonic_eq_iff_isRoot (p := negLow p) (a := tenthPt p)).mpr
    (negLow_root hp)
  rw [negH, ← mul_assoc, one_add_ten_mul_inv hp, hroot]

theorem negLow_natDegree : (negLow p).natDegree ≤ 3 := by
  unfold negLow negLowRest bandOneLow
  compute_degree

theorem negH_natDegree : (negH p).natDegree ≤ 2 := by
  unfold negH
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  rw [Polynomial.natDegree_divByMonic _ (Polynomial.monic_X_sub_C _),
    Polynomial.natDegree_X_sub_C]
  have := negLow_natDegree (p := p)
  omega

/-- The shifted negative resonance numerator `ã = x^p a⁻`. -/
def negA (p : ℕ) [Fact p.Prime] : PowerSeries ℤ_[p] := negSeries p (negConst p)

theorem coeff_negA_zero : coeff 0 (negA p) = 1 := by
  have := (Fact.out : p.Prime).pos
  rw [negA, coeff_negSeries, if_neg (by omega), negCore_zero]

theorem coeff_negA_high (m : ℕ) (hm : p < m) : coeff m (negA p) = 0 := by
  rw [negA, coeff_negSeries, if_neg (by omega), negCore_ge m hm.le]

theorem negLow_coeff (n : ℕ) (hn : n < 4) :
    (negLow p).coeff n = coeff (p + (n + 1)) (bandSeries (p : ℤ_[p]) (negSeries p 0)) +
      negConst p * coeff (n + 1) (bandB0 : PowerSeries ℤ_[p]) := by
  have hB := bandB_expand (R := ℤ_[p]) 0 (by norm_num)
  simp only at hB
  rw [hB, map_sum]
  simp only [coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_range]
  interval_cases n <;>
    simp [negLow, negLowRest, bandOneLow, bandTable, Polynomial.coeff_X_pow, Polynomial.coeff_X,
      Polynomial.coeff_C] <;> ring

/-- **Negative resonance, exact form over `ℤ_[p]`:**
`band_p(ã) = -p³ + c_p X^p + X^{p+1}(1 + 10X) h⁻`. -/
theorem negA_band (hp : 11 ≤ p) :
    bandSeries (p : ℤ_[p]) (negA p) =
      C (-(p : ℤ_[p])^3) + C (negCP p) * X^p +
        X^(p + 1) * ((1 + 10 * X) * (negH p : PowerSeries ℤ_[p])) := by
  have hfac : ((1 + 10 * X) * (negH p : PowerSeries ℤ_[p])) = (negLow p : PowerSeries ℤ_[p]) := by
    rw [negLow_factor hp]
    simp
  rw [hfac]
  ext k
  rw [map_add, map_add, coeff_C, coeff_C_mul, coeff_X_pow, coeff_X_pow_mul', Polynomial.coeff_coe]
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rw [negA, negBand_zero]
    simp [show p + 1 ≠ 0 by omega, show (0 : ℕ) ≠ p by
      have := (Fact.out : p.Prime).pos; omega]
  rw [if_neg (by omega)]
  rcases Nat.lt_or_ge k p with hkp | hkp
  · rw [negA, negBand_middle _ k hk0 hkp, if_neg (by omega), if_neg (by omega)]
    ring
  rcases Nat.eq_or_lt_of_le hkp with heq | hgt
  · subst heq
    rw [negA, negBand_p hp, if_pos rfl, if_neg (by omega)]
    ring
  by_cases hk4 : k ≤ p + 4
  · rw [if_neg (by omega), if_pos (by omega), negA, negSeries_split, bandSeries_add, map_add,
      bandSeries_p_const, coeff_C_mul, coeff_X_pow_mul', if_pos (by omega)]
    obtain ⟨n, rfl⟩ : ∃ n, k = p + (n + 1) := ⟨k - p - 1, by omega⟩
    rw [show p + (n + 1) - (p + 1) = n by omega, show p + (n + 1) - p = n + 1 by omega,
      negLow_coeff n (by omega)]
    ring
  · rw [if_neg (by omega), negA, negBand_high _ k (by omega)]
    split_ifs with h
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt negLow_natDegree (by omega))]
      ring
    · ring

end Zeta7Auxiliary

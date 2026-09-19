import Zeta7Proof.AuxiliaryResonanceOperator

/-! P5 modulo `p`: the reduced actual operator, homogeneity of `Γ·F(X^p)`, the homogeneous
Laurent polynomial `w₀ = Γ P(x^p)/x^p` in the shifted form `A₀ = Q̄² P̄^{p-2σ-1}`, and the
reductions of both resonance band identities. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
namespace Zeta7Auxiliary
open PowerSeries Zeta7Common

variable {p : ℕ} [Fact p.Prime]

local notation "σp" => (p - 1) / 3

abbrev zred (p : ℕ) [Fact p.Prime] : PowerSeries ℤ_[p] →+* PowerSeries (ZMod p) :=
  PowerSeries.map PadicInt.toZMod

/-- The reduced potential `V̄ = W / P²`. -/
def redV2 (p : ℕ) [Fact p.Prime] : PowerSeries (ZMod p) := bandW * ((bandP : PowerSeries (ZMod p))^2)⁻¹

theorem bandP_zmod : (bandP : PowerSeries (ZMod p)) = reducedP p := by
  rw [reducedP_value]; rfl

theorem bandP_zmod_const : constantCoeff (bandP : PowerSeries (ZMod p)) ≠ 0 := by
  simp [bandP]

theorem redV2_band : (bandP : PowerSeries (ZMod p))^2 * redV2 p = bandW := by
  have h : constantCoeff ((bandP : PowerSeries (ZMod p))^2) ≠ 0 := by
    rw [map_pow]; exact pow_ne_zero _ bandP_zmod_const
  rw [redV2, mul_comm, mul_assoc, PowerSeries.inv_mul_cancel _ h, mul_one]

theorem two_ne_zero_zmod (hp : 11 ≤ p) : (2 : ZMod p) ≠ 0 := two_unit hp

def halfZMod (p : ℕ) [Fact p.Prime] : ZMod p := (2 : ZMod p)⁻¹

theorem halfZMod_mul (hp : 11 ≤ p) : halfZMod p * 2 = 1 :=
  inv_mul_cancel₀ (two_ne_zero_zmod hp)

/-- The reduced operator `L̄`. -/
abbrev redL (p : ℕ) [Fact p.Prime] (f : PowerSeries (ZMod p)) : PowerSeries (ZMod p) :=
  resOp (halfZMod p) (redV2 p) 0 f

theorem resOp_zero_mul_const {R : Type*} [CommRing R] (half : R) (V G F : PowerSeries R)
    (hF : euler F = 0) : resOp half V 0 (G * F) = F * resOp half V 0 G := by
  simp only [resOp, thetaS_zero_eq, euler_mul_general, hF, euler_add_gen, mul_zero, add_zero]
  ring

theorem gamma_unit (hp : 5 ≤ p) : constantCoeff (hasseGammaSeries p hp) ≠ 0 := by
  rw [hasseGammaSeries_constant]; exact one_ne_zero

/-- **Homogeneity of `Γ`**, from the proved cleared Riccati identity. -/
theorem redL_gamma (hp : 11 ≤ p) : redL p (hasseGammaSeries p (by omega)) = 0 := by
  set G := hasseGammaSeries p (by omega) with hG
  have hR := hasseGammaSeries_clearedRiccati p (by omega)
  change clearedRiccati G = 0 at hR
  unfold clearedRiccati hasseP hasseW at hR
  have hPV := redV2_band (p := p)
  unfold bandP bandW at hPV
  have hP2 : IsUnit ((1 + 13 * X + 49 * X^2 : PowerSeries (ZMod p))^2) := by
    apply IsUnit.pow
    exact (bandP_isUnit (R := ZMod p))
  -- the uncleared Riccati identity
  have hR0 : 2 * G * euler (euler G) - (euler G)^2 - redV2 p * G^2 = 0 := by
    apply hP2.mul_left_cancel
    rw [mul_zero]
    linear_combination hR - G^2 * hPV
  have hD := congrArg euler hR0
  have e0 : euler (0 : PowerSeries (ZMod p)) = 0 := by simp [euler]
  rw [e0] at hD
  have h2e : euler (2 : PowerSeries (ZMod p)) = 0 := euler_ofNat_gen 2
  have hsub : ∀ a b : PowerSeries (ZMod p), euler (a - b) = euler a - euler b := fun a b => by
    simp [euler, mul_sub]
  simp only [hsub, euler_mul_general, h2e, pow_two, zero_mul, zero_add] at hD
  have hh : (C (halfZMod p) : PowerSeries (ZMod p)) * 2 = 1 := by
    rw [show (2 : PowerSeries (ZMod p)) = C 2 from (map_ofNat C 2).symm, ← map_mul,
      halfZMod_mul hp, map_one]
  have hGu : IsUnit (2 * G) := by
    apply PowerSeries.isUnit_iff_constantCoeff.mpr
    rw [map_mul, hasseGammaSeries_constant, mul_one]
    change IsUnit ((2 : ZMod p))
    exact (two_ne_zero_zmod hp).isUnit
  apply hGu.mul_left_cancel
  simp only [resOp, thetaS_zero_eq, mul_zero]
  linear_combination hD - (euler (redV2 p) * G^2) * hh

/-- `L̄(Γ · F(X^p)) = 0`. -/
theorem redL_gamma_frobenius (hp : 11 ≤ p) (F : PowerSeries (ZMod p)) :
    redL p (hasseGammaSeries p (by omega) * expand p (Fact.out : p.Prime).ne_zero F) = 0 := by
  unfold redL
  rw [resOp_zero_mul_const _ _ _ _ (euler_frobenius_zero p F)]
  have h := redL_gamma (p := p) hp
  unfold redL at h
  rw [h, mul_zero]

/-- The shifted homogeneous numerator `A₀ = Q̄² P̄^{p-2σ-1}`, so that `P̄ A₀ = Γ P̄^p`. -/
def homA0 (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) : Polynomial (ZMod p) :=
  (reducedQuotient p hp)^2 * (hassePolyP : Polynomial (ZMod p))^(p - 2 * ((p - 1) / 3) - 1)

theorem bandP_mul_homA0 (hp : 11 ≤ p) :
    (bandP : PowerSeries (ZMod p)) * (homA0 p (by omega) : PowerSeries (ZMod p)) =
      hasseGammaSeries p (by omega) *
        expand p (Fact.out : p.Prime).ne_zero (bandP : PowerSeries (ZMod p)) := by
  rw [← zmod_series_frobenius, hasseGammaSeries, homA0, bandP_zmod]
  simp only [Polynomial.coe_mul, Polynomial.coe_pow, hassePolyP_coe_reducedP]
  have hPinv := reducedP_mul_inv (p := p)
  have hpow : reducedP p ^ p = reducedP p ^ (p - 2 * σp - 1) * reducedP p ^ (2 * σp) * reducedP p := by
    rw [← pow_add, ← pow_succ]; congr 1; omega
  rw [hpow]
  calc (reducedP p) * (↑(reducedQuotient p (by omega))^2 * (reducedP p)^(p - 2 * σp - 1))
      = ↑(reducedQuotient p (by omega))^2 * (reducedP p)^(p - 2 * σp - 1) * reducedP p *
          ((reducedP p * (reducedP p)⁻¹)^(2 * σp)) := by rw [hPinv, one_pow]; ring
    _ = _ := by rw [mul_pow]; ring

/-- **Homogeneity of `A₀`:** `band(A₀) = 0` in characteristic `p`. -/
theorem band_homA0 (hp : 11 ≤ p) :
    bandSeries 0 (homA0 p (by omega) : PowerSeries (ZMod p)) = 0 := by
  rw [← band_identity (halfZMod p) (halfZMod_mul hp) (redV2 p) redV2_band 0, bandP_mul_homA0 hp]
  change bandP * redL p _ = 0
  rw [redL_gamma_frobenius hp, mul_zero]

/-! ### Reductions of the resonance identities -/

theorem zred_coe (f : Polynomial ℤ_[p]) :
    zred p (f : PowerSeries ℤ_[p]) = ((redZ p f : Polynomial (ZMod p)) : PowerSeries (ZMod p)) :=
  (Polynomial.polynomial_map_coe (φ := PadicInt.toZMod) (f := f)).symm

theorem toZMod_natCast_p : PadicInt.toZMod ((p : ℤ_[p])) = 0 := by
  rw [map_natCast, ZMod.natCast_self]

theorem zred_band (s : ℤ_[p]) (f : PowerSeries ℤ_[p]) :
    zred p (bandSeries s f) = bandSeries (PadicInt.toZMod s) (zred p f) :=
  map_bandSeries _ s f

/-- `band(ā⁺) = X (1 + 10X) h̄⁺` in characteristic `p`. -/
theorem redPos_band (hp : 11 ≤ p) :
    bandSeries 0 (zred p (posA p)) =
      X * ((1 + 10 * X) * ((redZ p (posH p) : Polynomial (ZMod p)) : PowerSeries (ZMod p))) := by
  have h := congrArg (zred p) (posA_band (p := p) hp)
  rw [zred_band, map_zero] at h
  rw [h]
  simp only [map_add, map_mul, map_pow, map_X, map_C, map_one, map_ofNat, zred_coe,
    toZMod_natCast_p]
  simp

/-- `band(ã⁻) = X^{p+1} (1 + 10X) h̄⁻` in characteristic `p`. -/
theorem redNeg_band (hp : 11 ≤ p) :
    bandSeries 0 (zred p (negA p)) =
      X^(p + 1) * ((1 + 10 * X) * ((redZ p (negH p) : Polynomial (ZMod p)) : PowerSeries (ZMod p))) := by
  have h := congrArg (zred p) (negA_band (p := p) hp)
  rw [zred_band, toZMod_natCast_p, negCP_eq hp] at h
  rw [h]
  simp only [map_add, map_mul, map_pow, map_X, map_C, map_one, map_ofNat, map_neg, zred_coe,
    toZMod_natCast_p]
  simp

theorem bandSeries_sub_gen {R : Type*} [CommRing R] (s : R) (f g : PowerSeries R) :
    bandSeries s (f - g) = bandSeries s f - bandSeries s g := by
  have h := bandSeries_add s (f - g) g
  rw [sub_add_cancel] at h
  rw [h]; ring

theorem bandSeries_C_mul_gen {R : Type*} [CommRing R] (s c : R) (f : PowerSeries R) :
    bandSeries s (C c * f) = C c * bandSeries s f := bandSeries_C_mul s c f

theorem zmod_band_X_pow (g : PowerSeries (ZMod p)) :
    bandSeries 0 (X^p * g) = X^p * bandSeries 0 g := by
  have h := bandSeries_X_pow_mul (0 : ZMod p) p g
  rwa [zero_add, ZMod.natCast_self] at h

/-! ### Coefficient facts -/

theorem coeff_redPos_top (hp : 11 ≤ p) : coeff (p - 2) (zred p (posA p)) = 1 := by
  rw [coeff_map, coeff_posA_top hp, map_one]

theorem coeff_redPos_high (m : ℕ) (hm : p - 2 < m) : coeff m (zred p (posA p)) = 0 := by
  rw [coeff_map, coeff_posA_high m hm, map_zero]

theorem coeff_redNeg_zero : coeff 0 (zred p (negA p)) = 1 := by
  rw [coeff_map, coeff_negA_zero, map_one]

theorem coeff_redNeg_high (m : ℕ) (hm : p < m) : coeff m (zred p (negA p)) = 0 := by
  rw [coeff_map, coeff_negA_high m hm, map_zero]

theorem reducedQuotient_ne_zero (hp : 5 ≤ p) : reducedQuotient p hp ≠ 0 := by
  intro h
  have := reducedQuotient_constant p hp
  rw [h, Polynomial.coeff_zero] at this
  exact zero_ne_one this

theorem hassePolyP_ne_zero_zmod : (hassePolyP : Polynomial (ZMod p)) ≠ 0 := by
  intro h
  have h0 := congrArg (fun f : Polynomial (ZMod p) => f.coeff 0) h
  simp [hassePolyP] at h0

theorem homA0_natDegree (hp : 11 ≤ p) : (homA0 p (by omega)).natDegree = 2 * p - 2 := by
  rw [homA0, Polynomial.natDegree_mul (pow_ne_zero _ (reducedQuotient_ne_zero _))
    (pow_ne_zero _ hassePolyP_ne_zero_zmod), Polynomial.natDegree_pow, Polynomial.natDegree_pow,
    reducedQuotient_degree p hp, hassePolyP_natDegree p hp]
  omega

theorem homA0_ne_zero (hp : 11 ≤ p) : homA0 p (by omega) ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ (reducedQuotient_ne_zero _)) (pow_ne_zero _ hassePolyP_ne_zero_zmod)

/-- The leading coefficient of `A₀`, a unit. -/
def homLead (p : ℕ) [Fact p.Prime] (hp : 11 ≤ p) : ZMod p := (homA0 p (by omega)).leadingCoeff

theorem homLead_ne_zero (hp : 11 ≤ p) : homLead p hp ≠ 0 :=
  Polynomial.leadingCoeff_ne_zero.mpr (homA0_ne_zero hp)

theorem homA0_coeff_zero (hp : 11 ≤ p) : (homA0 p (by omega)).coeff 0 = 1 := by
  rw [homA0, Polynomial.coeff_zero_eq_eval_zero]
  simp only [Polynomial.eval_mul, Polynomial.eval_pow]
  rw [← Polynomial.coeff_zero_eq_eval_zero, reducedQuotient_constant]
  simp [hassePolyP]

/-! ### The difference `ã⁻ - A₀` -/

/-- `δ = ã⁻ - A₀` (reduced). -/
def resDelta (p : ℕ) [Fact p.Prime] (hp : 11 ≤ p) : PowerSeries (ZMod p) :=
  zred p (negA p) - (homA0 p (by omega) : PowerSeries (ZMod p))

theorem resDelta_band (hp : 11 ≤ p) :
    bandSeries 0 (resDelta p hp) =
      X^(p + 1) * ((1 + 10 * X) * ((redZ p (negH p) : Polynomial (ZMod p)) : PowerSeries (ZMod p))) := by
  rw [resDelta, bandSeries_sub_gen, redNeg_band hp, band_homA0 hp, sub_zero]

theorem resDelta_low (hp : 11 ≤ p) : ∀ k, k < p → coeff k (resDelta p hp) = 0 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [resDelta, map_sub, coeff_redNeg_zero, Polynomial.coeff_coe, homA0_coeff_zero hp, sub_self]
    have hb := congrArg (coeff k) (resDelta_band (p := p) hp)
    rw [coeff_X_pow_mul', if_neg (by omega), coeff_bandSeries, sum_range_five] at hb
    have hz : ∀ j, 1 ≤ j → j ≤ k → coeff (k - j) (resDelta p hp) = 0 := fun j hj1 hjk =>
      ih (k - j) (by omega) (by omega)
    have e1 : (if 1 ≤ k then bandWeight 1 (((k - 1 : ℕ) : ZMod p) - 0) *
        coeff (k - 1) (resDelta p hp) else 0) = 0 := by
      split_ifs with h
      · rw [hz 1 le_rfl h, mul_zero]
      · rfl
    have e2 : (if 2 ≤ k then bandWeight 2 (((k - 2 : ℕ) : ZMod p) - 0) *
        coeff (k - 2) (resDelta p hp) else 0) = 0 := by
      split_ifs with h
      · rw [hz 2 (by norm_num) h, mul_zero]
      · rfl
    have e3 : (if 3 ≤ k then bandWeight 3 (((k - 3 : ℕ) : ZMod p) - 0) *
        coeff (k - 3) (resDelta p hp) else 0) = 0 := by
      split_ifs with h
      · rw [hz 3 (by norm_num) h, mul_zero]
      · rfl
    have e4 : (if 4 ≤ k then bandWeight 4 (((k - 4 : ℕ) : ZMod p) - 0) *
        coeff (k - 4) (resDelta p hp) else 0) = 0 := by
      split_ifs with h
      · rw [hz 4 (by norm_num) h, mul_zero]
      · rfl
    rw [e1, e2, e3, e4, if_pos (Nat.zero_le k), Nat.sub_zero, sub_zero, add_zero, add_zero,
      add_zero, add_zero] at hb
    simp only [bandWeight] at hb
    have hkZ : ((k : ℕ) : ZMod p)^3 ≠ 0 :=
      pow_ne_zero _ (zmod_natCast_ne_zero (Nat.not_dvd_of_pos_of_lt hk0 hk))
    exact (mul_eq_zero.mp hb).resolve_left hkZ

/-- The quotient `α = δ / X^p`. -/
def resAlpha (p : ℕ) [Fact p.Prime] (hp : 11 ≤ p) : PowerSeries (ZMod p) :=
  mk fun m => coeff (m + p) (resDelta p hp)

theorem resDelta_eq (hp : 11 ≤ p) : resDelta p hp = X^p * resAlpha p hp := by
  ext m
  rw [coeff_X_pow_mul']
  split_ifs with h
  · rw [resAlpha, coeff_mk, Nat.sub_add_cancel h]
  · exact resDelta_low hp m (by omega)

theorem resAlpha_high (hp : 11 ≤ p) (m : ℕ) (hm : p - 2 < m) : coeff m (resAlpha p hp) = 0 := by
  rw [resAlpha, coeff_mk, resDelta, map_sub, coeff_redNeg_high _ (by omega), Polynomial.coeff_coe,
    Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [homA0_natDegree hp]; omega), sub_zero]

theorem resAlpha_top (hp : 11 ≤ p) : coeff (p - 2) (resAlpha p hp) = -homLead p hp := by
  rw [resAlpha, coeff_mk, resDelta, map_sub, coeff_redNeg_high _ (by omega), Polynomial.coeff_coe,
    show p - 2 + p = (homA0 p (by omega)).natDegree by rw [homA0_natDegree hp]; omega,
    Polynomial.coeff_natDegree, zero_sub]
  rfl

theorem resAlpha_band (hp : 11 ≤ p) :
    bandSeries 0 (resAlpha p hp) =
      X * ((1 + 10 * X) * ((redZ p (negH p) : Polynomial (ZMod p)) : PowerSeries (ZMod p))) := by
  have h := resDelta_band (p := p) hp
  rw [resDelta_eq hp, zmod_band_X_pow, pow_succ, mul_assoc] at h
  exact mul_left_cancel₀ (pow_ne_zero _ X_ne_zero) h

end Zeta7Auxiliary

import Zeta7Proof.AuxiliaryResonanceNegative

/-! P5: the actual operator `L` in `ℚ_[p]`, the Lagrange (skew-adjointness) identity, the
constant-term vanishing `CT(B · L(P a⁻)) = 0` coming from the actual homogeneous solution `B`,
and the exact resonance relations
`L(P a⁺) = h⁺ R + p³ · (integral)` and `x^p L(x^{-p} P ã) = x^p h⁻ R + p³ · (integral)`. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
namespace Zeta7Auxiliary
open PowerSeries Zeta7Main Zeta7Common

variable {p : ℕ} [Fact p.Prime]

/-! ### Transport of the band operator along ring maps -/

theorem map_thetaS {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (s : R)
    (f : PowerSeries R) : (thetaS s f).map φ = thetaS (φ s) (f.map φ) := by
  simp [thetaS, map_euler, map_C]

theorem map_bandSeries {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (s : R)
    (f : PowerSeries R) : (bandSeries s f).map φ = bandSeries (φ s) (f.map φ) := by
  simp only [bandSeries, map_add, map_mul, map_thetaS]
  simp [bandB3, bandB2, bandB1, bandB0, map_ofNat]

/-! ### The actual operator in `ℚ_[p]` -/

abbrev padicV (p : ℕ) [Fact p.Prime] : PowerSeries ℚ_[p] := padicMap (p := p) rationalPotential

theorem bandP_padic : (bandP : PowerSeries ℚ_[p]) = padicMap (p := p) shortP := by
  rw [shortP_value]
  simp [bandP, map_ofNat]

theorem padicV_band : (bandP : PowerSeries ℚ_[p])^2 * padicV p = bandW := by
  have h := congrArg (padicMap (p := p)) rationalPotential_cleared
  simp only [map_mul, map_pow, map_add, map_ofNat, map_X] at h
  rw [bandP_padic, mul_comm]
  rw [h]
  simp [bandW, map_ofNat]

theorem half_padic : (1/2 : ℚ_[p]) * 2 = 1 := by norm_num

theorem modularL_padic (f : PowerSeries ℚ) :
    padicMap (p := p) (modularL f) = resOp (1/2 : ℚ_[p]) (padicV p) 0 (padicMap (p := p) f) := by
  have hθ : ∀ g : PowerSeries ℚ_[p], thetaS (0 : ℚ_[p]) g = euler g := fun g => by
    simp [thetaS]
  simp only [modularL, resOp, hθ, map_sub, map_mul, map_euler]
  rw [padicMap_half]

theorem padicB_homogeneous :
    resOp (1/2 : ℚ_[p]) (padicV p) 0 (padicMap (p := p) BSeries) = 0 := by
  rw [← modularL_padic, BSeries_homogeneous, map_zero]

/-! ### Lagrange identity -/

/-- The twisted concomitant `W_s(f, g)`. -/
def concomitant {R : Type*} [CommRing R] (V : PowerSeries R) (s : R) (f g : PowerSeries R) :
    PowerSeries R :=
  f * thetaS s (thetaS s g) - euler f * thetaS s g + euler (euler f) * g - V * f * g

theorem thetaS_zero_eq {R : Type*} [CommRing R] (g : PowerSeries R) : thetaS (0 : R) g = euler g := by
  simp [thetaS]

/-- **Lagrange identity**: `f L_s g + g L f = θ_s W_s(f,g)`. -/
theorem lagrange_identity {R : Type*} [CommRing R] (half : R) (hhalf : half * 2 = 1)
    (V : PowerSeries R) (s : R) (f g : PowerSeries R) :
    f * resOp half V s g + g * resOp half V 0 f = thetaS s (concomitant V s f g) := by
  have hh : (C half : PowerSeries R) * 2 = 1 := by
    rw [show (2 : PowerSeries R) = C 2 from (map_ofNat C 2).symm, ← map_mul, hhalf, map_one]
  have hs : ∀ a b : PowerSeries R, thetaS s (a - b) = thetaS s a - thetaS s b := fun a b => by
    simp only [thetaS, sub_eq_add_neg, euler_add_gen]
    have : euler (-b) = -euler b := by simp [euler]
    rw [this]; ring
  simp only [resOp, concomitant, thetaS_zero_eq, hs, thetaS_add, thetaS_mul, euler_mul_general]
  linear_combination (-(euler V * f * g)) * hh

/-- **Constant-term vanishing** from the actual homogeneous solution `B`. -/
theorem coeff_B_mul_resOp (g : PowerSeries ℚ_[p]) :
    coeff p (padicMap (p := p) BSeries * resOp (1/2 : ℚ_[p]) (padicV p) (p : ℚ_[p]) g) = 0 := by
  have h := lagrange_identity (1/2 : ℚ_[p]) half_padic (padicV p) (p : ℚ_[p])
    (padicMap (p := p) BSeries) g
  rw [padicB_homogeneous, mul_zero, add_zero] at h
  rw [h, coeff_thetaS, sub_self, zero_mul]

/-! ### The integral quantity `e_p` -/

/-- The integral inverse of `P`. -/
def intPinv (p : ℕ) [Fact p.Prime] : PowerSeries ℤ_[p] := PowerSeries.invOfUnit (integralP p) 1

theorem zpMap_intPinv : zpMap (p := p) (intPinv p) = (padicMap (p := p) shortP)⁻¹ := by
  rw [intPinv, ← map_invOfUnit (integralP p) 1 (by rw [integralP_constant, Units.val_one]),
    zpMap_integralP]

/-- `e_p = [x^p] (B / P)`. -/
def resonanceE (p : ℕ) [Fact p.Prime] : ℤ_[p] := coeff p (integralB p * intPinv p)

theorem coeff_zero_BPinv : coeff 0 (integralB p * intPinv p) = 1 := by
  rw [coeff_zero_eq_constantCoeff_apply, map_mul]
  have hB : constantCoeff (integralB p) = 1 := by
    apply Subtype.ext
    rw [← coeff_zero_eq_constantCoeff, integralB, integerSeriesLift, coeff_mk]
    change ((coeff 0 BSeries : ℚ) : ℚ_[p]) = 1
    rw [coeff_zero_eq_constantCoeff, BSeries_constant, Rat.cast_one]
  rw [hB, intPinv, constantCoeff_invOfUnit, one_mul, inv_one, Units.val_one]

theorem padicP_ne : constantCoeff (padicMap (p := p) shortP) ≠ 0 := padicShortP_const

theorem padicP_mul_inv :
    padicMap (p := p) shortP * (padicMap (p := p) shortP)⁻¹ = 1 :=
  PowerSeries.mul_inv_cancel _ padicP_ne

theorem resOp_band_inv (s : ℚ_[p]) (F : PowerSeries ℚ_[p]) :
    resOp (1/2 : ℚ_[p]) (padicV p) s (bandP * F) =
      (padicMap (p := p) shortP)⁻¹ * bandSeries s F := by
  rw [← band_identity (1/2 : ℚ_[p]) half_padic (padicV p) padicV_band s F, ← mul_assoc,
    bandP_padic, mul_comm _⁻¹, padicP_mul_inv, one_mul]

theorem coeff_mul_C_X_pow (E : PowerSeries ℤ_[p]) (a : ℤ_[p]) (n : ℕ) :
    coeff n (E * (C a * X^n)) = a * coeff 0 E := by
  rw [show E * (C a * X^n) = C a * (X^n * E) by ring, coeff_C_mul, coeff_X_pow_mul',
    if_pos le_rfl, Nat.sub_self]

theorem coeff_mul_X_pow_succ (E Y : PowerSeries ℤ_[p]) (n : ℕ) :
    coeff n (E * (X^(n + 1) * Y)) = 0 := by
  rw [show E * (X^(n + 1) * Y) = X^(n + 1) * (E * Y) by ring, coeff_X_pow_mul',
    if_neg (by omega)]

/-- **The degree-`p` band coefficient of the negative resonance is `p³ e_p`.** -/
theorem negCP_eq (hp : 11 ≤ p) : negCP p = (p : ℤ_[p])^3 * resonanceE p := by
  have hband := negA_band (p := p) hp
  have hmap := map_bandSeries (algebraMap ℤ_[p] ℚ_[p]) (p : ℤ_[p]) (negA p)
  rw [map_natCast] at hmap
  have h0 := coeff_B_mul_resOp (p := p) (bandP * zpMap (p := p) (negA p))
  rw [resOp_band_inv, ← hmap, ← mul_assoc, ← zpMap_intPinv, ← zpMap_integralB, ← map_mul,
    ← map_mul, coeff_map] at h0
  have h1 : coeff p (integralB p * intPinv p * bandSeries (p : ℤ_[p]) (negA p)) = 0 := by
    have hinj : Function.Injective (algebraMap ℤ_[p] ℚ_[p]) := Subtype.val_injective
    exact hinj (by rw [h0, map_zero])
  rw [hband, mul_add, mul_add, map_add, map_add, coeff_mul_C_X_pow, coeff_mul_X_pow_succ,
    coeff_zero_BPinv, mul_comm _ (C _), coeff_C_mul] at h1
  rw [resonanceE]
  linear_combination h1

theorem rationalForcing_padic :
    padicMap (p := p) rationalForcing =
      X * (1 + 10 * X) * (padicMap (p := p) shortP)⁻¹ := by
  rw [rationalForcing, map_mul, map_inv_padic _ (by simp), ← shortP_value]
  simp [map_ofNat]

/-- The integral positive residual `2401 X^{p+2} / P`. -/
def posResidual (p : ℕ) [Fact p.Prime] : PowerSeries ℤ_[p] :=
  C 2401 * X^(p + 2) * intPinv p

/-- The integral negative residual `(e_p X^p - 1) / P`. -/
def negResidual (p : ℕ) [Fact p.Prime] : PowerSeries ℤ_[p] :=
  (C (resonanceE p) * X^p - 1) * intPinv p

theorem zpMap_polynomial (f : Polynomial ℤ_[p]) :
    zpMap (p := p) (f : PowerSeries ℤ_[p]) = zpPoly p f := rfl

/-- **Positive resonance relation:** `L(P a⁺) = h⁺ R + p³ · posResidual`, exactly in `ℚ_[p]`. -/
theorem posA_relation (hp : 11 ≤ p) :
    resOp (1/2 : ℚ_[p]) (padicV p) 0 (bandP * zpMap (p := p) (posA p)) =
      zpPoly p (posH p) * padicMap (p := p) rationalForcing +
        (p : PowerSeries ℚ_[p])^3 * zpMap (p := p) (posResidual p) := by
  have hmap := map_bandSeries (algebraMap ℤ_[p] ℚ_[p]) (0 : ℤ_[p]) (posA p)
  rw [map_zero] at hmap
  rw [resOp_band_inv, ← hmap, posA_band hp, rationalForcing_padic, posResidual, ← zpMap_intPinv]
  simp only [map_add, map_mul, map_pow, map_X, map_C, map_ofNat, zpMap_polynomial]
  simp only [map_one, map_ofNat, map_natCast]
  ring

/-- **Negative resonance relation:** `L_p(P ã) = X^p h⁻ R + p³ · negResidual`, exactly. -/
theorem negA_relation (hp : 11 ≤ p) :
    resOp (1/2 : ℚ_[p]) (padicV p) (p : ℚ_[p]) (bandP * zpMap (p := p) (negA p)) =
      X^p * (zpPoly p (negH p) * padicMap (p := p) rationalForcing) +
        (p : PowerSeries ℚ_[p])^3 * zpMap (p := p) (negResidual p) := by
  have hmap := map_bandSeries (algebraMap ℤ_[p] ℚ_[p]) (p : ℤ_[p]) (negA p)
  rw [map_natCast] at hmap
  rw [resOp_band_inv, ← hmap, negA_band hp, negCP_eq hp, rationalForcing_padic, negResidual,
    ← zpMap_intPinv]
  simp only [map_add, map_mul, map_pow, map_X, map_C, map_neg, map_sub, map_one,
    zpMap_polynomial, map_natCast]
  simp only [map_one, map_ofNat, map_natCast]
  ring

end Zeta7Auxiliary

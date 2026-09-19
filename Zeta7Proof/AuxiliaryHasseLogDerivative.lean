import Zeta7Proof.AuxiliaryDerivativeExpansion

/-! P4: the p-adic logarithmic derivative `r` of the actual Hasse quotient and the integral
correction `ξ`, with the exact splitting `u = r + p ξ` of the logarithmic derivative of `B`.
Both `r` and `ξ` are integral in every degree. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
namespace Zeta7Auxiliary
open PowerSeries Zeta7Main Zeta7Common

variable {p : ℕ} [Fact p.Prime]

/-! ### Logarithmic derivatives over a field -/

section LogDer
variable {k : Type*} [Field k]

def logDer (f : PowerSeries k) : PowerSeries k := euler f * f⁻¹

theorem logDer_mul (f g : PowerSeries k) (hf : constantCoeff f ≠ 0)
    (hg : constantCoeff g ≠ 0) : logDer (f * g) = logDer f + logDer g := by
  have hfi := PowerSeries.mul_inv_cancel f hf
  have hgi := PowerSeries.mul_inv_cancel g hg
  have hfg : constantCoeff (f * g) ≠ 0 := by rw [map_mul]; exact mul_ne_zero hf hg
  have hfgi := PowerSeries.mul_inv_cancel (f * g) hfg
  have hinv : (f * g)⁻¹ = f⁻¹ * g⁻¹ := by
    calc (f * g)⁻¹ = (f * g)⁻¹ * ((f * f⁻¹) * (g * g⁻¹)) := by rw [hfi, hgi]; ring
      _ = ((f * g) * (f * g)⁻¹) * (f⁻¹ * g⁻¹) := by ring
      _ = _ := by rw [hfgi, one_mul]
  unfold logDer
  rw [euler_mul_general, hinv]
  linear_combination (euler f * f⁻¹) * hgi + (euler g * g⁻¹) * hfi

theorem constantCoeff_pow_ne (f : PowerSeries k) (hf : constantCoeff f ≠ 0) (n : ℕ) :
    constantCoeff (f^n) ≠ 0 := by
  rw [map_pow]; exact pow_ne_zero n hf

theorem logDer_pow (f : PowerSeries k) (hf : constantCoeff f ≠ 0) (n : ℕ) :
    logDer (f^n) = (n : PowerSeries k) * logDer f := by
  induction n with
  | zero => simp [logDer, euler]
  | succ n ih =>
    rw [pow_succ, logDer_mul _ _ (constantCoeff_pow_ne f hf n) hf, ih]
    push_cast
    ring

theorem logDer_one_add (F : PowerSeries k) (a : k) (h : constantCoeff (1 + C a * F) ≠ 0) :
    logDer (1 + C a * F) = C a * (euler F * (1 + C a * F)⁻¹) := by
  unfold logDer
  rw [euler_add_gen, euler_mul_general]
  simp only [euler, derivative_C, derivative_one, mul_zero, zero_mul, zero_add]
  ring

end LogDer

theorem map_inv_padic (f : PowerSeries ℚ) (hf : constantCoeff f ≠ 0) :
    padicMap (p := p) f⁻¹ = (padicMap (p := p) f)⁻¹ := by
  have hf' : constantCoeff (padicMap (p := p) f) ≠ 0 := by
    change (algebraMap ℚ ℚ_[p]) (constantCoeff f) ≠ 0
    exact (map_ne_zero _).mpr hf
  symm
  apply (PowerSeries.inv_eq_iff_mul_eq_one hf').mpr
  rw [← map_mul, PowerSeries.inv_mul_cancel f hf, map_one]

theorem padicMap_logarithmicB :
    padicMap (p := p) logarithmicB = logDer (padicMap (p := p) BSeries) := by
  unfold logarithmicB logDer
  rw [map_mul, map_euler, map_inv_padic _ (by rw [BSeries_constant]; exact one_ne_zero)]

/-! ### Integral inverses -/

theorem integral_series_cap (φ : PowerSeries ℤ_[p]) (N : ℕ) :
    Cap N 0 (φ.map (algebraMap ℤ_[p] ℚ_[p])) := by
  intro n _
  rw [_root_.pow_zero, one_mul, coeff_map]
  exact integral_coe _

theorem map_invOfUnit (φ : PowerSeries ℤ_[p]) (w : ℤ_[p]ˣ) (h : constantCoeff φ = w) :
    (φ.map (algebraMap ℤ_[p] ℚ_[p]))⁻¹ =
      (φ.invOfUnit w).map (algebraMap ℤ_[p] ℚ_[p]) := by
  have hc : constantCoeff (φ.map (algebraMap ℤ_[p] ℚ_[p])) ≠ 0 := by
    change (algebraMap ℤ_[p] ℚ_[p]) (constantCoeff φ) ≠ 0
    rw [h]
    exact (map_ne_zero_iff _ Subtype.val_injective).mpr w.ne_zero
  apply (PowerSeries.inv_eq_iff_mul_eq_one hc).mpr
  rw [← map_mul, invOfUnit_mul φ w h, map_one]

theorem inv_cap_zero (φ : PowerSeries ℤ_[p]) (w : ℤ_[p]ˣ) (h : constantCoeff φ = w) (N : ℕ) :
    Cap N 0 ((φ.map (algebraMap ℤ_[p] ℚ_[p]))⁻¹) := by
  rw [map_invOfUnit φ w h]
  exact integral_series_cap _ N

/-! ### The Hasse splitting -/

/-- The exponent `e = (p-1)/2` is a unit. -/
theorem half_weight_not_dvd (hp : 5 ≤ p) : ¬p ∣ (p-1)/2 := by
  apply Nat.not_dvd_of_pos_of_lt <;> omega

theorem one_add_prime_mul_isUnit (F0 : ℤ_[p]) : IsUnit (1 + (p : ℤ_[p]) * F0) := by
  have h := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits (-((p : ℤ_[p]) * F0)) (by
    intro hu
    have hn := PadicInt.isUnit_iff.mp hu
    rw [norm_neg, norm_mul, PadicInt.norm_p] at hn
    have h1 : ‖F0‖ ≤ 1 := F0.norm_le_one
    have hp1 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)
    have h0 : (0 : ℝ) ≤ (p : ℝ)⁻¹ := by positivity
    have := mul_le_mul_of_nonneg_left h1 h0
    linarith)
  simpa [sub_neg_eq_add] using h

/-- The integral series `F` of the proved cleared Eisenstein congruence. -/
def hasseCorrection (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) : PowerSeries ℤ_[p] :=
  Classical.choose (integralQuotient_cleared_congruence p hp)

theorem hasseCorrection_spec (hp : 5 ≤ p) :
    (integralP p)^((p-1)/3) * (1 + C (p : ℤ_[p]) * hasseCorrection p hp) =
      (integralB p)^((p-1)/2) * (integralQuotientPolynomial p hp : PowerSeries ℤ_[p]) :=
  Classical.choose_spec (integralQuotient_cleared_congruence p hp)

abbrev zpMap : PowerSeries ℤ_[p] →+* PowerSeries ℚ_[p] := PowerSeries.map (algebraMap ℤ_[p] ℚ_[p])

/-- `Q_p`, the actual integral Hasse quotient, in `ℚ_[p]`. -/
def hasseQp (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) : PowerSeries ℚ_[p] :=
  zpMap (p := p) (integralQuotientPolynomial p hp : PowerSeries ℤ_[p])

def hasseFp (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) : PowerSeries ℚ_[p] :=
  zpMap (p := p) (hasseCorrection p hp)

/-- `r = e⁻¹ (σ Dlog P - Dlog Q_p)` with `e = (p-1)/2`, `σ = (p-1)/3`. -/
def hasseR (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) : PowerSeries ℚ_[p] :=
  C (((p-1)/2 : ℕ) : ℚ_[p])⁻¹ *
    ((((p-1)/3 : ℕ) : PowerSeries ℚ_[p]) * logDer (padicMap (p := p) shortP) -
      logDer (hasseQp p hp))

/-- `ξ = e⁻¹ DF/(1 + pF)`. -/
def hasseXi (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) : PowerSeries ℚ_[p] :=
  C (((p-1)/2 : ℕ) : ℚ_[p])⁻¹ *
    (euler (hasseFp p hp) * (1 + C (p : ℚ_[p]) * hasseFp p hp)⁻¹)

theorem integralP_constant : constantCoeff (integralP p) = 1 := by
  apply Subtype.ext
  rw [← coeff_zero_eq_constantCoeff, integralP, integerSeriesLift, coeff_mk]
  change ((coeff 0 shortP : ℚ) : ℚ_[p]) = 1
  rw [coeff_zero_eq_constantCoeff_apply, shortP_value]
  simp

theorem zpMap_integralP : zpMap (p := p) (integralP p) = padicMap (p := p) shortP :=
  integerSeriesLift_map p _ _

theorem zpMap_integralB : zpMap (p := p) (integralB p) = padicMap (p := p) BSeries :=
  integerSeriesLift_map p _ _

theorem integralQuotient_series_constant (hp : 5 ≤ p) :
    constantCoeff (integralQuotientPolynomial p hp : PowerSeries ℤ_[p]) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe,
    integralQuotientPolynomial_constant]

theorem zp_const_ne {φ : PowerSeries ℤ_[p]} {w : ℤ_[p]ˣ} (h : constantCoeff φ = w) :
    constantCoeff (zpMap (p := p) φ) ≠ 0 := by
  change (algebraMap ℤ_[p] ℚ_[p]) (constantCoeff φ) ≠ 0
  rw [h]
  exact (map_ne_zero_iff _ Subtype.val_injective).mpr w.ne_zero

theorem correction_const (hp : 5 ≤ p) :
    constantCoeff (1 + C (p : ℤ_[p]) * hasseCorrection p hp) =
      ((one_add_prime_mul_isUnit (constantCoeff (hasseCorrection p hp))).unit : ℤ_[p]) := by
  rw [IsUnit.unit_spec, map_add, map_one, map_mul, constantCoeff_C]

theorem zpMap_correction (hp : 5 ≤ p) :
    zpMap (p := p) (1 + C (p : ℤ_[p]) * hasseCorrection p hp) =
      1 + C (p : ℚ_[p]) * hasseFp p hp := by
  rw [map_add, map_one, map_mul, map_C, map_natCast]
  rfl

/-- **The Hasse splitting** `u = r + p ξ` of the actual logarithmic derivative of `B`. -/
theorem logarithmicB_split (hp : 5 ≤ p) :
    padicMap (p := p) logarithmicB = hasseR p hp + (p : PowerSeries ℚ_[p]) * hasseXi p hp := by
  have hPc : constantCoeff (padicMap (p := p) shortP) ≠ 0 := by
    rw [← zpMap_integralP]; exact zp_const_ne (w := 1) (by rw [integralP_constant]; rfl)
  have hBc : constantCoeff (padicMap (p := p) BSeries) ≠ 0 := by
    change (algebraMap ℚ ℚ_[p]) (constantCoeff BSeries) ≠ 0
    rw [BSeries_constant, map_one]; exact one_ne_zero
  have hQc : constantCoeff (hasseQp p hp) ≠ 0 :=
    zp_const_ne (w := 1) (by rw [integralQuotient_series_constant]; rfl)
  have hFc : constantCoeff (1 + C (p : ℚ_[p]) * hasseFp p hp) ≠ 0 := by
    rw [← zpMap_correction]; exact zp_const_ne (correction_const hp)
  have h := congrArg (zpMap (p := p)) (hasseCorrection_spec hp)
  rw [map_mul, map_mul, map_pow, map_pow, zpMap_integralP, zpMap_integralB,
    zpMap_correction] at h
  change _ = _ * hasseQp p hp at h
  have hl := congrArg logDer h
  rw [logDer_mul _ _ (constantCoeff_pow_ne _ hPc _) hFc,
    logDer_mul _ _ (constantCoeff_pow_ne _ hBc _) hQc, logDer_pow _ hPc, logDer_pow _ hBc,
    logDer_one_add _ _ hFc] at hl
  have hpC : (C (p : ℚ_[p]) : PowerSeries ℚ_[p]) = p := map_natCast C p
  have he : C (((p-1)/2 : ℕ) : ℚ_[p])⁻¹ * (((p-1)/2 : ℕ) : PowerSeries ℚ_[p]) = 1 := by
    have hne : (((p-1)/2 : ℕ) : ℚ_[p]) ≠ 0 := by
      exact_mod_cast (show (p-1)/2 ≠ 0 by omega)
    rw [show ((((p-1)/2 : ℕ)) : PowerSeries ℚ_[p]) = C (((p-1)/2 : ℕ) : ℚ_[p]) from
      (map_natCast C _).symm, ← map_mul, inv_mul_cancel₀ hne, map_one]
  rw [padicMap_logarithmicB]
  unfold hasseR hasseXi
  linear_combination (-C (((p-1)/2 : ℕ) : ℚ_[p])⁻¹) * hl -
    logDer (padicMap (p := p) BSeries) * he +
    (C (((p-1)/2 : ℕ) : ℚ_[p])⁻¹ * (euler (hasseFp p hp) *
      (1 + C (p : ℚ_[p]) * hasseFp p hp)⁻¹)) * hpC

theorem inv_half_weight_integral (hp : 5 ≤ p) :
    Integral ((((p-1)/2 : ℕ) : ℚ_[p])⁻¹) :=
  integral_nat_inv (half_weight_not_dvd hp)

theorem cap_C_integral {N : ℕ} {a : ℚ_[p]} (ha : Integral a) {F : PowerSeries ℚ_[p]}
    (hF : Cap N 0 F) : Cap N 0 (C a * F) := by
  simpa using hF.const_mul ⟨a, ha⟩

theorem padic_natCast_cap (n N : ℕ) : Cap N 0 ((n : PowerSeries ℚ_[p])) := by
  have h := (IntegerSeries.natCast n).cap_zero (p := p) N
  rwa [map_natCast] at h

theorem logDer_zp_cap {φ : PowerSeries ℤ_[p]} {w : ℤ_[p]ˣ} (h : constantCoeff φ = w)
    (N : ℕ) : Cap N 0 (logDer (zpMap (p := p) φ)) := by
  have h1 : Cap N 0 (euler (φ.map (algebraMap ℤ_[p] ℚ_[p]))) := (integral_series_cap φ N).euler
  have h2 : Cap N 0 ((φ.map (algebraMap ℤ_[p] ℚ_[p]))⁻¹) := inv_cap_zero φ w h N
  have h3 := h1.mul h2
  exact h3

theorem hasseR_cap (hp : 5 ≤ p) (N : ℕ) : Cap N 0 (hasseR p hp) := by
  have hP : Cap N 0 (logDer (padicMap (p := p) shortP)) := by
    have h := logDer_zp_cap (p := p) (φ := integralP p) (w := 1)
      (by rw [integralP_constant, Units.val_one]) N
    rwa [zpMap_integralP] at h
  have hQ : Cap N 0 (logDer (hasseQp p hp)) :=
    logDer_zp_cap (p := p) (w := 1)
      (by rw [integralQuotient_series_constant, Units.val_one]) N
  have hn : Cap N 0 (((p-1)/3 : ℕ) : PowerSeries ℚ_[p]) := padic_natCast_cap _ N
  have hS : Cap N 0 ((((p-1)/3 : ℕ) : PowerSeries ℚ_[p]) * logDer (padicMap (p := p) shortP) -
      logDer (hasseQp p hp)) := (hn.mul hP).sub hQ
  unfold hasseR
  exact cap_C_integral (inv_half_weight_integral hp) hS

theorem correction_inv_cap (hp : 5 ≤ p) (N : ℕ) :
    Cap N 0 ((1 + C (p : ℚ_[p]) * hasseFp p hp)⁻¹) := by
  rw [← zpMap_correction]
  exact inv_cap_zero (p := p) (1 + C (p : ℤ_[p]) * hasseCorrection p hp) _ (correction_const hp) N

theorem hasseFp_euler_cap (hp : 5 ≤ p) (N : ℕ) : Cap N 0 (euler (hasseFp p hp)) :=
  (integral_series_cap (hasseCorrection p hp) N).euler

theorem hasseXi_cap (hp : 5 ≤ p) (N : ℕ) : Cap N 0 (hasseXi p hp) := by
  have hM := (hasseFp_euler_cap hp N).mul (correction_inv_cap hp N)
  exact cap_C_integral (inv_half_weight_integral hp) hM

end Zeta7Auxiliary

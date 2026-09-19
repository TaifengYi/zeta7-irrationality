import Zeta7Proof.AuxiliaryDerivativeCaps

/-! P4: denominator clearing for the exact maps `F₀, F₁`, their degree bounds, and the
characteristic-`p` divisibility `Q̄ ∣ P̄₂` on the reduction of the exact kernel. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
namespace Zeta7Auxiliary
open PowerSeries Zeta7Main Zeta7Common

variable {p : ℕ} [Fact p.Prime]

/-! ### Euler operator on polynomials -/

section EulerPoly
variable {R : Type*} [CommRing R]

def eulerPoly (f : Polynomial R) : Polynomial R := Polynomial.X * Polynomial.derivative f

theorem eulerPoly_coe (f : Polynomial R) :
    ((eulerPoly f : Polynomial R) : PowerSeries R) = euler (f : PowerSeries R) := by
  rw [eulerPoly, Polynomial.coe_mul, Polynomial.coe_X, euler, PowerSeries.derivative_coe]

theorem eulerPoly_natDegree_le (f : Polynomial R) : (eulerPoly f).natDegree ≤ f.natDegree := by
  unfold eulerPoly
  by_cases h : f.natDegree = 0
  · rw [Polynomial.natDegree_eq_zero.mp h |>.choose_spec.symm, Polynomial.derivative_C, mul_zero]
    simp
  · calc (Polynomial.X * Polynomial.derivative f).natDegree
        ≤ 1 + (Polynomial.derivative f).natDegree := Polynomial.natDegree_mul_le.trans
          (by gcongr; exact Polynomial.natDegree_X_le)
      _ ≤ 1 + (f.natDegree - 1) := by gcongr; exact Polynomial.natDegree_derivative_le f
      _ = f.natDegree := by omega

theorem eulerPoly_map {S : Type*} [CommRing S] (φ : R →+* S) (f : Polynomial R) :
    (eulerPoly f).map φ = eulerPoly (f.map φ) := by
  simp [eulerPoly, Polynomial.derivative_map]

end EulerPoly

/-! ### Integral polynomial data -/

/-- Polynomials over `ℤ_[p]`, viewed as power series over `ℚ_[p]`. -/
abbrev zpPoly (p : ℕ) [Fact p.Prime] : Polynomial ℤ_[p] →+* PowerSeries ℚ_[p] :=
  (zpMap (p := p)).comp Polynomial.coeToPowerSeries.ringHom

theorem zpPoly_apply (f : Polynomial ℤ_[p]) :
    zpPoly p f = zpMap (p := p) (f : PowerSeries ℤ_[p]) := rfl

theorem zpPoly_eulerPoly (f : Polynomial ℤ_[p]) :
    zpPoly p (eulerPoly f) = euler (zpPoly p f) := by
  rw [zpPoly_apply, zpPoly_apply, eulerPoly_coe, map_euler]

theorem zpPoly_injective : Function.Injective (zpPoly p) := by
  intro f g h
  apply Polynomial.coe_injective
  exact PowerSeries.map_injective (algebraMap ℤ_[p] ℚ_[p]) Subtype.val_injective h

def intPolyP (p : ℕ) [Fact p.Prime] : Polynomial ℤ_[p] :=
  1 + 13 * Polynomial.X + 49 * Polynomial.X^2

def intPolyW (p : ℕ) [Fact p.Prime] : Polynomial ℤ_[p] :=
  8 * Polynomial.X * (1 + 16 * Polynomial.X + 49 * Polynomial.X^2)

theorem zpPoly_intPolyP : zpPoly p (intPolyP p) = padicMap (p := p) shortP := by
  rw [shortP_value, intPolyP]
  simp [map_ofNat]

theorem zpPoly_intPolyQ (hp : 5 ≤ p) :
    zpPoly p (integralQuotientPolynomial p hp) = hasseQp p hp := rfl

def einvZ (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) : ℤ_[p] :=
  ⟨(((p-1)/2 : ℕ) : ℚ_[p])⁻¹, inv_half_weight_integral hp⟩

def halfZ (p : ℕ) [Fact p.Prime] (hp : 2 < p) : ℤ_[p] :=
  ⟨(1/2 : ℚ_[p]), by
    have h := integral_nat_inv (p := p) (a := 2) (Nat.not_dvd_of_pos_of_lt (by omega) hp)
    rw [one_div]
    rw [show ((2 : ℕ) : ℚ_[p]) = 2 by norm_num] at h
    exact h⟩

theorem zpPoly_C (a : ℤ_[p]) : zpPoly p (Polynomial.C a) = PowerSeries.C (a : ℚ_[p]) := by
  rw [zpPoly_apply, Polynomial.coe_C, map_C]
  rfl

/-- The cleared logarithmic derivative `ρ = PQ·r`. -/
def rhoPoly (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) : Polynomial ℤ_[p] :=
  Polynomial.C (einvZ p hp) * (Polynomial.C (((p-1)/3 : ℕ) : ℤ_[p]) * eulerPoly (intPolyP p) *
    integralQuotientPolynomial p hp - eulerPoly (integralQuotientPolynomial p hp) * intPolyP p)

theorem hasseQp_const (hp : 5 ≤ p) : constantCoeff (hasseQp p hp) ≠ 0 :=
  zp_const_ne (w := 1) (by rw [integralQuotient_series_constant, Units.val_one])

theorem padicShortP_const : constantCoeff (padicMap (p := p) shortP) ≠ 0 := by
  rw [← zpMap_integralP]
  exact zp_const_ne (w := 1) (by rw [integralP_constant, Units.val_one])

theorem hasseR_cleared (hp : 5 ≤ p) :
    hasseR p hp * (padicMap (p := p) shortP * hasseQp p hp) = zpPoly p (rhoPoly p hp) := by
  have hP := PowerSeries.mul_inv_cancel _ (padicShortP_const (p := p))
  have hQ := PowerSeries.mul_inv_cancel _ (hasseQp_const hp)
  rw [rhoPoly, map_mul, map_sub, map_mul, map_mul, map_mul, zpPoly_C, zpPoly_C,
    zpPoly_eulerPoly, zpPoly_eulerPoly, zpPoly_intPolyP, zpPoly_intPolyQ]
  unfold hasseR logDer
  have hσ : PowerSeries.C ((((p-1)/3 : ℕ) : ℤ_[p]) : ℚ_[p]) =
      (((p-1)/3 : ℕ) : PowerSeries ℚ_[p]) := by
    rw [← map_natCast (PowerSeries.C (R := ℚ_[p]))]
    congr 1
  rw [hσ]
  change PowerSeries.C (((p-1)/2 : ℕ) : ℚ_[p])⁻¹ * _ * _ =
    PowerSeries.C (((p-1)/2 : ℕ) : ℚ_[p])⁻¹ * _
  linear_combination
    (PowerSeries.C (((p-1)/2 : ℕ) : ℚ_[p])⁻¹ * (((p-1)/3 : ℕ) : PowerSeries ℚ_[p]) *
      euler (padicMap (p := p) shortP) * hasseQp p hp) * hP -
    (PowerSeries.C (((p-1)/2 : ℕ) : ℚ_[p])⁻¹ * euler (hasseQp p hp) *
      padicMap (p := p) shortP) * hQ

theorem rationalPotential_cleared :
    rationalPotential * shortP^2 = 8 * PowerSeries.X * (1 + 16 * PowerSeries.X + 49 * PowerSeries.X^2) := by
  have hc : constantCoeff ((1 + 13 * PowerSeries.X + 49 * PowerSeries.X ^ 2 : PowerSeries ℚ)^2) ≠ 0 := by
    simp
  have h := PowerSeries.inv_mul_cancel _ hc
  rw [rationalPotential, shortP_value]
  linear_combination (8 * PowerSeries.X * (1 + 16 * PowerSeries.X + 49 * PowerSeries.X ^ 2)) * h

theorem potential_cleared :
    padicMap (p := p) rationalPotential * (padicMap (p := p) shortP)^2 = zpPoly p (intPolyW p) := by
  rw [← map_pow, ← map_mul, rationalPotential_cleared, intPolyW]
  simp [map_ofNat]

theorem zpPoly_halfZ (hp : 2 < p) : zpPoly p (Polynomial.C (halfZ p hp)) = PowerSeries.C (1/2 : ℚ_[p]) := by
  rw [zpPoly_C]; rfl

/-- The cleared exact map `(PQ)² F₀`. -/
def clearedF0 (p : ℕ) [Fact p.Prime] (hp : 11 ≤ p) (P0 P1 P2 : Polynomial ℤ_[p]) :
    Polynomial ℤ_[p] :=
  (intPolyP p * integralQuotientPolynomial p (by omega))^2 * P0 +
    (intPolyP p * integralQuotientPolynomial p (by omega)) * rhoPoly p (by omega) * P1 +
    Polynomial.C (halfZ p (by omega)) * (integralQuotientPolynomial p (by omega)^2 * intPolyW p +
      rhoPoly p (by omega)^2) * P2

/-- The cleared exact map `(PQ) F₁`. -/
def clearedF1 (p : ℕ) [Fact p.Prime] (hp : 11 ≤ p) (P1 P2 : Polynomial ℤ_[p]) :
    Polynomial ℤ_[p] :=
  (intPolyP p * integralQuotientPolynomial p (by omega)) * P1 + rhoPoly p (by omega) * P2

theorem derivativeF0_cleared (hp : 11 ≤ p) (P0 P1 P2 : Polynomial ℤ_[p]) :
    (padicMap (p := p) shortP * hasseQp p (by omega))^2 *
        derivativeF0 (by omega) (P0 : PowerSeries ℤ_[p]) P1 P2 =
      zpPoly p (clearedF0 p hp P0 P1 P2) := by
  have hr := hasseR_cleared (p := p) (by omega)
  have hV := potential_cleared (p := p)
  unfold clearedF0 derivativeF0
  simp only [map_add, map_mul, map_pow, zpPoly_intPolyP, zpPoly_intPolyQ, zpPoly_halfZ,
    ← zpPoly_apply]
  rw [← hr, ← hV]
  ring

theorem derivativeF1_cleared (hp : 11 ≤ p) (P1 P2 : Polynomial ℤ_[p]) :
    (padicMap (p := p) shortP * hasseQp p (by omega)) *
        derivativeF1 (by omega) (P1 : PowerSeries ℤ_[p]) P2 =
      zpPoly p (clearedF1 p hp P1 P2) := by
  have hr := hasseR_cleared (p := p) (by omega)
  unfold clearedF1 derivativeF1
  simp only [map_add, map_mul, zpPoly_intPolyP, zpPoly_intPolyQ, ← zpPoly_apply]
  rw [← hr]
  ring

theorem cleared_factor_ne (hp : 5 ≤ p) (k : ℕ) :
    (padicMap (p := p) shortP * hasseQp p hp)^k ≠ 0 := by
  apply pow_ne_zero
  intro h
  have hc := congrArg constantCoeff h
  rw [map_mul, map_zero] at hc
  exact mul_ne_zero (padicShortP_const (p := p)) (hasseQp_const hp) hc

/-- The exact kernel of `F₀` is the kernel of its integral clearing. -/
theorem derivativeF0_eq_zero_iff (hp : 11 ≤ p) (P0 P1 P2 : Polynomial ℤ_[p]) :
    derivativeF0 (by omega) (P0 : PowerSeries ℤ_[p]) P1 P2 = 0 ↔ clearedF0 p hp P0 P1 P2 = 0 := by
  constructor
  · intro h
    apply zpPoly_injective (p := p)
    rw [← derivativeF0_cleared, h, mul_zero, map_zero]
  · intro h
    have h' := derivativeF0_cleared hp P0 P1 P2
    rw [h, map_zero] at h'
    exact (mul_eq_zero.mp h').resolve_left (cleared_factor_ne (by omega) 2)

end Zeta7Auxiliary

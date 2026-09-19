import Zeta7Proof.AuxiliaryRationalHasseQuotient
import Zeta7Proof.AuxiliaryActualGermCaps

/-! Integral coefficients of the actual Hasse quotient, after polynomiality. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
namespace Zeta7Auxiliary
open PowerSeries Zeta7Main Zeta7Common
variable (p : ℕ) [Fact p.Prime]

theorem prime_half_weight (hp : 5 ≤ p) : 2*((p-1)/2) = p-1 := by
  have h := (Fact.out : p.Prime).even_sub_one (by omega)
  obtain ⟨k,hk⟩ := h
  omega

theorem eisensteinSeries_cap_zero (hp : 5 ≤ p) (N : ℕ) :
    Cap N 0 ((eisensteinSeries (p-1)).map (algebraMap ℚ ℚ_[p])) := by
  intro j hj
  rw [pow_zero, one_mul, coeff_map]
  by_cases hj0 : j = 0
  · subst j
    simpa [eisensteinSeries, eisensteinCoefficient] using (integral_one (p := p))
  · change ‖(algebraMap ℚ ℚ_[p]) (coeff j (eisensteinSeries (p-1)))‖ ≤ 1
    simp only [eisensteinSeries, coeff_mk]
    apply (eisensteinCoefficient_congruence p (by omega) j hj0).trans
    exact (inv_le_one₀ (by positivity : (0:ℝ)<p)).mpr (by exact_mod_cast (by omega : 1 ≤ p))

theorem shortP_integer : IntegerSeries shortP := by
  rw [shortP_value]
  exact (IntegerSeries.one.add ((IntegerSeries.natCast 13).mul IntegerSeries.X)).add
    ((IntegerSeries.natCast 49).mul (IntegerSeries.X.pow 2))

theorem rationalQuotientPolynomial_integral (hp : 5 ≤ p) (j : ℕ) :
    Integral ((rationalQuotientPolynomial ((p-1)/2)).coeff j : ℚ_[p]) := by
  let n := (p-1)/2
  have hn : 2 ≤ n := by dsimp [n]; omega
  have he : 2*n = p-1 := prime_half_weight p hp
  have hi : IntegerSeries (shortP^(2*n/3) * (BSeries⁻¹)^n) :=
    (shortP_integer.pow _).mul ((BSeries_integer.inv BSeries_constant).pow _)
  have ht := (eisensteinSeries_cap_zero p hp (j+1)).subst_integer
    qSeries_integer qSeries_constant
  have hm := (hi.cap_zero (p := p) (j+1)).mul ht
  have hs : PowerSeries.map (algebraMap ℚ ℚ_[p])
      (qTransport (eisensteinSeries (p-1))) =
      ((eisensteinSeries (p-1)).map (algebraMap ℚ ℚ_[p])).subst
        (qSeries.map (algebraMap ℚ ℚ_[p])) := by
    rw [qTransport_apply]
    exact map_subst (h := algebraMap ℚ ℚ_[p]) q_hasSubst _
  have hcap : Cap (j+1) 0 ((rationalQuotientSeries n).map (algebraMap ℚ ℚ_[p])) := by
    simpa only [rationalQuotientSeries, he, map_mul, hs, zero_add] using hm
  have hj := hcap j (by omega)
  rw [pow_zero, one_mul, coeff_map, ← rationalQuotientPolynomial_series n hn,
    Polynomial.coeff_coe] at hj
  exact hj

def integralQuotientSeries (hp : 5 ≤ p) : PowerSeries ℤ_[p] :=
  PowerSeries.mk (fun j => ⟨((rationalQuotientPolynomial ((p-1)/2)).coeff j : ℚ_[p]),
    rationalQuotientPolynomial_integral p hp j⟩)

def integralQuotientPolynomial (hp : 5 ≤ p) : Polynomial ℤ_[p] :=
  (integralQuotientSeries p hp).trunc (2*((p-1)/3)+1)

theorem integralQuotientPolynomial_map (hp : 5 ≤ p) :
    (integralQuotientPolynomial p hp).map (algebraMap ℤ_[p] ℚ_[p]) =
      (rationalQuotientPolynomial ((p-1)/2)).map (algebraMap ℚ ℚ_[p]) := by
  have hn : 2 ≤ (p-1)/2 := by omega
  have he := prime_half_weight p hp
  ext j
  simp only [Polynomial.coeff_map, integralQuotientPolynomial, coeff_trunc]
  split_ifs with hj
  · simp only [integralQuotientSeries, coeff_mk, PadicInt.algebraMap_apply]
    rfl
  · rw [map_zero, Polynomial.coeff_eq_zero_of_natDegree_lt (by
      rw [rationalQuotientPolynomial_degree _ hn, he]; omega), map_zero]

theorem integralQuotientPolynomial_constant (hp : 5 ≤ p) :
    (integralQuotientPolynomial p hp).coeff 0 = 1 := by
  apply Subtype.ext
  change (algebraMap ℤ_[p] ℚ_[p]) ((integralQuotientPolynomial p hp).coeff 0) = 1
  rw [← Polynomial.coeff_map, integralQuotientPolynomial_map,
    Polynomial.coeff_map, rationalQuotientPolynomial_constant, map_one]

theorem integralQuotientPolynomial_degree (hp : 5 ≤ p) :
    (integralQuotientPolynomial p hp).natDegree = 2*((p-1)/3) := by
  rw [← Polynomial.natDegree_map_eq_of_injective (f := algebraMap ℤ_[p] ℚ_[p]) Subtype.val_injective,
    integralQuotientPolynomial_map, Polynomial.natDegree_map,
    rationalQuotientPolynomial_degree _ (by omega), prime_half_weight p hp]

theorem integralQuotientPolynomial_lead (hp : 5 ≤ p) :
    (integralQuotientPolynomial p hp).leadingCoeff =
      (49:ℤ_[p])^((p-1)/3) * (-7:ℤ_[p])^((p-1)/2) := by
  apply Subtype.ext
  change (algebraMap ℤ_[p] ℚ_[p]) (integralQuotientPolynomial p hp).leadingCoeff =
    (algebraMap ℤ_[p] ℚ_[p]) ((49:ℤ_[p])^((p-1)/3) * (-7:ℤ_[p])^((p-1)/2))
  have h := congrArg Polynomial.leadingCoeff (integralQuotientPolynomial_map p hp)
  rw [Polynomial.leadingCoeff_map_of_injective (f := algebraMap ℤ_[p] ℚ_[p]) Subtype.val_injective,
    Polynomial.leadingCoeff_map, rationalQuotientPolynomial_lead _ (by omega),
    prime_half_weight p hp] at h
  simpa only [map_mul, map_pow, map_ofNat, map_neg] using h

/-- The actual complete Hasse quotient identity over Qp, with an integral polynomial. -/
theorem integralQuotientPolynomial_identity (hp : 5 ≤ p) :
    (shortP.map (algebraMap ℚ ℚ_[p]))^((p-1)/3) *
        (qTransport (eisensteinSeries (p-1))).map (algebraMap ℚ ℚ_[p]) =
      (BSeries.map (algebraMap ℚ ℚ_[p]))^((p-1)/2) *
        ((integralQuotientPolynomial p hp).map (algebraMap ℤ_[p] ℚ_[p]) :
          Polynomial ℚ_[p]) := by
  rw [integralQuotientPolynomial_map, Polynomial.polynomial_map_coe]
  have h := congrArg (PowerSeries.map (algebraMap ℚ ℚ_[p]))
    (rationalQuotientPolynomial_identity ((p-1)/2) (by omega))
  simpa only [prime_half_weight p hp, map_mul, map_pow] using h

end Zeta7Auxiliary

import Zeta7Proof.AuxiliaryIntegralHasseQuotient
import Mathlib.RingTheory.MvPowerSeries.Expand

/-! Reduction of the actual Hasse quotient and the cleared Frobenius equation. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
namespace Zeta7Auxiliary
open PowerSeries Zeta7Main Zeta7Common
variable (p : ℕ) [Fact p.Prime]

def integerSeriesLift (f : PowerSeries ℚ) (hf : IntegerSeries f) : PowerSeries ℤ_[p] :=
  PowerSeries.mk (fun j => ⟨((coeff j f : ℚ) : ℚ_[p]), hf.integral_coeff j⟩)

theorem integerSeriesLift_map (f : PowerSeries ℚ) (hf : IntegerSeries f) :
    (integerSeriesLift p f hf).map (algebraMap ℤ_[p] ℚ_[p]) =
      f.map (algebraMap ℚ ℚ_[p]) := by
  ext j
  simp only [coeff_map, integerSeriesLift, coeff_mk, PadicInt.algebraMap_apply]
  rfl

theorem integerSeriesLift_constant (f : PowerSeries ℚ) (hf : IntegerSeries f)
    (h0 : constantCoeff f = 0) : constantCoeff (integerSeriesLift p f hf) = 0 := by
  apply Subtype.ext
  rw [← coeff_zero_eq_constantCoeff, integerSeriesLift, coeff_mk]
  change ((coeff 0 f : ℚ) : ℚ_[p]) = 0
  rw [coeff_zero_eq_constantCoeff, h0, Rat.cast_zero]

abbrev integralB := integerSeriesLift p BSeries BSeries_integer
abbrev integralP := integerSeriesLift p shortP shortP_integer
abbrev integralQCoordinate := integerSeriesLift p qSeries qSeries_integer
def reducedB : PowerSeries (ZMod p) := (integralB p).map PadicInt.toZMod
def reducedP : PowerSeries (ZMod p) := (integralP p).map PadicInt.toZMod
def reducedQuotient (hp : 5 ≤ p) : Polynomial (ZMod p) :=
  (integralQuotientPolynomial p hp).map PadicInt.toZMod

theorem reducedP_value : reducedP p = 1 + 13*X + 49*X^2 := by
  have hi : integralP p = 1 + 13*X + 49*X^2 := by
    apply PowerSeries.map_injective (algebraMap ℤ_[p] ℚ_[p]) Subtype.val_injective
    rw [integerSeriesLift_map, shortP_value]
    simp [map_ofNat]
  rw [reducedP, hi]
  simp [map_ofNat]

theorem integralQuotient_cleared_congruence (hp : 5 ≤ p) :
    ∃ F : PowerSeries ℤ_[p],
      (integralP p)^((p-1)/3) * (1 + C (p:ℤ_[p])*F) =
        (integralB p)^((p-1)/2) * (integralQuotientPolynomial p hp : PowerSeries ℤ_[p]) := by
  obtain ⟨F,hF⟩ := eisensteinSeries_congruence p (by omega)
  have hq0 := integerSeriesLift_constant p qSeries qSeries_integer qSeries_constant
  let substQ : PowerSeries ℤ_[p] →ₐ[ℤ_[p]] PowerSeries ℤ_[p] :=
    substAlgHom (HasSubst.of_constantCoeff_zero hq0)
  refine ⟨substQ F, ?_⟩
  apply PowerSeries.map_injective (algebraMap ℤ_[p] ℚ_[p]) Subtype.val_injective
  rw [map_mul, map_pow, integerSeriesLift_map, map_mul, map_pow, integerSeriesLift_map]
  rw [← Polynomial.polynomial_map_coe, ← integralQuotientPolynomial_identity p hp]
  congr 1
  rw [map_add, map_one, map_mul, map_C, map_natCast]
  have hs : PowerSeries.map (algebraMap ℤ_[p] ℚ_[p]) (substQ F) =
      (F.map (algebraMap ℤ_[p] ℚ_[p])).subst (qSeries.map (algebraMap ℚ ℚ_[p])) := by
    simp only [substQ, coe_substAlgHom]
    have hh : PowerSeries.map (algebraMap ℤ_[p] ℚ_[p]) (F.subst (integralQCoordinate p)) =
        (F.map (algebraMap ℤ_[p] ℚ_[p])).subst
          ((integralQCoordinate p).map (algebraMap ℤ_[p] ℚ_[p])) :=
      map_subst (h := algebraMap ℤ_[p] ℚ_[p]) (HasSubst.of_constantCoeff_zero hq0) F
    rw [integerSeriesLift_map] at hh
    exact hh
  rw [hs]
  have hsub : PowerSeries.map (algebraMap ℚ ℚ_[p]) (qTransport (eisensteinSeries (p-1))) =
      ((eisensteinSeries (p-1)).map (algebraMap ℚ ℚ_[p])).subst
        (qSeries.map (algebraMap ℚ ℚ_[p])) := by
    rw [qTransport_apply]
    exact map_subst (h := algebraMap ℚ ℚ_[p]) q_hasSubst _
  rw [hsub, hF]
  have hqm : HasSubst (qSeries.map (algebraMap ℚ ℚ_[p])) :=
    HasSubst.of_constantCoeff_zero (by
      change (algebraMap ℚ ℚ_[p]) (constantCoeff qSeries) = 0
      rw [qSeries_constant, map_zero])
  rw [← coe_substAlgHom hqm, map_add, map_one, map_mul]
  have hc : substAlgHom hqm (C (p:ℚ_[p])) = C (p:ℚ_[p]) :=
    (substAlgHom hqm).commutes (p:ℚ_[p])
  rw [hc]

theorem reducedQuotient_identity (hp : 5 ≤ p) :
    (reducedP p)^((p-1)/3) =
      (reducedB p)^((p-1)/2) * (reducedQuotient p hp : PowerSeries (ZMod p)) := by
  obtain ⟨F,hF⟩ := integralQuotient_cleared_congruence p hp
  have h := congrArg (PowerSeries.map (PadicInt.toZMod (p := p))) hF
  have hpC : PowerSeries.map (PadicInt.toZMod (p := p)) (C (p:ℤ_[p])) = 0 := by
    rw [map_C]
    have hz : PadicInt.toZMod (p:ℤ_[p]) = 0 := by
      rw [map_natCast, ZMod.natCast_self]
    rw [hz, map_zero]
  simpa only [map_mul, map_pow, map_add, map_one, hpC, zero_mul, add_zero, mul_one,
    ← Polynomial.polynomial_map_coe, reducedP, reducedB, reducedQuotient] using h

theorem reducedQuotient_constant (hp : 5 ≤ p) : (reducedQuotient p hp).coeff 0 = 1 := by
  simp [reducedQuotient, integralQuotientPolynomial_constant]

theorem quotient_reduced_lead_nonzero (hp : 11 ≤ p) :
    (49:ZMod p)^((p-1)/3) * (-7:ZMod p)^((p-1)/2) ≠ 0 := by
  have h7 : (7:ZMod p) ≠ 0 := by
    intro h
    have hd := (ZMod.natCast_eq_zero_iff 7 p).mp h
    have := Nat.le_of_dvd (by decide : 0 < 7) hd
    omega
  have h49 : (49:ZMod p) ≠ 0 := by
    rw [show (49:ZMod p) = 7^2 by norm_num]
    exact pow_ne_zero _ h7
  exact mul_ne_zero (pow_ne_zero _ h49) (pow_ne_zero _ (neg_ne_zero.mpr h7))

theorem reducedQuotient_degree (hp : 11 ≤ p) :
    (reducedQuotient p (by omega)).natDegree = 2*((p-1)/3) := by
  rw [reducedQuotient, (Polynomial.natDegree_map_eq_iff.mpr (Or.inl (by
    simpa only [integralQuotientPolynomial_lead, map_mul, map_pow, map_ofNat, map_neg]
      using quotient_reduced_lead_nonzero p hp))), integralQuotientPolynomial_degree]

theorem reducedQuotient_lead (hp : 11 ≤ p) :
    (reducedQuotient p (by omega)).leadingCoeff =
      (49:ZMod p)^((p-1)/3) * (-7:ZMod p)^((p-1)/2) := by
  rw [Polynomial.leadingCoeff, reducedQuotient_degree p hp, reducedQuotient,
    Polynomial.coeff_map, ← integralQuotientPolynomial_degree p (by omega),
    Polynomial.coeff_natDegree, integralQuotientPolynomial_lead]
  simp only [map_mul, map_pow, map_ofNat, map_neg]

theorem reducedB_frobenius_cleared (hp : 5 ≤ p) :
    (reducedP p)^(2*((p-1)/3)) * reducedB p =
      (reducedQuotient p hp : PowerSeries (ZMod p))^2 * (reducedB p)^p := by
  have h := congrArg (fun z : PowerSeries (ZMod p) => z^2 * reducedB p)
    (reducedQuotient_identity p hp)
  have he := prime_half_weight p hp
  calc
    _ = ((reducedP p)^((p-1)/3))^2 * reducedB p := by rw [← pow_mul]; congr 2; omega
    _ = _ := h
    _ = _ := by
      rw [mul_pow, ← pow_mul, mul_comm ((p-1)/2) 2, he]
      have he' : p-1+1=p := by omega
      rw [mul_right_comm, ← pow_succ, he', mul_comm]

theorem zmod_series_frobenius (F : PowerSeries (ZMod p)) :
    F^p = expand p (Fact.out : p.Prime).ne_zero F := by
  have h := MvPowerSeries.map_frobenius_expand (R := ZMod p) p
    (Fact.out : p.Prime).ne_zero (f := F)
  have hf : frobenius (ZMod p) p = RingHom.id (ZMod p) := by
    ext a
    simpa only [frobenius_def, RingHom.id_apply, ZMod.card] using FiniteField.pow_card a
  rw [hf, MvPowerSeries.map_id] at h
  exact h.symm

theorem reducedB_expansion_cleared (hp : 5 ≤ p) :
    (reducedP p)^(2*((p-1)/3)) * reducedB p =
      (reducedQuotient p hp : PowerSeries (ZMod p))^2 *
        expand p (Fact.out : p.Prime).ne_zero (reducedB p) := by
  rw [← zmod_series_frobenius]
  exact reducedB_frobenius_cleared p hp

end Zeta7Auxiliary

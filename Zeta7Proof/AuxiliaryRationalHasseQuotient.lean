import Zeta7Proof.AuxiliaryClearedExpansion

/-! Rational descent of the complete, bounded-degree modular quotient. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
namespace Zeta7Auxiliary
open PowerSeries Zeta7Main Zeta7Common UpperHalfPlane ModularForm MatrixGroups
open scoped ModularForm

def rationalQuotientSeries (n : ℕ) : PowerSeries ℚ :=
  shortP^(2*n/3) * (BSeries⁻¹)^n * qTransport (eisensteinSeries (2*n))

def rationalQuotientPolynomial (n : ℕ) : Polynomial ℚ :=
  (rationalQuotientSeries n).trunc (2*(2*n/3)+1)

theorem qTransport_constant (f : PowerSeries ℚ) :
    constantCoeff (qTransport f) = constantCoeff f := by
  have h := constantCoeff_subst_eq_zero qSeries_constant (f-C (constantCoeff f)) (by simp)
  change constantCoeff ((f-C (constantCoeff f)).subst qSeries) = 0 at h
  rw [← qTransport_apply] at h
  rw [map_sub] at h
  have hc : qTransport (C (constantCoeff f)) = C (constantCoeff f) := by
    exact qTransport.commutes (constantCoeff f)
  exact sub_eq_zero.mp (by simpa only [hc, map_sub, constantCoeff_C] using h)

theorem rationalQuotientSeries_constant (n : ℕ) :
    constantCoeff (rationalQuotientSeries n) = 1 := by
  simp only [rationalQuotientSeries, map_mul, map_pow, qTransport_constant,
    constantCoeff_inv, shortP_constant, BSeries_constant, inv_one, one_pow, one_mul]
  simp [eisensteinSeries, eisensteinCoefficient, ← coeff_zero_eq_constantCoeff]

theorem rationalQuotientSeries_complex (n : ℕ) (hn : 2 ≤ n) :
    complexSeriesMap (rationalQuotientSeries n) =
      clearedExpansion n (ModularForm.mcast (by push_cast; ring)
        (ModularForm.E (k := 2*n) (by omega))) := by
  rw [clearedExpansion_apply, ModularForm.qExpansion_mcast]
  rw [← eisensteinSeries_complex (2*n) (by omega) (even_two_mul n), complexQTransport_map]
  exact map_mul _ _ _

theorem rationalQuotientSeries_polynomial (n : ℕ) (hn : 2 ≤ n) :
    ∃ Q : Polynomial ℂ, (Q : PowerSeries ℂ) = complexSeriesMap (rationalQuotientSeries n) ∧
      Q.natDegree ≤ 2*(2*n/3) ∧ Q.coeff (2*(2*n/3)) = (49:ℂ)^(2*n/3)*(-7:ℂ)^n := by
  obtain ⟨Q,hQ,dQ,tQ⟩ := clearedExpansion_polynomial n
    (ModularForm.mcast (by push_cast; ring) (ModularForm.E (k := 2*n) (by omega)))
  rw [← rationalQuotientSeries_complex n hn] at hQ
  have h0 : Q.coeff 0 = 1 := by
    have hh := congrArg constantCoeff hQ
    change Q.coeff 0 = (algebraMap ℚ ℂ) (constantCoeff (rationalQuotientSeries n)) at hh
    simpa [rationalQuotientSeries_constant] using hh
  exact ⟨Q,hQ,dQ,by simpa [h0] using tQ⟩

theorem rationalQuotientSeries_high_coeff (n : ℕ) (hn : 2 ≤ n)
    (j : ℕ) (hj : 2*(2*n/3) < j) : coeff j (rationalQuotientSeries n) = 0 := by
  obtain ⟨Q,hQ,dQ,tQ⟩ := rationalQuotientSeries_polynomial n hn
  have hh := congrArg (coeff j) hQ
  rw [Polynomial.coeff_coe, coeff_map, Polynomial.coeff_eq_zero_of_natDegree_lt (dQ.trans_lt hj)] at hh
  exact (algebraMap ℚ ℂ).injective (by simpa using hh.symm)

/-- Equality of complete series, after the all-weight modular polynomiality proof. -/
theorem rationalQuotientPolynomial_series (n : ℕ) (hn : 2 ≤ n) :
    (rationalQuotientPolynomial n : PowerSeries ℚ) = rationalQuotientSeries n := by
  ext j
  rw [Polynomial.coeff_coe, rationalQuotientPolynomial, coeff_trunc]
  split_ifs with hj
  · rfl
  · exact (rationalQuotientSeries_high_coeff n hn j (by omega)).symm

theorem rationalQuotientPolynomial_constant (n : ℕ) :
    (rationalQuotientPolynomial n).coeff 0 = 1 := by
  rw [rationalQuotientPolynomial, coeff_trunc, if_pos (by omega)]
  simpa only [coeff_zero_eq_constantCoeff] using rationalQuotientSeries_constant n

theorem rationalQuotientPolynomial_top (n : ℕ) (hn : 2 ≤ n) :
    (rationalQuotientPolynomial n).coeff (2*(2*n/3)) = (49:ℚ)^(2*n/3)*(-7:ℚ)^n := by
  obtain ⟨Q,hQ,dQ,tQ⟩ := rationalQuotientSeries_polynomial n hn
  have hh := congrArg (coeff (2*(2*n/3))) hQ
  rw [Polynomial.coeff_coe, coeff_map, tQ] at hh
  rw [rationalQuotientPolynomial, coeff_trunc, if_pos (by omega)]
  apply (algebraMap ℚ ℂ).injective
  simpa only [map_mul, map_pow, map_ofNat, map_neg] using hh.symm

theorem rationalQuotientPolynomial_degree (n : ℕ) (hn : 2 ≤ n) :
    (rationalQuotientPolynomial n).natDegree = 2*(2*n/3) := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    (Nat.lt_succ_iff.mp (natDegree_trunc_lt _ _))
  change (rationalQuotientPolynomial n).coeff (2*(2*n/3)) ≠ 0
  rw [rationalQuotientPolynomial_top n hn]
  exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ (by norm_num))

theorem rationalQuotientPolynomial_lead (n : ℕ) (hn : 2 ≤ n) :
    (rationalQuotientPolynomial n).leadingCoeff = (49:ℚ)^(2*n/3)*(-7:ℚ)^n := by
  rw [Polynomial.leadingCoeff, rationalQuotientPolynomial_degree n hn]
  exact rationalQuotientPolynomial_top n hn

theorem rationalQuotientPolynomial_identity (n : ℕ) (hn : 2 ≤ n) :
    shortP^(2*n/3) * qTransport (eisensteinSeries (2*n)) =
      BSeries^n * (rationalQuotientPolynomial n : PowerSeries ℚ) := by
  rw [rationalQuotientPolynomial_series n hn, rationalQuotientSeries]
  calc
    _ = (BSeries * BSeries⁻¹)^n *
        (shortP^(2*n/3) * qTransport (eisensteinSeries (2*n))) := by
      rw [BSeries_mul_inv, one_pow, one_mul]
    _ = _ := by rw [mul_pow]; ring

end Zeta7Auxiliary

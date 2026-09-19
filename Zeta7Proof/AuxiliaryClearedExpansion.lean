import Zeta7Proof.AuxiliaryLevelOneGeneration
import Zeta7Proof.AuxiliaryActualE6Quotient
import Zeta7Proof.AuxiliaryEisensteinCongruence

/-! The cleared expansion of a genuine level-one form in the original coordinate. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
namespace Zeta7Auxiliary
open PowerSeries Zeta7Main Zeta7Common UpperHalfPlane ModularForm MatrixGroups
open scoped ModularForm

abbrev complexSeriesMap : PowerSeries ℚ →+* PowerSeries ℂ := PowerSeries.map (algebraMap ℚ ℂ)

def complexQTransport : PowerSeries ℂ →ₐ[ℂ] PowerSeries ℂ :=
  substAlgHom (HasSubst.of_constantCoeff_zero (a := complexSeriesMap qSeries) (by
    change (algebraMap ℚ ℂ) (constantCoeff qSeries) = 0
    rw [qSeries_constant, map_zero]))

theorem complexQTransport_map (f : PowerSeries ℚ) :
    complexQTransport (complexSeriesMap f) = complexSeriesMap (qTransport f) := by
  rw [qTransport_apply]
  simp only [complexQTransport, coe_substAlgHom]
  exact (map_subst (h := algebraMap ℚ ℂ) q_hasSubst f).symm

def levelOneExpansion (n : ℕ) :
    ModularForm 𝒮ℒ (2*(n:ℤ)) →ₗ[ℂ] PowerSeries ℂ where
  toFun f := qExpansion 1 f
  map_add' f g := ModularForm.qExpansion_add one_pos one_mem_strictPeriods_SL f g
  map_smul' c f := ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL c f

def clearedExpansion (n : ℕ) :
    ModularForm 𝒮ℒ (2*(n:ℤ)) →ₗ[ℂ] PowerSeries ℂ :=
  (LinearMap.mulLeft ℂ (complexSeriesMap (shortP^(2*n/3) * (BSeries⁻¹)^n))).comp
    (complexQTransport.toLinearMap.comp (levelOneExpansion n))

theorem clearedExpansion_apply (n : ℕ) (f : ModularForm 𝒮ℒ (2*(n:ℤ))) :
    clearedExpansion n f = complexSeriesMap (shortP^(2*n/3) * (BSeries⁻¹)^n) *
      complexQTransport (qExpansion 1 f) := rfl

theorem weightedMonomial_expansion {n : ℕ} (a b : ℕ) (h : 2*a+3*b=n) :
    qExpansion 1 (weightedMonomial a b h) =
      complexSeriesMap (eisensteinFourQ^a * eisensteinSixQ^b) := by
  simp only [weightedMonomial, ModularForm.qExpansion_mcast,
    ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL,
    map_mul, map_pow, complexSeriesMap, eisensteinFourQ_classical,
    eisensteinSixQ_classical, ModularForm.E₄, ModularForm.E₆]

theorem clearedExpansion_monomial {n : ℕ} (a b : ℕ) (h : 2*a+3*b=n) :
    clearedExpansion n (weightedMonomial a b h) =
      complexSeriesMap (quotientMonomial (2*n/3) a b : Polynomial ℚ) := by
  rw [clearedExpansion_apply, weightedMonomial_expansion, complexQTransport_map, ← map_mul]
  apply congrArg complexSeriesMap
  simp only [map_mul, map_pow]
  change shortP^(2*n/3) * (BSeries⁻¹)^n * (pulledE4^a * pulledE6^b) = _
  calc
    _ = (BSeries⁻¹)^n * (shortP^(2*n/3) * (pulledE4^a * pulledE6^b)) := by ring
    _ = (BSeries⁻¹)^n * (BSeries^(2*a+3*b) *
        (quotientMonomial (2*n/3) a b : Polynomial ℚ)) := by
      rw [pulled_monomial_cleared _ _ _ (monomial_denominator_bound h)]
    _ = _ := by
      rw [h, ← mul_assoc, ← mul_pow, mul_comm BSeries⁻¹ BSeries,
        BSeries_mul_inv, one_pow, one_mul]

theorem clearedExpansion_polynomial (n : ℕ) (f : ModularForm 𝒮ℒ (2*(n:ℤ))) :
    ∃ Q : Polynomial ℂ, (Q : PowerSeries ℂ) = clearedExpansion n f ∧
      Q.natDegree ≤ 2*(2*n/3) ∧
      Q.coeff (2*(2*n/3)) = (49:ℂ)^(2*n/3) * (-7:ℂ)^n * Q.coeff 0 := by
  have hf := levelOne_mem_weightedSpan n f
  change f ∈ Submodule.span ℂ _ at hf
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨a,b,h,rfl⟩ := hf
    refine ⟨(quotientMonomial (2*n/3) a b).map (algebraMap ℚ ℂ), ?_, ?_, ?_⟩
    · rw [clearedExpansion_monomial, Polynomial.polynomial_map_coe]
    · rw [Polynomial.natDegree_map, quotientMonomial_degree _ _ _ (monomial_denominator_bound h)]
    · simp only [Polynomial.coeff_map, quotientMonomial_constant, map_one, mul_one,
        quotientMonomial_top _ _ _ (monomial_denominator_bound h), h, map_mul,
        map_pow, map_ofNat, map_neg]
  | zero => exact ⟨0, by simp, by simp, by simp⟩
  | add f g _ _ hf hg =>
    obtain ⟨Q,hQ,dQ,tQ⟩ := hf
    obtain ⟨S,hS,dS,tS⟩ := hg
    refine ⟨Q+S, ?_, (Polynomial.natDegree_add_le _ _).trans (max_le dQ dS), ?_⟩
    · rw [Polynomial.coe_add, map_add, hQ, hS]
    · simp only [Polynomial.coeff_add, tQ, tS]; ring
  | smul c f _ hf =>
    obtain ⟨Q,hQ,dQ,tQ⟩ := hf
    refine ⟨c • Q, ?_, (Polynomial.natDegree_smul_le _ _).trans dQ, ?_⟩
    · rw [Polynomial.coe_smul, map_smul, hQ]
    · simp only [Polynomial.coeff_smul, smul_eq_mul, tQ]; ring

end Zeta7Auxiliary

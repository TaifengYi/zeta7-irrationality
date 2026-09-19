import Zeta7Proof.LevelOneSerre

/-! The weight-four Ramanujan identity for the original Eisenstein series.
Finite determination here is justified by the proved level-one Sturm theorem.
This is separate from the still-required level-seven quotient identities. -/
noncomputable section
open UpperHalfPlane Derivative PowerSeries Filter
open scoped MatrixGroups ModularForm Manifold Topology
namespace Zeta7Classical
open Zeta7Common

theorem constantCoeff_map_rat (f : ℚ⟦X⟧) :
    constantCoeff (f.map (algebraMap ℚ ℂ)) = (algebraMap ℚ ℂ) (constantCoeff f) := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply]

theorem constantCoeff_euler_complex (f : ℂ⟦X⟧) : constantCoeff (euler f) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, euler_coeff]
  simp

theorem normalizedDeriv_analyticAt_cusp_one {f : ℍ → ℂ}
    (hp : Function.Periodic (f ∘ ofComplex) 1) (hh : MDiff f)
    (hb : IsBoundedAtImInfty f) :
    AnalyticAt ℂ (cuspFunction 1 (normalizedDerivOfComplex f)) 0 := by
  have ha := analyticAt_deriv_cuspFunction (by norm_num : (0 : ℝ) < 1) hp hh hb
  apply (analyticAt_id.mul ha).congr
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1)] with w hw
  simpa using (cuspFunction_deriv (by norm_num : (0 : ℝ) < 1) hp hh hb
    (mem_ball_zero_iff.mp hw)).symm

theorem serreLevelOne_qExpansion {k : ℤ} (f : ModularForm 𝒮ℒ k) :
    qExpansion 1 (serreLevelOne f) = euler (qExpansion 1 f) -
      ((k : ℂ) * 12⁻¹) • (qExpansion 1 EisensteinSeries.E2 * qExpansion 1 f) := by
  have hp := SlashInvariantFormClass.periodic_comp_ofComplex f one_mem_strictPeriods_SL
  have hh := ModularFormClass.holo f
  have hb := ModularFormClass.bdd_at_infty f
  have hf := ModularFormClass.analyticAt_cuspFunction_zero f (by norm_num) one_mem_strictPeriods_SL
  have he := Zeta7Common.E2_analyticAt_cusp
  have hmul : AnalyticAt ℂ (cuspFunction 1 (EisensteinSeries.E2 * (f : ℍ → ℂ))) 0 := by
    rw [UpperHalfPlane.cuspFunction_mul he.continuousAt hf.continuousAt]
    exact he.mul hf
  have hsmul : AnalyticAt ℂ
      (cuspFunction 1 (((k : ℂ) * 12⁻¹) • (EisensteinSeries.E2 * (f : ℍ → ℂ)))) 0 := by
    rw [UpperHalfPlane.cuspFunction_smul hmul.continuousAt]
    exact hmul.const_smul
  have heq : (serreLevelOne f : ℍ → ℂ) = normalizedDerivOfComplex f -
      ((k : ℂ) * 12⁻¹) • (EisensteinSeries.E2 * (f : ℍ → ℂ)) := by
    funext τ
    change normalizedDerivOfComplex f τ - (k : ℂ) * 12⁻¹ * EisensteinSeries.E2 τ * f τ =
      normalizedDerivOfComplex f τ - ((k : ℂ) * 12⁻¹) * (EisensteinSeries.E2 τ * f τ)
    ring
  rw [heq, UpperHalfPlane.qExpansion_sub (normalizedDeriv_analyticAt_cusp_one hp hh hb) hsmul,
    qExpansion_normalizedDeriv_one hp hh hb, UpperHalfPlane.qExpansion_smul hmul,
    UpperHalfPlane.qExpansion_mul he hf]

/-- Serre differentiation of the actual normalized weight-four Eisenstein form. -/
theorem serre_E4 :
    serreLevelOne (ModularForm.E (k := 4) (by decide)) =
      (-1 / 3 : ℂ) • ModularForm.E (k := 6) (by decide) := by
  apply levelOne_eq_of_coeff_zero (k := 6) (by decide)
  rw [serreLevelOne_qExpansion, FunLike.coe_smul,
    ModularForm.qExpansion_smul (by norm_num) one_mem_strictPeriods_SL]
  rw [← eisensteinFourQ_classical, ← eisensteinSixQ_classical, ← eisensteinTwoQ_classical]
  norm_num [euler_coeff, coeff_mul, coeff_map, eisensteinFourQ, sigmaThree,
    eisensteinSixQ, sigmaFive, eisensteinTwoQ, sigmaOne, constantCoeff_map_rat,
    constantCoeff_euler_complex, constantCoeff_mk]

/-- θE₄ = (E₂E₄ − E₆)/3, as an equality of complete rational power series. -/
theorem eisensteinFourQ_ramanujan :
    C (3 : ℚ) * euler eisensteinFourQ = eisensteinTwoQ * eisensteinFourQ - eisensteinSixQ := by
  have h := congrArg (fun f : ModularForm 𝒮ℒ 6 => qExpansion 1 f) serre_E4
  rw [serreLevelOne_qExpansion, FunLike.coe_smul,
    ModularForm.qExpansion_smul (by norm_num) one_mem_strictPeriods_SL] at h
  rw [← eisensteinFourQ_classical, ← eisensteinSixQ_classical, ← eisensteinTwoQ_classical] at h
  apply PowerSeries.map_injective (algebraMap ℚ ℂ) (RingHom.injective _) 
  simp only [map_mul, map_sub, map_C, map_euler]
  ext n
  have hc := congrArg (coeff n) h
  norm_num [coeff_C_mul, map_sub, coeff_smul] at hc ⊢
  linear_combination 3 * hc

end Zeta7Classical

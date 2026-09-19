import Zeta7Proof.RamanujanFour

/-! The weight-two Ramanujan identity via cancellation of the quasimodular
correction and the proved level-one Sturm bound. -/
noncomputable section
open UpperHalfPlane hiding I
open Derivative PowerSeries Filter Complex EisensteinSeries Matrix.SpecialLinearGroup
open scoped MatrixGroups ModularForm Manifold Topology Real
namespace Zeta7Classical
open Zeta7Common

def e2Shift (γ : SL(2, ℤ)) (τ : ℍ) : ℂ :=
  12 * (2 * π * I)⁻¹ * (γ 1 0 : ℂ) * (denom γ τ) ^ (-1 : ℤ)

theorem e2Shift_holo (γ : SL(2, ℤ)) : MDiff (e2Shift γ) := by
  exact mdifferentiable_const.mul (mdifferentiable_denom_zpow (mapGL ℝ γ) (-1))

theorem E2_slash_add_shift (γ : SL(2, ℤ)) : E2 ∣[(2 : ℤ)] γ = E2 + e2Shift γ := by
  rw [E2_slash_action]
  ext τ
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, e2Shift, D2,
    zpow_neg_one, riemannZeta_two]
  field_simp
  ring_nf
  simp [I_sq]

theorem e2Shift_deriv (γ : SL(2, ℤ)) (τ : ℍ) :
    normalizedDerivOfComplex (e2Shift γ) τ =
      -12 * (2 * π * I)⁻¹ ^ 2 * ((γ 1 0 : ℂ) / denom γ τ) ^ 2 := by
  have heq : e2Shift γ ∘ ofComplex =ᶠ[𝓝 (τ : ℂ)] fun w : ℂ =>
      12 * (2 * π * I)⁻¹ * (γ 1 0 : ℂ) * (denom γ w) ^ (-1 : ℤ) := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos] with w hw
    simp [e2Shift, Function.comp_apply, ofComplex_apply_of_im_pos hw]
  rw [normalizedDerivOfComplex, heq.deriv_eq]
  have hd := (hasDerivAt_denom_zpow (mapGL ℝ γ) (-1) τ).const_mul
    (12 * (2 * π * I)⁻¹ * (γ 1 0 : ℂ))
  erw [hd.deriv]
  norm_num [zpow_neg, div_eq_mul_inv, mapGL]
  ring

def ramanujanTwoFunction : ℍ → ℂ := E2 * E2 - (12 : ℂ) • normalizedDerivOfComplex E2

theorem ramanujanTwoFunction_slash (γ : SL(2, ℤ)) :
    ramanujanTwoFunction ∣[(4 : ℤ)] γ = ramanujanTwoFunction := by
  have hd := normalizedDerivOfComplex_SL_slash (k := 2) E2_mdifferentiable (γ := γ)
  rw [E2_slash_add_shift, normalizedDerivOfComplex_add _ _ E2_mdifferentiable
    (e2Shift_holo γ)] at hd
  ext τ
  have hdz := congrFun hd τ
  simp only [Pi.add_apply, Pi.sub_apply, e2Shift_deriv] at hdz
  have hm := congrFun (ModularForm.mul_slash_SL2 2 2 γ E2 E2) τ
  simp only [E2_slash_add_shift, Pi.mul_apply, Pi.add_apply] at hm
  simp only [ramanujanTwoFunction, sub_eq_add_neg, SlashAction.add_slash,
    SlashAction.neg_slash, ModularForm.SL_smul_slash,
    Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul, Pi.mul_apply]
  rw [show (2 : ℤ) + 2 = 4 from rfl] at hdz hm
  rw [hm]
  simp only [Pi.add_apply, e2Shift, zpow_neg_one, div_eq_mul_inv] at hdz ⊢
  linear_combination 12 * hdz

def ramanujanTwoForm : ModularForm 𝒮ℒ 4 :=
  levelOneForm ramanujanTwoFunction
    ((E2_mdifferentiable.mul E2_mdifferentiable).sub
      (mdifferentiable_const.mul (normalizedDerivOfComplex_mdifferentiable E2_mdifferentiable)))
    ramanujanTwoFunction_slash (by
      have he : BoundedAtFilter atImInfty (E2 * E2) :=
        BoundedAtFilter.mul isBoundedAtImInfty_E2 isBoundedAtImInfty_E2
      have hd := (normalizedDeriv_zero_at_infty (by norm_num : (0 : ℝ) < 1)
        E2_periodic_comp_ofComplex E2_mdifferentiable isBoundedAtImInfty_E2).isBoundedAtImInfty
      simpa only [IsBoundedAtImInfty, ramanujanTwoFunction, sub_eq_add_neg] using
        BoundedAtFilter.add he (BoundedAtFilter.neg (hd.smul (12 : ℂ))))

theorem ramanujanTwoForm_qExpansion :
    qExpansion 1 ramanujanTwoForm = qExpansion 1 E2 * qExpansion 1 E2 -
      (12 : ℂ) • euler (qExpansion 1 E2) := by
  have he := E2_analyticAt_cusp
  have hp : AnalyticAt ℂ (cuspFunction 1 (E2 * E2)) 0 := by
    rw [UpperHalfPlane.cuspFunction_mul he.continuousAt he.continuousAt]
    exact he.mul he
  have hd := normalizedDeriv_analyticAt_cusp_one E2_periodic_comp_ofComplex
    E2_mdifferentiable isBoundedAtImInfty_E2
  have hds : AnalyticAt ℂ (cuspFunction 1 ((12 : ℂ) • normalizedDerivOfComplex E2)) 0 := by
    rw [UpperHalfPlane.cuspFunction_smul hd.continuousAt]
    exact hd.const_smul
  change qExpansion 1 (E2 * E2 - (12 : ℂ) • normalizedDerivOfComplex E2) = _
  rw [UpperHalfPlane.qExpansion_sub hp hds, UpperHalfPlane.qExpansion_mul he he,
    UpperHalfPlane.qExpansion_smul hd, qExpansion_normalizedDeriv_one
      E2_periodic_comp_ofComplex E2_mdifferentiable isBoundedAtImInfty_E2]

theorem ramanujanTwoForm_eq_E4 : ramanujanTwoForm = ModularForm.E (k := 4) (by decide) := by
  apply levelOne_eq_of_coeff_zero (k := 4) (by decide)
  rw [ramanujanTwoForm_qExpansion, ← eisensteinFourQ_classical, ← eisensteinTwoQ_classical]
  norm_num [euler_coeff, coeff_mul, coeff_map, eisensteinFourQ, sigmaThree,
    eisensteinTwoQ, sigmaOne, constantCoeff_map_rat, constantCoeff_euler_complex,
    constantCoeff_mk]

theorem eisensteinTwoQ_ramanujan :
    C (12 : ℚ) * euler eisensteinTwoQ = eisensteinTwoQ ^ 2 - eisensteinFourQ := by
  have h := congrArg (fun f : ModularForm 𝒮ℒ 4 => qExpansion 1 f) ramanujanTwoForm_eq_E4
  rw [ramanujanTwoForm_qExpansion, ← eisensteinFourQ_classical, ← eisensteinTwoQ_classical] at h
  apply PowerSeries.map_injective (algebraMap ℚ ℂ) (RingHom.injective _)
  simp only [map_mul, map_sub, map_pow, map_C, map_euler]
  ext n
  have hc := congrArg (coeff n) h
  norm_num [coeff_C_mul, map_sub, coeff_smul, pow_two] at hc ⊢
  linear_combination -hc

end Zeta7Classical

import Zeta7Proof.ActualAEisenstein
import Zeta7Proof.ActualModularEquation
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.MDifferentiable

/-! Identification of the complete rational expansions with the genuine
classical Eisenstein functions needed in Section 1.1. -/
set_option autoImplicit false
noncomputable section
open PowerSeries
namespace Zeta7Common

theorem E2_periodic_comp_ofComplex :
    Function.Periodic (EisensteinSeries.E2 ∘ UpperHalfPlane.ofComplex) (1 : ℂ) := by
  intro w
  by_cases hw : 0 < w.im
  · have hw' : 0 < (w + 1).im := by simpa using hw
    simp only [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos hw,
      UpperHalfPlane.ofComplex_apply_of_im_pos hw']
    have he : Complex.exp (2 * Real.pi * Complex.I * (w + 1)) =
        Complex.exp (2 * Real.pi * Complex.I * w) := by
      simpa only [mul_add, mul_one] using
        Complex.exp_periodic (2 * Real.pi * Complex.I * w)
    simp only [EisensteinSeries.E2_eq_tsum_cexp, he]
  · have hw' : (w + 1).im ≤ 0 := by simpa using le_of_not_gt hw
    simp [UpperHalfPlane.ofComplex_apply_of_im_nonpos hw',
      UpperHalfPlane.ofComplex_apply_of_im_nonpos (le_of_not_gt hw)]

theorem E2_analyticAt_cusp :
    AnalyticAt ℂ (UpperHalfPlane.cuspFunction 1 EisensteinSeries.E2) 0 :=
  UpperHalfPlane.analyticAt_cuspFunction_zero (by norm_num)
    (by simpa using E2_periodic_comp_ofComplex) E2_mdifferentiable
    EisensteinSeries.isBoundedAtImInfty_E2

/-- Full q-expansion equality, not a finite comparison. -/
theorem eisensteinTwoQ_classical :
    eisensteinTwoQ.map (algebraMap ℚ ℂ) =
      UpperHalfPlane.qExpansion 1 EisensteinSeries.E2 := by
  ext n
  have hs (τ : UpperHalfPlane) : HasSum (fun m : ℕ =>
      (if m = 0 then 1 else -24 * (ArithmeticFunction.sigma 1 m : ℂ)) •
        Function.Periodic.qParam 1 τ ^ m) (EisensteinSeries.E2 τ) := by
    simpa only [Function.Periodic.qParam, Complex.ofReal_one, div_one]
      using EisensteinSeries.hasSum_qExpansion_E2 (z := τ)
  rw [coeff_map]
  calc
    _ = (if n = 0 then 1 else -24 * (ArithmeticFunction.sigma 1 n : ℂ)) := by
      by_cases hn : n = 0
      · subst n
        simp [eisensteinTwoQ, sigmaOne]
      · simp [eisensteinTwoQ, sigmaOne, coeff_one, hn, ArithmeticFunction.sigma_apply]
    _ = _ := by
      let E2c : C(UpperHalfPlane, ℂ) := ⟨EisensteinSeries.E2, E2_mdifferentiable.continuous⟩
      exact UpperHalfPlane.qExpansion_coeff_unique E2c
        (by norm_num : (0 : ℝ) < 1) E2_analyticAt_cusp hs n

def sigmaFive (n : ℕ) : ℚ := ∑ d ∈ n.divisors, (d : ℚ) ^ 5
def eisensteinSixQ : ℚ⟦X⟧ := 1 - C (504 : ℚ) * mk sigmaFive

theorem eisensteinSixQ_classical :
    eisensteinSixQ.map (algebraMap ℚ ℂ) =
      UpperHalfPlane.qExpansion 1 (ModularForm.E (k := 6) (by decide)) := by
  ext n
  rw [coeff_map, EisensteinSeries.E_qExpansion_coeff _ (by decide)]
  by_cases hn : n = 0
  · subst n
    simp [eisensteinSixQ, sigmaFive]
  · have hb : bernoulli 6 = (1 / 42 : ℚ) := by decide +kernel
    norm_num [eisensteinSixQ, sigmaFive, coeff_one, hn, hb,
      ArithmeticFunction.sigma_apply]

end Zeta7Common

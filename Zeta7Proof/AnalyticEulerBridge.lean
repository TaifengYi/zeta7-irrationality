import Zeta7Proof.LevelSevenEtaCusps
import Zeta7Proof.GenusSevenCoordinate
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-! Passing from the actual locally uniform Euler product to every Taylor coefficient. -/
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open Filter
open scoped Topology PowerSeries.WithPiTopology
namespace Zeta7LevelSeven

theorem polynomial_iteratedDeriv (p : Polynomial ℂ) (n : ℕ) :
    iteratedDeriv n p.eval = (Polynomial.derivative^[n] p).eval := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ, ih, Function.iterate_succ_apply']
    funext z
    exact Polynomial.deriv _

theorem polynomial_taylorCoeff (p : Polynomial ℂ) (n : ℕ) :
    iteratedDeriv n p.eval 0 / (n.factorial : ℂ) = p.coeff n := by
  rw [polynomial_iteratedDeriv]
  change (Polynomial.derivative^[n] p).eval 0 / _ = _
  rw [← Polynomial.coeff_zero_eq_eval_zero,
    Polynomial.coeff_iterate_derivative]
  simp [Nat.descFactorial_self, Nat.factorial_ne_zero]

def eulerPartialPolynomial (s : Finset ℕ) : Polynomial ℚ :=
  ∏ j ∈ s, (1 - Polynomial.X ^ (j + 1))

theorem eulerPartialPolynomial_eval (s : Finset ℕ) (z : ℂ) :
    ((eulerPartialPolynomial s).map (algebraMap ℚ ℂ)).eval z =
      ∏ j ∈ s, (1 - z ^ (j + 1)) := by
  simp [eulerPartialPolynomial, Polynomial.eval_prod]

theorem eulerPartialPolynomial_deriv_limit (n : ℕ) :
    TendstoLocallyUniformlyOn
      (fun s : Finset ℕ => iteratedDeriv n
        ((eulerPartialPolynomial s).map (algebraMap ℚ ℂ)).eval)
      (iteratedDeriv n analyticEuler) atTop (Metric.ball 0 1) := by
  induction n with
  | zero =>
    change TendstoLocallyUniformlyOn
      (fun s : Finset ℕ => ((eulerPartialPolynomial s).map (algebraMap ℚ ℂ)).eval)
      (fun q : ℂ => ∏' n : ℕ, (1 - q ^ (n + 1))) atTop (Metric.ball 0 1)
    simpa only [HasProdLocallyUniformlyOn, iteratedDeriv_zero, eulerPartialPolynomial_eval,
      Finset.prod_apply, analyticEuler] using
      ModularForm.multipliableLocallyUniformlyOn_one_sub_pow.hasProdLocallyUniformlyOn
  | succ n ih =>
    simpa only [iteratedDeriv_succ, Function.comp_def] using
      ih.deriv (Eventually.of_forall fun s => by
        rw [polynomial_iteratedDeriv]
        exact Polynomial.differentiableOn _) Metric.isOpen_ball

theorem analyticEuler_coeff_limit (n : ℕ) :
    Tendsto (fun s : Finset ℕ =>
      (algebraMap ℚ ℂ) ((eulerPartialPolynomial s).coeff n)) atTop
      (𝓝 (iteratedDeriv n analyticEuler 0 / (n.factorial : ℂ))) := by
  have h := ((eulerPartialPolynomial_deriv_limit n).tendsto_at
    (by simp : (0 : ℂ) ∈ Metric.ball 0 1)).div_const (n.factorial : ℂ)
  simpa only [polynomial_taylorCoeff, Polynomial.coeff_map] using h

theorem eulerPartialPolynomial_series (s : Finset ℕ) :
    (eulerPartialPolynomial s : PowerSeries ℚ) =
      ∏ j ∈ s, (1 - PowerSeries.X ^ (j + 1)) := by
  change Polynomial.coeToPowerSeries.ringHom (eulerPartialPolynomial s) = _
  simp [eulerPartialPolynomial, map_prod, Polynomial.coeToPowerSeries.ringHom_apply]

/-- Equality in every degree, proved by uniqueness of the two coefficient limits. -/
theorem analyticEuler_taylorCoeff (n : ℕ) :
    iteratedDeriv n analyticEuler 0 / (n.factorial : ℂ) =
      (algebraMap ℚ ℂ) (PowerSeries.coeff n Zeta7GenusSeven.euler) := by
  have h := (PowerSeries.WithPiTopology.continuous_coeff ℚ n).tendsto
    Zeta7GenusSeven.euler |>.comp Zeta7GenusSeven.euler_multipliable.hasProd
  have hc := (continuous_algebraMap ℚ ℂ).tendsto
    (PowerSeries.coeff n Zeta7GenusSeven.euler) |>.comp h
  apply tendsto_nhds_unique (analyticEuler_coeff_limit n)
  simpa only [SummationFilter.unconditional, Function.comp_def,
    ← eulerPartialPolynomial_series, Polynomial.coeff_coe] using hc

theorem analyticEuler_hasSum {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n => (algebraMap ℚ ℂ)
      (PowerSeries.coeff n Zeta7GenusSeven.euler) * z ^ n) (analyticEuler z) := by
  have h := Complex.hasSum_taylorSeries_on_ball
    ModularForm.differentiableOn_tprod_one_sub_pow
    (by simpa using hz : z ∈ Metric.ball (0 : ℂ) 1)
  change HasSum (fun n => (n.factorial : ℂ)⁻¹ • (z - 0) ^ n •
    iteratedDeriv n analyticEuler 0) (analyticEuler z) at h
  simp only [← analyticEuler_taylorCoeff]
  convert h using 1 <;> try rfl
  · funext n
    simp only [smul_eq_mul, sub_zero, div_eq_mul_inv]
    ring

end Zeta7LevelSeven

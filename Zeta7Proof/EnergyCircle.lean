import Zeta7Proof.ValenceJensen
import Zeta7Proof.ValenceIntegral
import Zeta7Proof.ArchCTheorem

/-! Circle averages of the potential and the pointwise bound for `U` on each circle.

* `circle_to_unit`: `circleAverage f 0 e^{-2πy} = ∫_0^1 f(e^{2πi(u + iy)}) du`.
* `log_mean`: `circleAverage (log |x|) 0 e^{-2πy} = -2πy`, from `x = q · u(q)` with `u` analytic and
  nonvanishing on the unit disc, `u(0) = 1`.
* `potentialU_eq`: `U(z) = Σ_j w_j · circleAverage (log |z - x(·)|) 0 r_j`.
* `potential_point_le`: at every generic point of the circle of height `y_i`,
  `U(x(q')) ≤ log |x(q')| + Σ_j w_j Σ_{p ∈ box} orbitTerm(y_i, y_j, u, p)`. -/
noncomputable section
set_option autoImplicit false
namespace Zeta7Valence
open Complex Zeta7Arch Zeta7LevelSeven MeasureTheory Metric Real
open UpperHalfPlane hiding I
open scoped MatrixGroups

theorem circlePt_eq_qParam (y u : ℝ) :
    circleMap 0 (Real.exp (-(2 * π * y))) (2 * π * u) = Function.Periodic.qParam 1 ((u : ℂ) + y * I) := by
  unfold circleMap Function.Periodic.qParam
  rw [zero_add, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring_nf
  rw [I_sq]
  ring

theorem circle_to_unit (f : ℂ → ℝ) (y : ℝ) :
    circleAverage f 0 (Real.exp (-(2 * π * y))) =
      ∫ u in (0 : ℝ)..1, f (Function.Periodic.qParam 1 ((u : ℂ) + y * I)) := by
  rw [circleAverage_def, smul_eq_mul]
  have h2pi : (2 * π : ℝ) ≠ 0 := by positivity
  have hsub := intervalIntegral.integral_comp_mul_left
    (fun θ => f (circleMap 0 (Real.exp (-(2 * π * y))) θ)) h2pi (a := 0) (b := 1)
  simp only [mul_zero, mul_one, smul_eq_mul] at hsub
  rw [← hsub]
  congr 1
  funext u
  rw [circlePt_eq_qParam]

/-! ### The unit factor of `x` -/

/-- `x(q)/q` as an analytic function on the unit disc. -/
def uFun (q : ℂ) : ℂ := evalQ uC q

theorem uFun_analytic : AnalyticOnNhd ℂ uFun (ball 0 1) := uC_tempered'.analyticOnNhd

theorem uFun_zero : uFun 0 = 1 := by
  rw [uFun, evalQ_zero_point, uC, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply, Zeta7Main.xUnit_constant]
  simp

theorem uFun_ne_zero {q : ℂ} (hq : ‖q‖ < 1) : uFun q ≠ 0 := by
  by_cases h0 : q = 0
  · rw [h0, uFun_zero]; exact one_ne_zero
  · intro hu
    have := xFun_ne_zero h0 hq
    rw [xFun_eq_mul hq] at this
    exact this (by rw [show evalQ uC q = uFun q from rfl, hu, mul_zero])

/-- **The circle mean of `log |x|`.** -/
theorem log_mean {y : ℝ} (hy : 0 < y) :
    circleAverage (fun q => Real.log ‖xFun q‖) 0 (Real.exp (-(2 * π * y))) = -(2 * π * y) := by
  set R := Real.exp (-(2 * π * y)) with hR
  have hR0 : 0 < R := Real.exp_pos _
  have hR1 : R < 1 := by rw [hR, ← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by nlinarith [pi_pos])
  have habs : |R| = R := abs_of_pos hR0
  have hcongr : Set.EqOn (fun q => Real.log ‖xFun q‖) (fun q => Real.log R + Real.log ‖uFun q‖)
      (sphere 0 |R|) := by
    intro q hq
    rw [habs, mem_sphere, dist_zero_right] at hq
    have hq1 : ‖q‖ < 1 := by rw [hq]; exact hR1
    have hq0 : q ≠ 0 := by intro h; rw [h, norm_zero] at hq; linarith
    simp only
    rw [xFun_eq_mul hq1, show evalQ uC q = uFun q from rfl, norm_mul, Real.log_mul (norm_ne_zero_iff.mpr hq0)
      (norm_ne_zero_iff.mpr (uFun_ne_zero hq1)), hq]
  rw [circleAverage_congr_sphere hcongr]
  have hball : closedBall (0 : ℂ) |R| ⊆ ball 0 1 := fun z hz => by
    rw [habs, mem_closedBall, dist_zero_right] at hz; rw [mem_ball, dist_zero_right]; linarith
  have hua : AnalyticOnNhd ℂ uFun (closedBall 0 |R|) := fun z hz => uFun_analytic z (hball hz)
  have hu0 : ∀ z ∈ closedBall (0 : ℂ) |R|, uFun z ≠ 0 := fun z hz => by
    have := hball hz; rw [mem_ball, dist_zero_right] at this; exact uFun_ne_zero this
  have hint : CircleIntegrable (fun q => Real.log ‖uFun q‖) 0 R := by
    apply ContinuousOn.circleIntegrable'
    intro z hz
    have hzb : z ∈ closedBall (0 : ℂ) |R| := sphere_subset_closedBall hz
    exact ((hua z hzb).continuousAt.norm.log (norm_ne_zero_iff.mpr (hu0 z hzb))).continuousWithinAt
  rw [show (fun q : ℂ => Real.log R + Real.log ‖uFun q‖) =
      (fun _ : ℂ => Real.log R) + (fun q => Real.log ‖uFun q‖) from rfl,
    circleAverage_add (circleIntegrable_const _ _ _) hint, circleAverage_const,
    hua.circleAverage_log_norm_of_ne_zero hu0, uFun_zero, norm_one, Real.log_one, add_zero, hR,
    Real.log_exp]

/-! ### The potential as a weighted sum of circle averages -/

theorem measure_le (j : Fin 6) :
    ENNReal.ofReal (circleW j) • circleMeasure j ≤ potentialMeasure := by
  unfold potentialMeasure
  exact Finset.single_le_sum (f := fun i => ENNReal.ofReal (circleW i) • circleMeasure i)
    (fun i _ => bot_le) (Finset.mem_univ j)

theorem integrable_log_circle (z : ℂ) (j : Fin 6) :
    Integrable (fun w => Real.log ‖z - w‖) (circleMeasure j) := by
  have h := (integrable_log z).mono_measure (measure_le j)
  have hw : ENNReal.ofReal (circleW j) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact circleW_pos j
  exact (integrable_smul_measure hw ENNReal.ofReal_ne_top).mp h

theorem circleAverage_log_circle (z : ℂ) (j : Fin 6) :
    ∫ w, Real.log ‖z - w‖ ∂circleMeasure j =
      circleAverage (fun q => Real.log ‖z - xFun q‖) 0 (circleR j) := by
  rw [integral_circleMeasure j (measurable_log_dist z).aestronglyMeasurable,
    circleAverage_def, smul_eq_mul, intervalIntegral.integral_of_le two_pi_pos.le,
    ← integral_Icc_eq_integral_Ioc]
  congr 1
  refine setIntegral_congr_fun measurableSet_Icc fun θ _ => ?_
  simp [circleMap, circlePt, circFun]

theorem potentialU_eq (z : ℂ) :
    potentialU z = ∑ j, circleW j * circleAverage (fun q => Real.log ‖z - xFun q‖) 0 (circleR j) := by
  rw [potentialU, integral_potentialMeasure (integrable_log_circle z)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [circleAverage_log_circle]

/-- **The pointwise bound for `U`** at a generic point of the circle of height `y_i`. -/
theorem potential_point_le (i : Fin 6) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hfib : ∀ τ : ℍ, etaCoordinate τ = etaCoordinate (horPt (circleY_pos i) u) →
      ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 7 ∧ τ = γ • horPt (circleY_pos i) u)
    (hder : deriv Xf ((horPt (circleY_pos i) u : ℍ) : ℂ) ≠ 0) :
    potentialU (xFun (Function.Periodic.qParam 1 (horPt (circleY_pos i) u))) ≤
      Real.log ‖xFun (Function.Periodic.qParam 1 (horPt (circleY_pos i) u))‖ +
        ∑ j, circleW j * ∑ p ∈ cosetBox (circleY i) (circleY j), orbitTerm (circleY i) (circleY j) u p := by
  set z := xFun (Function.Periodic.qParam 1 (horPt (circleY_pos i) u)) with hz
  rw [potentialU_eq]
  have hbound : ∀ j, circleAverage (fun q => Real.log ‖z - xFun q‖) 0 (circleR j) ≤
      Real.log ‖z‖ + ∑ p ∈ cosetBox (circleY i) (circleY j), orbitTerm (circleY i) (circleY j) u p := by
    intro j
    have h := jensen_bound (circleY_pos i) (circleY_pos j) hu0 hu1 hfib hder
    have hsym : (fun q => Real.log ‖z - xFun q‖) = fun q => Real.log ‖xFun q - z‖ := by
      funext q; rw [norm_sub_rev]
    rw [hsym]
    exact h
  calc ∑ j, circleW j * circleAverage (fun q => Real.log ‖z - xFun q‖) 0 (circleR j)
      ≤ ∑ j, circleW j * (Real.log ‖z‖ + ∑ p ∈ cosetBox (circleY i) (circleY j),
          orbitTerm (circleY i) (circleY j) u p) :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hbound j) (circleW_pos j).le
    _ = (∑ j, circleW j) * Real.log ‖z‖ + ∑ j, circleW j * ∑ p ∈ cosetBox (circleY i) (circleY j),
          orbitTerm (circleY i) (circleY j) u p := by
        rw [Finset.sum_mul, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => by ring
    _ = _ := by rw [circleW_sum, one_mul]

end Zeta7Valence

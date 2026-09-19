import Zeta7Proof.EnergyOrbit

/-! **The energy of the actual six-circle measure is bounded by the explicit formula (48).**

* `energyW_le`: `W_i = ∫ U dμ_i ≤ Σ_j w_j E(y_i, y_j)`.
* `energyI_le_explicitI`: `I = ∫ U dμ ≤ Σ_{i,j} w_i w_j E(y_i, y_j)`.

For almost every point `x(q')` of the circle of height `y_i` (`generic_fiber`), the potential satisfies
the pointwise Jensen bound (`potential_point_le`); integrating over the circle, the mean of `log|x|`
is `-2πy_i` (`log_mean`) and the averaged orbit terms are bounded by `2π(y_i - y_j)₊` plus the
arccosine terms of (48) (`orbit_integral_le`). -/
noncomputable section
set_option autoImplicit false
namespace Zeta7Valence
open Real MeasureTheory Zeta7Arch Zeta7Cert Complex
open UpperHalfPlane hiding I

theorem circleY_eq_cy (i : Fin 6) : circleY i = ((cy i : ℚ) : ℝ) := by
  fin_cases i <;> norm_num [circleY, cy]

theorem circleW_eq_cw (i : Fin 6) : circleW i = ((cw i : ℚ) : ℝ) := by
  fin_cases i <;> norm_num [circleW, cw]

theorem cy_pos (i : Fin 6) : 0 < cy i := by
  have := circleY_pos i
  rw [circleY_eq_cy] at this
  exact_mod_cast this

theorem orbitTerm_continuous {y t : ℝ} {p : ℤ × ℤ} (hy : 0 < y) (hp : p ∈ cosetBox y t) :
    Continuous fun u => orbitTerm y t u p := by
  have hs : bottomShape p := (Finset.mem_filter.mp hp).2
  rcases hs with ⟨h1, h2⟩ | ⟨h1, _, _⟩
  · have : (fun u => orbitTerm y t u p) = fun _ => 2 * π * max 0 (y - t) := by
      funext u; rw [show p = (0, 1) from Prod.ext h1 h2, orbitTerm_zero_one]
    rw [this]; exact continuous_const
  · have hc : (0 : ℝ) < p.1 := by exact_mod_cast h1
    simp only [orbitTerm_eq_profile]
    exact (profile_continuous hy hc).comp (by fun_prop)

theorem q_continuous (y : ℝ) (hy : 0 < y) :
    Continuous fun u : ℝ => xFun (Function.Periodic.qParam 1 ((u : ℂ) + y * I)) := by
  have hq : Continuous fun u : ℝ => Function.Periodic.qParam 1 ((u : ℂ) + y * I) :=
    (Function.Periodic.differentiable_qParam.continuous).comp (by fun_prop)
  refine continuous_iff_continuousAt.mpr fun u => ?_
  have hmem : Function.Periodic.qParam 1 ((u : ℂ) + y * I) ∈ Metric.ball (0 : ℂ) 1 := by
    rw [Metric.mem_ball, dist_zero_right]
    exact Function.Periodic.norm_qParam_lt_one one_pos (by simp [hy])
  exact ContinuousAt.comp (g := xFun)
    (f := fun u : ℝ => Function.Periodic.qParam 1 ((u : ℂ) + y * I)) (x := u)
    ((xFun_analytic _ hmem).continuousAt) hq.continuousAt

theorem circleR_eq (i : Fin 6) : circleR i = Real.exp (-(2 * π * circleY i)) := rfl

/-- **`W_i ≤ Σ_j w_j E(y_i, y_j)`.** -/
theorem energyW_le (i : Fin 6) : energyW i ≤ ∑ j, circleW j * energyE (cy i) (cy j) := by
  set y := circleY i with hydef
  have hy : 0 < y := circleY_pos i
  set qf : ℝ → ℂ := fun u => xFun (Function.Periodic.qParam 1 ((u : ℂ) + y * I)) with hqf
  have hqc : Continuous qf := q_continuous y hy
  have hqne : ∀ u, qf u ≠ 0 := fun u => by
    refine xFun_ne_zero (Function.Periodic.qParam_ne_zero _) ?_
    exact Function.Periodic.norm_qParam_lt_one one_pos (by simp [hy])
  -- the potential as an average over `u`
  rw [← circleAverage_U_x i, circleR_eq, circle_to_unit]
  set g : ℝ → ℝ := fun u => Real.log ‖qf u‖ +
    ∑ j, circleW j * ∑ p ∈ cosetBox y (circleY j), orbitTerm y (circleY j) u p with hg
  have hfint : IntervalIntegrable (fun u => potentialU (qf u)) volume 0 1 :=
    (potentialU_continuous.comp hqc).intervalIntegrable _ _
  have hlogc : Continuous fun u => Real.log ‖qf u‖ :=
    hqc.norm.log fun u => norm_ne_zero_iff.mpr (hqne u)
  have horbc : ∀ j, Continuous fun u => ∑ p ∈ cosetBox y (circleY j), orbitTerm y (circleY j) u p :=
    fun j => continuous_finset_sum _ fun p hp => orbitTerm_continuous hy hp
  have hgc : Continuous g := hlogc.add (continuous_finset_sum _ fun j _ =>
    continuous_const.mul (horbc j))
  have hmono := intervalIntegral.integral_mono_ae_restrict zero_le_one hfint
    (hgc.intervalIntegrable 0 1) (by
      filter_upwards [ae_restrict_of_ae (generic_fiber hy), ae_restrict_mem measurableSet_Icc]
        with u hgen hu
      exact potential_point_le i hu.1 hu.2 hgen.1 hgen.2.1)
  show ∫ u in (0 : ℝ)..1, potentialU (qf u) ≤ _
  refine hmono.trans ?_
  -- evaluate the right-hand side
  simp only [hg]
  have hI1 : IntervalIntegrable (fun u => Real.log ‖qf u‖) volume 0 1 := hlogc.intervalIntegrable 0 1
  have hI2 : IntervalIntegrable (fun u => ∑ j, circleW j * ∑ p ∈ cosetBox y (circleY j),
      orbitTerm y (circleY j) u p) volume 0 1 :=
    (continuous_finset_sum _ fun j _ => continuous_const.mul (horbc j)).intervalIntegrable 0 1
  have hI3 : ∀ j ∈ Finset.univ, IntervalIntegrable (fun u => circleW j * ∑ p ∈ cosetBox y (circleY j),
      orbitTerm y (circleY j) u p) volume 0 1 :=
    fun j _ => (continuous_const.mul (horbc j)).intervalIntegrable 0 1
  rw [intervalIntegral.integral_add hI1 hI2, intervalIntegral.integral_finset_sum hI3]
  have hlog : ∫ u in (0 : ℝ)..1, Real.log ‖qf u‖ = -(2 * π * y) := by
    rw [← log_mean hy, circle_to_unit]
  rw [hlog]
  have horb : ∀ j, ∫ u in (0 : ℝ)..1, circleW j * ∑ p ∈ cosetBox y (circleY j),
      orbitTerm y (circleY j) u p ≤
      circleW j * (2 * π * max 0 (y - circleY j) + ∑ m ∈ mSet (cy i) (cy j), eTerm (cy i) (cy j) m) := by
    intro j
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finset_sum (fun p hp =>
      (orbitTerm_continuous hy hp).intervalIntegrable 0 1)]
    refine mul_le_mul_of_nonneg_left ?_ (circleW_pos j).le
    have h := orbit_integral_le (cy_pos i) (cy_pos j)
    rw [hydef, circleY_eq_cy, circleY_eq_cy]
    exact h
  calc -(2 * π * y) + ∑ j, ∫ u in (0 : ℝ)..1, circleW j * ∑ p ∈ cosetBox y (circleY j),
        orbitTerm y (circleY j) u p
      ≤ -(2 * π * y) + ∑ j, circleW j *
          (2 * π * max 0 (y - circleY j) + ∑ m ∈ mSet (cy i) (cy j), eTerm (cy i) (cy j) m) := by
        gcongr with j; exact horb j
    _ = ∑ j, circleW j * energyE (cy i) (cy j) := by
        have hsum : -(2 * π * y) = ∑ j, circleW j * (-(2 * π * y)) := by
          rw [← Finset.sum_mul, circleW_sum, one_mul]
        rw [hsum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [energyE, Rat.cast_min, ← circleY_eq_cy, ← circleY_eq_cy, ← hydef]
        have : -(2 * π * y) + 2 * π * max 0 (y - circleY j) = -2 * π * min y (circleY j) := by
          rcases le_total y (circleY j) with h | h
          · rw [min_eq_left h, max_eq_left (by linarith)]; ring
          · rw [min_eq_right h, max_eq_right (by linarith)]; ring
        linear_combination circleW j * this

/-- **The actual energy is at most the explicit energy (48).** -/
theorem energyI_le_explicitI : energyI ≤ explicitI := by
  rw [energyI_eq_sum, explicitI]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← circleW_eq_cw, explicitW]
  refine mul_le_mul_of_nonneg_left ?_ (circleW_pos i).le
  refine (energyW_le i).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [circleW_eq_cw]

end Zeta7Valence

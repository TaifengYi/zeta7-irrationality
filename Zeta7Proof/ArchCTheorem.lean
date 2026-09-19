import Zeta7Proof.ArchC30

/-! C: the explicit constant `J` and the actual C theorem.

With the actual energies `W_i = ∫ U dμ_i` and `I = ∫ U dμ` of C1, the boundaries
`b_0 = 0`, `b_i = 7 Σ_{j<i} w_j` (so `b_6 = 7`) and `t_i = log r_i = -2π y_i`, put

`J = Σ_i ((b_{i+1} - b_i) W_i - (b_{i+1}² - b_i²)/2 · t_i)`.

* `energyI_eq_sum`: `I = Σ_i w_i W_i`.
* `circleT_eq`: `t_i = -2π y_i`.
* `bnd_zero`, `bnd_six`, `bnd_succ_sub`: `b_0 = 0`, `b_6 = 7`, `b_{i+1} - b_i = 7 w_i > 0`.
* `integral_phiMin_le_J`: `∫_0^7 min_i (W_i - k t_i) dk ≤ J`.
* `c_theorem` (**C**): for every rational `c` and `ε > 0`, eventually
  `log |D_d| ≤ (J - (7/2) I + ε) d²` for the unchanged determinant. -/
noncomputable section
set_option autoImplicit false
namespace Zeta7Arch
open MeasureTheory Set Real Filter Topology

theorem integrable_U_circle (i : Fin 6) : Integrable potentialU (circleMeasure i) := by
  rw [circleMeasure, integrable_map_measure potentialU_continuous.aestronglyMeasurable
    (circFun_measurable i).aemeasurable]
  refine Integrable.of_bound
    ((potentialU_continuous.measurable.comp (circFun_measurable i)).aestronglyMeasurable)
    (2 * supR + tailBound 0) (Eventually.of_forall fun θ => ?_)
  rw [Real.norm_eq_abs]
  exact potentialU_bounded_on_support _ (circFun_mem_supportSet i θ)

/-- `I = Σ_i w_i W_i`. -/
theorem energyI_eq_sum : energyI = ∑ i, circleW i * energyW i :=
  integral_potentialMeasure integrable_U_circle

/-- `t_i = log r_i = -2π y_i`. -/
theorem circleT_eq (i : Fin 6) : circleT i = -(2 * π * circleY i) := by
  rw [circleT, circleR, Real.log_exp]

/-! ### The boundaries `b_i` -/

/-- `b_n = 7 Σ_{j<n} w_j`. -/
def bnd (n : ℕ) : ℝ := 7 * ∑ j : Fin 6, if (j : ℕ) < n then circleW j else 0

theorem bnd_zero : bnd 0 = 0 := by simp [bnd]

theorem bnd_six : bnd 6 = 7 := by
  have : ∀ j : Fin 6, (if (j : ℕ) < 6 then circleW j else 0) = circleW j := fun j =>
    ite_eq_left_iff.mpr fun h => absurd j.isLt h
  simp only [bnd, this, circleW_sum, mul_one]

theorem bnd_succ_sub (i : Fin 6) : bnd (i + 1) - bnd i = 7 * circleW i := by
  have hterm : ∀ j : Fin 6, (if (j : ℕ) < i + 1 then circleW j else 0) =
      (if (j : ℕ) < i then circleW j else 0) + (if j = i then circleW j else 0) := by
    intro j
    by_cases h1 : (j : ℕ) < i
    · have : j ≠ i := fun h => by rw [h] at h1; exact lt_irrefl _ h1
      simp [h1, Nat.lt_succ_of_lt h1, this]
    · by_cases h2 : j = i
      · subst h2; simp
      · have : ¬ (j : ℕ) < i + 1 := by
          intro h; exact h2 (Fin.ext (by omega))
        simp [h1, h2, this]
  simp only [bnd, hterm, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

theorem bnd_mono (i : Fin 6) : bnd i ≤ bnd (i + 1) := by
  have := bnd_succ_sub i
  have := circleW_pos i
  linarith

/-- `b_i = 7 Σ_{j ≤ i} w_j` in the paper's 1-based indexing: `b_{i+1} = 7 Σ_{j ≤ i} w_j`. -/
theorem bnd_succ_eq (i : Fin 6) :
    bnd (i + 1) = 7 * ∑ j : Fin 6, if j ≤ i then circleW j else 0 := by
  unfold bnd
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  exact propext ⟨fun h => Fin.le_def.mpr (by omega), fun h => by
    have := Fin.le_def.mp h; omega⟩

/-! ### The constant `J` -/

/-- `J = Σ_i ((b_{i+1} - b_i) W_i - (b_{i+1}² - b_i²)/2 · t_i)`. -/
def constJ : ℝ :=
  ∑ i : Fin 6, ((bnd (i + 1) - bnd i) * energyW i - (bnd (i + 1) ^ 2 - bnd i ^ 2) / 2 * circleT i)

/-- The explicit form `J = Σ_i (7 w_i W_i + π (b_{i+1}² - b_i²) y_i)`. -/
theorem constJ_eq : constJ =
    ∑ i : Fin 6, (7 * circleW i * energyW i + π * (bnd (i + 1) ^ 2 - bnd i ^ 2) * circleY i) := by
  unfold constJ
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [bnd_succ_sub, circleT_eq]
  ring

theorem integral_affine (W t a b : ℝ) :
    ∫ k in a..b, (W - k * t) = (b - a) * W - (b ^ 2 - a ^ 2) / 2 * t := by
  rw [intervalIntegral.integral_sub intervalIntegrable_const
    ((by fun_prop : Continuous fun k : ℝ => k * t).intervalIntegrable a b), intervalIntegral.integral_const,
    intervalIntegral.integral_mul_const, integral_id, smul_eq_mul]

/-- **`∫_0^7 min_i (W_i - k t_i) dk ≤ J`.** -/
theorem integral_phiMin_le_J : ∫ k in (0 : ℝ)..7, phiMin k ≤ constJ := by
  have hint : ∀ n < 6, IntervalIntegrable phiMin volume (bnd n) (bnd (n + 1)) :=
    fun n _ => phiMin_continuous.intervalIntegrable _ _
  have hsplit := intervalIntegral.sum_integral_adjacent_intervals hint
  rw [bnd_zero, bnd_six] at hsplit
  rw [← hsplit, Finset.sum_range, constJ]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← integral_affine]
  refine intervalIntegral.integral_mono_on (bnd_mono i) (phiMin_continuous.intervalIntegrable _ _)
    ((by fun_prop : Continuous fun k : ℝ => energyW i - k * circleT i).intervalIntegrable _ _) fun k _ => ?_
  exact Finset.inf'_le (fun j : Fin 6 => energyW j - k * circleT j) (Finset.mem_univ i)

/-- **C**: for every rational `c` and `ε > 0`, eventually
`log |D_d| ≤ (J - (7/2) I + ε) d²` for the unchanged determinant and its actual jump rows. -/
theorem c_theorem (c : ℚ) {ε : ℝ} (hε : 0 < ε) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀,
      Real.log |(Zeta7Common.actualCommonDeterminant d c : ℝ)| ≤
        (constJ - 7 / 2 * energyI + ε) * (d : ℝ) ^ 2 := by
  obtain ⟨d₀, hd₀⟩ := c30 c hε
  refine ⟨d₀, fun d hd => (hd₀ d hd).trans ?_⟩
  exact mul_le_mul_of_nonneg_right (by linarith [integral_phiMin_le_J]) (sq_nonneg _)

end Zeta7Arch

import Zeta7Proof.Radius49FromPublishedGeometry
import Zeta7Proof.Radius49HOChain

/-! **Internal radius-49 continuation.** The geometric continuation statement
`HasRadius49GeometricContinuation` is proved from the two internal inputs
* `twistMatrix_bound` (HM, the Buzzard continuation step for the twisted `U₇` matrix), and
* `initial_HSeries_overconvergent` (HO, Coleman's initial overconvergence at `κ = -2`),
via `hasRadius49_of_matrix_bound_and_initial`. All downstream radius endpoints are derived
from `internal_radius49_geometric_continuation`; no external mathematical axiom is used. -/

set_option autoImplicit false
noncomputable section
namespace Zeta7Main
open PowerSeries Filter Topology Zeta7Radius49
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- **The radius-49 geometric continuation, proved internally.** -/
theorem internal_radius49_geometric_continuation : HasRadius49GeometricContinuation :=
  hasRadius49_of_matrix_bound_and_initial twistMatrix_bound initial_HSeries_overconvergent

/-- Coefficient decay of `HSeries` on every disc of radius `< 49` (internal). -/
theorem HSeries_radius49 :
    ∀ ρ : ℝ, 0 < ρ → ρ < 49 →
      Tendsto (fun n : ℕ => ‖coeff n HSeries‖ * ρ ^ n) atTop (𝓝 0) :=
  HSeries_radius49_of_geometric_continuation internal_radius49_geometric_continuation

/-- Restricted-series membership is a consequence of the completion argument. -/
theorem HSeries_isRestricted (ρ : ℝ) (hρ : 0 < ρ) (hρ49 : ρ < 49) :
    PowerSeries.IsRestricted ρ HSeries :=
  (PowerSeries.isRestricted_iff' _ _).mpr (HSeries_radius49 ρ hρ hρ49)

/-- Every positive closed t-disc of radius below one has Gauss coefficient decay.
This endpoint is derived from the internal radius theorem. -/
theorem normalisedHSeries_radius1 (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    Tendsto (fun n : ℕ => ‖coeff n normalisedHSeries‖ * ρ ^ n) atTop (𝓝 0) :=
  (normalisedHSeries_decay_iff ρ).mpr
    (HSeries_radius49 (49 * ρ) (by positivity) (by nlinarith))

theorem normalisedHSeries_isRestricted (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    PowerSeries.IsRestricted ρ normalisedHSeries :=
  (PowerSeries.isRestricted_iff' _ _).mpr (normalisedHSeries_radius1 ρ hρ hρ1)

/-- Actual convergence at every point of every smaller closed t-disc. -/
theorem normalisedHSeries_summable_on_closedDisc
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ < 1) (t : ℚ_[7]) (ht : ‖t‖ ≤ ρ) :
    Summable (fun n : ℕ => coeff n normalisedHSeries * t ^ n) := by
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  rw [Nat.cofinite_eq_atTop]
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun n => norm_nonneg _)
    (fun n => ?_) (normalisedHSeries_radius1 ρ hρ hρ1)
  rw [norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) ht n) (norm_nonneg _)

/-- Equation (12), with a separate constant B for each positive epsilon.
Zero coefficients are excluded because Padic.valuation uses a finite value at zero.
This endpoint is derived from the internal radius theorem. -/
theorem HSeries_equation12 (ε : ℝ) (hε : 0 < ε) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ, coeff n normalisedHSeries ≠ 0 →
      -ε * (n : ℝ) - B ≤ (Padic.valuation (coeff n normalisedHSeries) : ℝ) := by
  exact restricted_coeff_bound ε
    ⟨normalisedHSeries, normalisedHSeries_isRestricted ((7 : ℝ) ^ (-ε))
    (Real.rpow_pos_of_pos (by norm_num) _)
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos hε))⟩

/-- The norm form of equation (12), valid also at zero coefficients. -/
theorem normalisedHSeries_epsilon_norm_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ,
      ‖coeff n normalisedHSeries‖ ≤ (7 : ℝ) ^ (ε * n + B) := by
  obtain ⟨B, hB, hb⟩ := HSeries_equation12 ε hε
  refine ⟨B, hB, fun n => ?_⟩
  have h := Zeta7Section3.norm_bound_of_valuation
    (coeff n normalisedHSeries) (-ε * n - B) (hb n)
  convert h using 1
  congr 1
  ring

/-- The equivalent unscaled estimate retains the factor 2 from t=49x. -/
theorem HSeries_epsilon_valuation_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ, coeff n HSeries ≠ 0 →
      (2 - ε) * (n : ℝ) - B ≤ (Padic.valuation (coeff n HSeries) : ℝ) := by
  obtain ⟨B, hB, hb⟩ := HSeries_equation12 ε hε
  refine ⟨B, hB, fun n hn => ?_⟩
  have hn' : coeff n normalisedHSeries ≠ 0 := by
    rw [normalisedHSeries_coeff]
    exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero (by norm_num))) hn
  have h := hb n hn'
  have hv := Zeta7Section3.rescale_valuation HSeries n hn
  change (Padic.valuation (coeff n normalisedHSeries) : ℝ) =
    (Padic.valuation (coeff n HSeries) : ℝ) - 2 * n at hv
  rw [hv] at h
  nlinarith

/-- The already proposed scalar Laurent-annulus decay endpoint.
No determinant construction is involved. -/
theorem oppositeH_decaysOn_published : Zeta7Annulus.DecaysOn oppositeH 1 49 :=
  oppositeH_decaysOn_iff.mpr
    (fun r hr1 hr49 => HSeries_radius49 r (by linarith) hr49)

end Zeta7Main

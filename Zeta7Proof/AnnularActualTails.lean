import Zeta7Proof.AnnularSixDecay
import Zeta7Proof.ActualSixGermRadius

/-! Convergence and uniform bounds for the actual omitted source-column tails.
The target bounds here use the internally proved radius-49 decay `Zeta7Main.HSeries_radius49`. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
namespace Zeta7Annulus
open Filter Topology
local instance AnnularActualTails_prime : Fact (Nat.Prime 7) := ⟨by decide⟩

def actualNormalizedTargetCoefficients (j : Fin 6) : LaurentCoefficients :=
  ofPowerSeries (PowerSeries.rescale (49 : ℚ_[7])⁻¹ (Zeta7Common.targetGerms j))

theorem actualNormalizedTargetCoefficients_decay (j : Fin 6) {σ : ℝ}
    (hσ : 0 < σ) (hσ1 : σ < 1) : DecaysAt (actualNormalizedTargetCoefficients j) σ := by
  rw [actualNormalizedTargetCoefficients, ofPowerSeries_decaysAt_iff]
  exact (PowerSeries.isRestricted_iff' _ _).mp (Zeta7Common.normalized_targetGerms_restricted j σ hσ hσ1)

theorem actualNormalizedTargetCoefficients_bound {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (j : Fin 6) (n : ℕ),
      ‖actualNormalizedTargetCoefficients j (n : ℤ)‖ ≤ C * (σ⁻¹) ^ n := by
  classical
  let C : ℝ := ∑ j : Fin 6, bilateralGauss (actualNormalizedTargetCoefficients j) σ
  have hc (j : Fin 6) : 0 ≤ bilateralGauss (actualNormalizedTargetCoefficients j) σ :=
    bilateralGauss_nonneg (actualNormalizedTargetCoefficients_decay j hσ hσ1) hσ
  refine ⟨C, Finset.sum_nonneg (fun j _ => hc j), fun j n => ?_⟩
  have hle : bilateralGauss (actualNormalizedTargetCoefficients j) σ ≤ C :=
    Finset.single_le_sum (fun i _ => hc i) (Finset.mem_univ j)
  have hn := coefficient_norm_le_gauss (actualNormalizedTargetCoefficients_decay j hσ hσ1) hσ (n : ℤ)
  simp only [zpow_neg, zpow_natCast, ← inv_pow] at hn
  exact hn.trans (mul_le_mul_of_nonneg_right hle (by positivity))

def actualAnnularTailTerm (j : Fin 6) (m r l : ℕ) : ℚ_[7] :=
  (7 : ℚ_[7]) ^ 4 * actualAnnularCoefficients j (-((m + l + 1 : ℕ) : ℤ)) *
    actualNormalizedTargetCoefficients j ((r + l + 1 : ℕ) : ℤ)

/-- The exact omitted indices are -m-l and r+l, with l starting at one. -/
def actualAnnularTail (m r : ℕ) : ℚ_[7] :=
  ∑ j : Fin 6, ∑' l : ℕ, actualAnnularTailTerm j m r l

theorem padic_geometric_summable_bound {f : ℕ → ℚ_[7]} {C a : ℝ}
    (hC : 0 ≤ C) (ha : 0 ≤ a) (ha1 : a < 1) (hf : ∀ n, ‖f n‖ ≤ C * a ^ n) :
    Summable f ∧ ‖∑' n, f n‖ ≤ C := by
  have ht : Tendsto (fun n : ℕ => ‖f n‖) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => norm_nonneg _) hf
    simpa only [mul_zero] using (tendsto_pow_atTop_nhds_zero_of_lt_one ha ha1).const_mul C
  have hs : Summable f := NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero (by
    rw [tendsto_zero_iff_norm_tendsto_zero, Nat.cofinite_eq_atTop]
    exact ht)
  refine ⟨hs, norm_tsum_le_uniform hs hC (fun n => (hf n).trans ?_)⟩
  exact (mul_le_mul_of_nonneg_left (pow_le_one₀ ha ha1.le) hC).trans (by rw [mul_one])

/-- Both radii and the uniform constant precede every source degree and row.
No relation identity or vanishing coefficient is assumed in this estimate. -/
theorem actualAnnularTail_bound {ρ σ : ℝ}
    (hρ : (1 / 49 : ℝ) < ρ) (hρσ : ρ < σ) (hσ1 : σ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (m r : ℕ),
      (∀ j : Fin 6, Summable (actualAnnularTailTerm j m r)) ∧
      ‖actualAnnularTail m r‖ ≤ C * ρ ^ m * (σ⁻¹) ^ r := by
  have hρ0 : 0 < ρ := lt_trans (by norm_num) hρ
  have hσ0 : 0 < σ := hρ0.trans hρσ
  obtain ⟨A, hA, hAb⟩ := actualAnnularCoefficients_negative_bound hρ
  obtain ⟨B, hB, hBb⟩ := actualNormalizedTargetCoefficients_bound hσ0 hσ1
  have ha : 0 ≤ ρ * σ⁻¹ := by positivity
  have ha1 : ρ * σ⁻¹ < 1 := by rw [← div_eq_mul_inv]; exact (div_lt_one hσ0).mpr hρσ
  have hscale : ‖(7 : ℚ_[7]) ^ 4‖ ≤ 1 := by
    exact (norm_pow_le _ _).trans (pow_le_one₀ (norm_nonneg _)
      (by simpa using Padic.norm_int_le_one (p := 7) 7))
  refine ⟨A * B, mul_nonneg hA hB, fun m r => ?_⟩
  let C : ℝ := A * B * ρ ^ m * (σ⁻¹) ^ r
  have hC : 0 ≤ C := by positivity
  have hterm (j : Fin 6) (l : ℕ) : ‖actualAnnularTailTerm j m r l‖ ≤ C * (ρ * σ⁻¹) ^ l := by
    have hh := padic_mul_bound (padic_mul_bound hscale (hAb j (m + l + 1))) (hBb j (r + l + 1))
    have he : (1 * (A * ρ ^ (m + l + 1))) * (B * (σ⁻¹) ^ (r + l + 1)) =
        C * (ρ * σ⁻¹) ^ (l + 1) := by
      dsimp [C]
      simp only [pow_add, pow_one, mul_pow]
      ring
    change ‖actualAnnularTailTerm j m r l‖ ≤ _ at hh
    rw [he] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (by
      rw [pow_succ]
      exact (mul_le_mul_of_nonneg_left ha1.le (pow_nonneg ha l)).trans (by rw [mul_one])) hC)
  have hs (j : Fin 6) := padic_geometric_summable_bound hC ha ha1 (hterm j)
  refine ⟨fun j => (hs j).1, ?_⟩
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hC (fun j _ => (hs j).2)

end Zeta7Annulus

import Zeta7Proof.ClosedAnnulusRing
import Mathlib.Topology.MetricSpace.Cauchy

/-! Completeness of the bilateral coefficient ring in the endpoint Gauss norm.
The limit is constructed coefficient by coefficient, then uniform weighted
estimates prove decay of both tails and convergence in the annulus norm. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
open Filter Topology
namespace Zeta7Annulus
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

theorem decaysAt_of_uniform_approximation (a : LaurentCoefficients) {ρ : ℝ} (hρ : 0 < ρ)
    (h : ∀ ε : ℝ, 0 < ε → ∃ b : LaurentCoefficients, DecaysAt b ρ ∧
      ∀ k, weightedCoefficient (a - b) ρ k ≤ ε) : DecaysAt a ρ := by
  rw [decaysAt_iff_cofinite, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨b, hb, hab⟩ := h (ε / 2) (by linarith)
  have he := ((decaysAt_iff_cofinite b ρ).mp hb).eventually
    (gt_mem_nhds (by linarith : (0 : ℝ) < ε / 2))
  filter_upwards [he] with k hk
  rw [dist_zero_right, Real.norm_of_nonneg (weightedCoefficient_nonneg a hρ k)]
  have ht : weightedCoefficient a ρ k ≤
      max (weightedCoefficient (a - b) ρ k) (weightedCoefficient b ρ k) := by
    have hh := IsUltrametricDist.norm_add_le_max (a k - b k) (b k)
    rw [sub_add_cancel] at hh
    exact (mul_le_mul_of_nonneg_right hh (zpow_pos hρ k).le).trans_eq
      (max_mul_of_nonneg _ _ (zpow_pos hρ k).le)
  exact ht.trans_lt (max_lt ((hab k).trans_lt (by linarith)) (hk.trans (by linarith)))

namespace ClosedAnnulus
variable {r R : ℝ} [Fact (0 < r)] [Fact (0 < R)]

theorem cauchySeq_coeffs {u : ℕ → ClosedAnnulus r R} (hu : CauchySeq u) (k : ℤ) :
    CauchySeq (fun n => (u n).coeffs k) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  have hp : 0 < r ^ (-k) := zpow_pos Fact.out _
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hu (ε / r ^ (-k)) (div_pos hε hp)
  refine ⟨N, fun m hm n hn => ?_⟩
  rw [dist_eq_norm]
  calc
    _ ≤ ‖u m - u n‖ * r ^ (-k) := by
      simpa only [coeffs_sub, Pi.sub_apply] using (u m - u n).coeff_norm_le k
    _ < (ε / r ^ (-k)) * r ^ (-k) := mul_lt_mul_of_pos_right
      (by simpa only [dist_eq_norm] using hN m hm n hn) hp
    _ = ε := div_mul_cancel₀ _ hp.ne'

theorem cauchySeq_uniform_limit_bound {u : ℕ → ClosedAnnulus r R}
    (hu : CauchySeq u) {a : LaurentCoefficients}
    (ha : ∀ k, Tendsto (fun n => (u n).coeffs k) atTop (𝓝 (a k)))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n, N ≤ n → ∀ k : ℤ,
      weightedCoefficient ((u n).coeffs - a) r k ≤ ε ∧
      weightedCoefficient ((u n).coeffs - a) R k ≤ ε := by
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hu ε hε
  refine ⟨N, fun n hn k => ?_⟩
  have step (ρ : ℝ)
      (hb : ∀ m, weightedCoefficient (u n - u m).coeffs ρ k ≤ ‖u n - u m‖) :
      weightedCoefficient ((u n).coeffs - a) ρ k ≤ ε := by
    have ht : Tendsto (fun m => ‖(u n).coeffs k - (u m).coeffs k‖ * ρ ^ k)
        atTop (𝓝 (weightedCoefficient ((u n).coeffs - a) ρ k)) :=
      ((tendsto_const_nhds.sub (ha k)).norm).mul_const (ρ ^ k)
    apply le_of_tendsto ht
    filter_upwards [eventually_ge_atTop N] with m hm
    simpa only [weightedCoefficient, coeffs_sub, Pi.sub_apply] using
      (hb m).trans (by simpa only [dist_eq_norm] using (hN n hn m hm).le)
  exact ⟨step r (fun m => (weightedCoefficient_le_gauss (u n - u m).inner k).trans
      (le_max_left _ _)),
    step R (fun m => (weightedCoefficient_le_gauss (u n - u m).outer k).trans
      (le_max_right _ _))⟩

theorem cauchySeq_has_limit {u : ℕ → ClosedAnnulus r R} (hu : CauchySeq u) :
    ∃ a : ClosedAnnulus r R, Tendsto u atTop (𝓝 a) := by
  have hc (k : ℤ) := cauchySeq_tendsto_of_complete (cauchySeq_coeffs hu k)
  choose a ha using hc
  have hd (ρ : ℝ) (hρ : 0 < ρ)
      (hdecay : ∀ n, DecaysAt (u n).coeffs ρ)
      (hbound : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ k,
        weightedCoefficient ((u N).coeffs - a) ρ k ≤ ε) : DecaysAt a ρ := by
    apply decaysAt_of_uniform_approximation a hρ
    intro ε hε
    obtain ⟨N, hN⟩ := hbound ε hε
    refine ⟨(u N).coeffs, hdecay N, fun k => ?_⟩
    simpa only [weightedCoefficient, Pi.sub_apply, norm_sub_rev] using hN k
  have hir : DecaysAt a r := hd r Fact.out (fun n => (u n).inner) (by
    intro ε hε
    obtain ⟨N, hN⟩ := cauchySeq_uniform_limit_bound hu ha ε hε
    exact ⟨N, fun k => (hN N le_rfl k).1⟩)
  have hiR : DecaysAt a R := hd R Fact.out (fun n => (u n).outer) (by
    intro ε hε
    obtain ⟨N, hN⟩ := cauchySeq_uniform_limit_bound hu ha ε hε
    exact ⟨N, fun k => (hN N le_rfl k).2⟩)
  let A : ClosedAnnulus r R := ⟨a, hir, hiR⟩
  refine ⟨A, ?_⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := cauchySeq_uniform_limit_bound hu ha (ε / 2) (by linarith)
  refine ⟨N, fun n hn => ?_⟩
  rw [dist_eq_norm]
  have hb : ‖u n - A‖ ≤ ε / 2 := by
    simp only [norm_eq, closedAnnulusGauss, coeffs_sub]
    exact max_le
      (bilateralGauss_le (fun k => (hN n hn k).1))
      (bilateralGauss_le (fun k => (hN n hn k).2))
  exact hb.trans_lt (by linarith)

instance : CompleteSpace (ClosedAnnulus r R) :=
  Metric.complete_of_cauchySeq_tendsto (fun _ h => cauchySeq_has_limit h)

end ClosedAnnulus
end Zeta7Annulus

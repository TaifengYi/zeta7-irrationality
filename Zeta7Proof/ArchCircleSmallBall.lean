import Zeta7Proof.ArchCircleAnalytic

/-! C1, step 3: the uniform small-ball estimate for one circle, in the angle variable.

At every angle `θ₀` a fixed derivative of order `k ≥ 1` of the real or imaginary part of
`θ ↦ x(r e^{iθ})` is bounded below on a closed interval around `θ₀` (continuity of the derivative).
On such an interval the sublevel-set bound of `ArchSublevel` applies to `φ(x(r e^{iθ})) - φ(z)`,
uniformly in the centre `z`, because the shift by `φ(z)` does not change derivatives of positive
order. A finite subcover of `[0, 2π]` gives

`volume {θ ∈ [0, 2π] : |x(r e^{iθ}) - z| < ρ} ≤ C ρ^α`   for all `z ∈ ℂ` and `0 < ρ ≤ 1`,

with `α = 1/K`, `K` the largest of the finitely many local orders. Overlaps of the local arcs only
enlarge the sum; endpoints are covered because the cover uses open intervals around every point of
the closed interval `[0, 2π]` while the estimates use the closed intervals. -/
noncomputable section
set_option autoImplicit false
namespace Zeta7Arch
open MeasureTheory Set Filter Topology

theorem clm_comp_circFun_contDiff {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (φ : ℂ →L[ℝ] ℝ) :
    ContDiff ℝ ⊤ (fun θ => φ (circFun r θ)) :=
  φ.contDiff.comp (circFun_contDiff hr0 hr1)

/-- Local data at one angle: an interval, an order, a lower bound and a component. -/
theorem arc_local_data {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (θ₀ : ℝ) :
    ∃ δ > 0, ∃ k : ℕ, 1 ≤ k ∧ ∃ c > 0, ∃ φ : ℂ →L[ℝ] ℝ, (∀ w, |φ w| ≤ ‖w‖) ∧
      ∀ θ ∈ Icc (θ₀ - δ) (θ₀ + δ), c ≤ |iteratedDeriv k (fun θ => φ (circFun r θ)) θ| := by
  obtain ⟨k, hk, φ, hφ, hne⟩ := circFun_component_not_flat hr0 hr1 θ₀
  set D := iteratedDeriv k (fun θ => φ (circFun r θ)) with hD
  have hDc : Continuous D :=
    (clm_comp_circFun_contDiff hr0.le hr1 φ).continuous_iteratedDeriv k le_top
  have hpos : 0 < |D θ₀| := abs_pos.mpr hne
  have hev : ∀ᶠ θ in 𝓝 θ₀, |D θ₀| / 2 < |D θ| :=
    hDc.abs.continuousAt.eventually (lt_mem_nhds (half_lt_self hpos))
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨ε / 2, by positivity, k, hk, |D θ₀| / 2, by positivity, φ, hφ, fun θ hθ => ?_⟩
  refine (hball ?_).le
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith [hθ.1, hθ.2]

/-- The local measure bound on one closed interval, uniform in the centre. -/
theorem arc_local_measure {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) {a b c : ℝ} {k : ℕ} (hk : 1 ≤ k)
    (hc : 0 < c) {φ : ℂ →L[ℝ] ℝ} (hφ : ∀ w, |φ w| ≤ ‖w‖)
    (hd : ∀ θ ∈ Icc a b, c ≤ |iteratedDeriv k (fun θ => φ (circFun r θ)) θ|)
    (z : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    volume {θ ∈ Icc a b | ‖circFun r θ - z‖ < ρ} ≤
      ENNReal.ofReal (subConst k * (ρ / c) ^ ((k : ℝ)⁻¹)) := by
  have hsm := clm_comp_circFun_contDiff hr0.le hr1 φ
  have hu : ∀ j, Differentiable ℝ (iteratedDeriv j (fun θ => φ (circFun r θ) - φ z)) :=
    differentiable_iteratedDeriv_of_contDiff (hsm.sub contDiff_const)
  have hdu : ∀ θ ∈ Icc a b, c ≤ |iteratedDeriv k (fun θ => φ (circFun r θ) - φ z) θ| := by
    intro θ hθ
    rw [iteratedDeriv_sub_const (g := fun θ => φ (circFun r θ)) _ k hk]
    exact hd θ hθ
  refine le_trans (measure_mono ?_) (sublevel_volume_le k hk hu hc hρ hdu)
  rintro θ ⟨hθI, hθ⟩
  refine ⟨hθI, ?_⟩
  have h : φ (circFun r θ) - φ z = φ (circFun r θ - z) := (map_sub φ _ _).symm
  rw [h]
  exact (hφ _).trans hθ.le

/-- **Uniform small-ball estimate for one circle** (angle form). -/
theorem arc_small_ball {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    ∃ C α : ℝ, 0 ≤ C ∧ 0 < α ∧ ∀ (z : ℂ) (ρ : ℝ), 0 < ρ → ρ ≤ 1 →
      volume {θ ∈ Icc (0 : ℝ) (2 * Real.pi) | ‖circFun r θ - z‖ < ρ} ≤
        ENNReal.ofReal (C * ρ ^ α) := by
  choose δ hδ k hk c hc φ hφ hd using arc_local_data hr0 hr1
  obtain ⟨t, ht⟩ := isCompact_Icc.elim_finite_subcover
    (fun θ₀ : ℝ => Ioo (θ₀ - δ θ₀) (θ₀ + δ θ₀)) (fun _ => isOpen_Ioo)
    (fun θ _ => mem_iUnion.mpr ⟨θ, by constructor <;> linarith [hδ θ]⟩)
  set K : ℕ := max 1 (t.sup k) with hK
  have hK1 : 1 ≤ K := le_max_left _ _
  have hkK : ∀ j ∈ t, k j ≤ K := fun j hj => le_trans (Finset.le_sup hj) (le_max_right _ _)
  set α : ℝ := (K : ℝ)⁻¹ with hα
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK1
  have hα0 : 0 < α := by rw [hα]; positivity
  set C : ℝ := ∑ j ∈ t, subConst (k j) / (c j) ^ ((k j : ℝ)⁻¹) with hC
  have hterm0 : ∀ j, 0 ≤ subConst (k j) / (c j) ^ ((k j : ℝ)⁻¹) := fun j =>
    div_nonneg (subConst_pos _).le (Real.rpow_nonneg (hc j).le _)
  refine ⟨C, α, Finset.sum_nonneg fun j _ => hterm0 j, hα0, fun z ρ hρ hρ1 => ?_⟩
  have hsub : {θ ∈ Icc (0 : ℝ) (2 * Real.pi) | ‖circFun r θ - z‖ < ρ} ⊆
      ⋃ j ∈ t, {θ ∈ Icc (j - δ j) (j + δ j) | ‖circFun r θ - z‖ < ρ} := by
    rintro θ ⟨hθI, hθ⟩
    obtain ⟨j, hj, hθj⟩ := mem_iUnion₂.mp (ht hθI)
    exact mem_iUnion₂.mpr ⟨j, hj, ⟨Ioo_subset_Icc_self hθj, hθ⟩⟩
  have hpiece : ∀ j ∈ t, subConst (k j) * (ρ / c j) ^ ((k j : ℝ)⁻¹) ≤
      subConst (k j) / (c j) ^ ((k j : ℝ)⁻¹) * ρ ^ α := by
    intro j hj
    have hkj : (1 : ℝ) ≤ k j := by exact_mod_cast hk j
    have hexp : α ≤ ((k j : ℝ))⁻¹ := by
      rw [hα]
      exact inv_anti₀ (by linarith) (by exact_mod_cast hkK j hj)
    have hρpow : ρ ^ ((k j : ℝ)⁻¹) ≤ ρ ^ α :=
      Real.rpow_le_rpow_of_exponent_ge hρ hρ1 hexp
    have hcpos : 0 < (c j) ^ ((k j : ℝ)⁻¹) := Real.rpow_pos_of_pos (hc j) _
    rw [Real.div_rpow hρ.le (hc j).le]
    have hS := subConst_pos (k j)
    calc subConst (k j) * (ρ ^ ((k j : ℝ)⁻¹) / (c j) ^ ((k j : ℝ)⁻¹))
        = subConst (k j) / (c j) ^ ((k j : ℝ)⁻¹) * ρ ^ ((k j : ℝ)⁻¹) := by ring
      _ ≤ subConst (k j) / (c j) ^ ((k j : ℝ)⁻¹) * ρ ^ α :=
          mul_le_mul_of_nonneg_left hρpow (hterm0 j)
  calc volume {θ ∈ Icc (0 : ℝ) (2 * Real.pi) | ‖circFun r θ - z‖ < ρ}
      ≤ volume (⋃ j ∈ t, {θ ∈ Icc (j - δ j) (j + δ j) | ‖circFun r θ - z‖ < ρ}) :=
        measure_mono hsub
    _ ≤ ∑ j ∈ t, volume {θ ∈ Icc (j - δ j) (j + δ j) | ‖circFun r θ - z‖ < ρ} :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ j ∈ t, ENNReal.ofReal (subConst (k j) * (ρ / c j) ^ ((k j : ℝ)⁻¹)) :=
        Finset.sum_le_sum fun j _ =>
          arc_local_measure hr0 hr1 (hk j) (hc j) (hφ j) (hd j) z hρ
    _ ≤ ∑ j ∈ t, ENNReal.ofReal (subConst (k j) / (c j) ^ ((k j : ℝ)⁻¹) * ρ ^ α) :=
        Finset.sum_le_sum fun j hj => ENNReal.ofReal_le_ofReal (hpiece j hj)
    _ = ENNReal.ofReal (C * ρ ^ α) := by
        rw [hC, Finset.sum_mul, ENNReal.ofReal_sum_of_nonneg]
        intro j _
        exact mul_nonneg (hterm0 j) (Real.rpow_nonneg hρ.le _)

end Zeta7Arch

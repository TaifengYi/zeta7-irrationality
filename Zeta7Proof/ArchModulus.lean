import Zeta7Proof.ArchPotential

/-! C2, step 1: the fixed compact disc `𝒦` and the modulus of continuity of `U` on it.

`discK = closedBall 0 (R + 1)`, where `R` bounds the support of `μ`; it contains every closed disc
of radius `h ≤ 1` centred at a point of the support. `omegaU h` is the supremum of
`|U(z) - U(z')|` over `z, z' ∈ 𝒦` with `|z - z'| ≤ h`; it is finite because `U` is bounded on the
compact `𝒦`, and `omegaU h → 0` as `h → 0⁺` by uniform continuity of `U` on `𝒦`. -/
noncomputable section
set_option autoImplicit false
namespace Zeta7Arch
open MeasureTheory Set Real Filter Topology

/-- The fixed closed disc `𝒦`. -/
def discK : Set ℂ := Metric.closedBall 0 (supR + 1)

theorem isCompact_discK : IsCompact discK := isCompact_closedBall _ _

theorem supportSet_subset_discK : supportSet ⊆ discK := fun w hw => by
  rw [discK, Metric.mem_closedBall, dist_zero_right]
  linarith [norm_le_supR hw]

theorem closedBall_subset_discK {z : ℂ} (hz : z ∈ supportSet) {h : ℝ} (h1 : h ≤ 1) :
    Metric.closedBall z h ⊆ discK := fun w hw => by
  rw [discK, Metric.mem_closedBall, dist_zero_right]
  rw [Metric.mem_closedBall, dist_eq_norm] at hw
  have h2 := norm_le_supR hz
  have h3 := norm_le_norm_add_norm_sub' w z
  linarith

theorem exists_bound_U_discK : ∃ B : ℝ, ∀ z ∈ discK, |potentialU z| ≤ B := by
  obtain ⟨B, hB⟩ := isCompact_discK.exists_bound_of_continuousOn
    potentialU_continuous.continuousOn
  exact ⟨B, fun z hz => by simpa [Real.norm_eq_abs] using hB z hz⟩

/-- The set of oscillations of `U` at scale `h` on `𝒦`. -/
def oscSet (h : ℝ) : Set ℝ :=
  {e | ∃ z ∈ discK, ∃ z' ∈ discK, dist z z' ≤ h ∧ e = |potentialU z - potentialU z'|}

theorem oscSet_bddAbove (h : ℝ) : BddAbove (oscSet h) := by
  obtain ⟨B, hB⟩ := exists_bound_U_discK
  refine ⟨2 * B, ?_⟩
  rintro e ⟨z, hz, z', hz', _, rfl⟩
  have h1 := hB z hz
  have h2 := hB z' hz'
  have := abs_sub (potentialU z) (potentialU z')
  linarith

theorem zero_mem_oscSet {h : ℝ} (hh : 0 ≤ h) : (0 : ℝ) ∈ oscSet h := by
  have h0 : (0 : ℂ) ∈ discK := by
    rw [discK, Metric.mem_closedBall, dist_self]
    linarith [supR_nonneg]
  exact ⟨0, h0, 0, h0, by simpa using hh, by simp⟩

/-- **The modulus of continuity `ω(h)` of `U` on `𝒦`.** -/
def omegaU (h : ℝ) : ℝ := sSup (oscSet h)

theorem omegaU_nonneg {h : ℝ} (hh : 0 ≤ h) : 0 ≤ omegaU h :=
  le_csSup (oscSet_bddAbove h) (zero_mem_oscSet hh)

theorem abs_sub_le_omegaU {h : ℝ} {z z' : ℂ} (hz : z ∈ discK) (hz' : z' ∈ discK)
    (hd : dist z z' ≤ h) : |potentialU z - potentialU z'| ≤ omegaU h :=
  le_csSup (oscSet_bddAbove h) ⟨z, hz, z', hz', hd, rfl⟩

/-- **`ω(h) → 0`.** -/
theorem omegaU_tendsto : Tendsto omegaU (𝓝[>] 0) (𝓝 0) := by
  have huc := isCompact_discK.uniformContinuousOn_of_continuous potentialU_continuous.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hball⟩ := huc (ε / 2) (by positivity)
  refine ⟨δ, hδ, fun h hh hhδ => ?_⟩
  have hh0 : 0 < h := hh
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (omegaU_nonneg hh0.le)]
  have hhd : h < δ := by rw [Real.dist_eq, sub_zero, abs_of_pos hh0] at hhδ; exact hhδ
  refine lt_of_le_of_lt (csSup_le ⟨0, zero_mem_oscSet hh0.le⟩ ?_) (half_lt_self hε)
  rintro e ⟨z, hz, z', hz', hd, rfl⟩
  have := hball z hz z' hz' (lt_of_le_of_lt hd hhd)
  rw [Real.dist_eq] at this
  exact this.le

/-- On a small disc around a support point, `U ≤ U(z) + ω(h)`. -/
theorem potentialU_le_add_omega {z : ℂ} (hz : z ∈ supportSet) {h : ℝ} (h1 : h ≤ 1)
    {w : ℂ} (hw : w ∈ Metric.closedBall z h) : potentialU w ≤ potentialU z + omegaU h := by
  have hzK := supportSet_subset_discK hz
  have hwK := closedBall_subset_discK hz h1 hw
  have hd : dist w z ≤ h := hw
  have := abs_sub_le_omegaU hwK hzK hd
  have := le_abs_self (potentialU w - potentialU z)
  linarith

end Zeta7Arch

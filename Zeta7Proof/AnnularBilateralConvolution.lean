import Zeta7Proof.AnnulusCoefficients
import Zeta7Proof.SevenAdicSeriesEvaluation
import Mathlib.Topology.Instances.Int

/-! Genuine infinite bilateral convolution, on the existing coefficient model.
All sums used below have summability proofs. No lower support bound is imposed. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
open Filter Topology
namespace Zeta7Annulus
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

def weightedCoefficient (a : LaurentCoefficients) (ρ : ℝ) (k : ℤ) : ℝ := ‖a k‖ * ρ ^ k

theorem decaysAt_iff_cofinite (a : LaurentCoefficients) (ρ : ℝ) :
    DecaysAt a ρ ↔ Tendsto (weightedCoefficient a ρ) cofinite (𝓝 0) := by
  constructor
  · intro ha
    rw [Int.cofinite_eq, tendsto_sup]
    have hp : Tendsto (weightedCoefficient a ρ) atTop (𝓝 0) := by
      rw [← Nat.map_cast_int_atTop, tendsto_map'_iff]
      simpa only [Function.comp_def, weightedCoefficient, zpow_natCast] using ha.1
    have hn : Tendsto (fun k : ℤ => weightedCoefficient a ρ (-k)) atTop (𝓝 0) := by
      rw [← Nat.map_cast_int_atTop, tendsto_map'_iff]
      simpa only [Function.comp_def, weightedCoefficient, zpow_neg, zpow_natCast,
        inv_pow] using ha.2
    refine ⟨?_, hp⟩
    simpa only [Function.comp_def, neg_neg] using hn.comp tendsto_neg_atBot_atTop
  · intro ha
    constructor
    · have hi : Function.Injective (fun n : ℕ => (n : ℤ)) := by
        intro x y h; dsimp at h; exact_mod_cast h
      have h := ha.comp hi.tendsto_cofinite
      simpa only [Nat.cofinite_eq_atTop, Function.comp_def, weightedCoefficient,
        zpow_natCast] using h
    · have hi : Function.Injective (fun n : ℕ => -(n : ℤ)) := by
        intro x y h; exact_mod_cast neg_injective h
      have h := ha.comp hi.tendsto_cofinite
      simpa only [Nat.cofinite_eq_atTop, Function.comp_def, weightedCoefficient,
        zpow_neg, zpow_natCast, inv_pow] using h

theorem weightedCoefficient_nonneg (a : LaurentCoefficients) {ρ : ℝ} (hρ : 0 < ρ) (k : ℤ) :
    0 ≤ weightedCoefficient a ρ k := mul_nonneg (norm_nonneg _) (zpow_pos hρ _).le

theorem DecaysAt.weighted_bounded {a : LaurentCoefficients} {ρ : ℝ} (ha : DecaysAt a ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℤ, weightedCoefficient a ρ k ≤ C := by
  obtain ⟨C, hC⟩ := ((decaysAt_iff_cofinite a ρ).mp ha).isBoundedUnder_le.bddAbove_range_of_cofinite
  exact ⟨max C 0, le_max_right _ _, fun k =>
    (hC (Set.mem_range_self k)).trans (le_max_left _ _)⟩

theorem weighted_mul_identity (a b : LaurentCoefficients) {ρ : ℝ} (hρ : 0 < ρ) (k i : ℤ) :
    ‖a i * b (k - i)‖ =
      (weightedCoefficient a ρ i * weightedCoefficient b ρ (k - i)) * ρ ^ (-k) := by
  simp only [weightedCoefficient, norm_mul]
  have hp : ρ ^ i * ρ ^ (k - i) * ρ ^ (-k) = 1 := by
    rw [← zpow_add₀ hρ.ne', ← zpow_add₀ hρ.ne']
    simp
  linear_combination -(‖a i‖ * ‖b (k - i)‖) * hp

theorem DecaysAt.convolution_summable {a b : LaurentCoefficients} {ρ : ℝ}
    (hρ : 0 < ρ) (ha : DecaysAt a ρ) (hb : DecaysAt b ρ) (k : ℤ) :
    Summable (fun i : ℤ => a i * b (k - i)) := by
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp_rw [weighted_mul_identity a b hρ k]
  have hi : Function.Injective (fun i : ℤ => k - i) := by
    intro x y h; exact sub_right_injective h
  have h := ((decaysAt_iff_cofinite a ρ).mp ha).mul
    (((decaysAt_iff_cofinite b ρ).mp hb).comp hi.tendsto_cofinite)
  simpa only [Function.comp_def, zero_mul] using h.mul_const (ρ ^ (-k))

def bilateralConvolution (a b : LaurentCoefficients) : LaurentCoefficients :=
  fun k => ∑' i : ℤ, a i * b (k - i)

theorem bilateralConvolution_comm (a b : LaurentCoefficients) :
    bilateralConvolution a b = bilateralConvolution b a := by
  ext k
  let e : ℤ ≃ ℤ := Equiv.subLeft k
  rw [bilateralConvolution, bilateralConvolution, ← e.tsum_eq]
  apply tsum_congr
  intro i
  simp [e, mul_comm]

theorem norm_tsum_le_uniform {ι : Type*} {f : ι → ℚ_[7]} (hf : Summable f)
    {C : ℝ} (hC : 0 ≤ C) (h : ∀ i, ‖f i‖ ≤ C) : ‖∑' i, f i‖ ≤ C := by
  apply le_of_tendsto hf.hasSum.norm
  exact Eventually.of_forall (fun s =>
    IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hC (fun i _ => h i))

theorem bilateralConvolution_weighted_bound {a b : LaurentCoefficients} {ρ A B : ℝ}
    (hρ : 0 < ρ) (ha : DecaysAt a ρ) (hb : DecaysAt b ρ)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hba : ∀ i, weightedCoefficient a ρ i ≤ A)
    (hbb : ∀ i, weightedCoefficient b ρ i ≤ B) (k : ℤ) :
    weightedCoefficient (bilateralConvolution a b) ρ k ≤ A * B := by
  have h := norm_tsum_le_uniform (C := A * B * ρ ^ (-k)) (ha.convolution_summable hρ hb k)
    (mul_nonneg (mul_nonneg hA hB) (zpow_pos hρ _).le) (fun i => ?_)
  · change ‖bilateralConvolution a b k‖ ≤ (A * B) * ρ ^ (-k) at h
    rw [weightedCoefficient]
    calc
      _ ≤ (A * B) * ρ ^ (-k) * ρ ^ k := mul_le_mul_of_nonneg_right h (zpow_pos hρ _).le
      _ = _ := by rw [mul_assoc, ← zpow_add₀ hρ.ne']; simp
  · rw [weighted_mul_identity a b hρ k]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul (hba i) (hbb _) (weightedCoefficient_nonneg b hρ _) hA) (zpow_pos hρ _).le

end Zeta7Annulus

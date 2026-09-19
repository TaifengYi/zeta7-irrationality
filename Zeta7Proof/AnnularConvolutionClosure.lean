import Zeta7Proof.AnnularBilateralConvolution

/-! Closure and associativity of the actual bilateral convolution.
The double-sum exchange is justified by a jointly summable family. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
open Filter Topology
namespace Zeta7Annulus
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

theorem bilateralConvolution_weighted_le {a b : LaurentCoefficients} {ρ C : ℝ}
    (hρ : 0 < ρ) (ha : DecaysAt a ρ) (hb : DecaysAt b ρ) (hC : 0 ≤ C) (k : ℤ)
    (h : ∀ i, weightedCoefficient a ρ i * weightedCoefficient b ρ (k - i) ≤ C) :
    weightedCoefficient (bilateralConvolution a b) ρ k ≤ C := by
  have ht : ‖bilateralConvolution a b k‖ ≤ C * ρ ^ (-k) := by
    apply norm_tsum_le_uniform (ha.convolution_summable hρ hb k)
      (mul_nonneg hC (zpow_pos hρ _).le)
    intro i
    rw [weighted_mul_identity a b hρ k]
    exact mul_le_mul_of_nonneg_right (h i) (zpow_pos hρ _).le
  rw [weightedCoefficient]
  calc
    _ ≤ C * ρ ^ (-k) * ρ ^ k := mul_le_mul_of_nonneg_right ht (zpow_pos hρ _).le
    _ = C := by rw [mul_assoc, ← zpow_add₀ hρ.ne']; simp

theorem DecaysAt.bilateralConvolution {a b : LaurentCoefficients} {ρ : ℝ}
    (ha : DecaysAt a ρ) (hb : DecaysAt b ρ) (hρ : 0 < ρ) :
    DecaysAt (bilateralConvolution a b) ρ := by
  rw [decaysAt_iff_cofinite, Metric.tendsto_nhds]
  intro ε hε
  have hp := tendsto_mul_cofinite_nhds_zero
    ((decaysAt_iff_cofinite a ρ).mp ha) ((decaysAt_iff_cofinite b ρ).mp hb)
  have hs : Set.Finite {p : ℤ × ℤ |
      ε / 2 ≤ weightedCoefficient a ρ p.1 * weightedCoefficient b ρ p.2} := by
    simpa only [not_lt] using (Filter.eventually_cofinite.mp
      (hp.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < ε / 2))))
  filter_upwards [(hs.image (fun p : ℤ × ℤ => p.1 + p.2)).compl_mem_cofinite] with k hk
  have hc : weightedCoefficient (Zeta7Annulus.bilateralConvolution a b) ρ k ≤ ε / 2 := by
    apply bilateralConvolution_weighted_le hρ ha hb (by linarith) k
    intro i
    apply le_of_lt
    by_contra hn
    apply hk
    refine ⟨(i, k - i), not_lt.mp hn, ?_⟩
    dsimp
    omega
  rw [dist_zero_right, Real.norm_of_nonneg (weightedCoefficient_nonneg _ hρ _)]
  linarith

theorem DecaysOn.bilateralConvolution {a b : LaurentCoefficients} {r R : ℝ}
    (ha : DecaysOn a r R) (hb : DecaysOn b r R) (hr : 0 ≤ r) :
    DecaysOn (bilateralConvolution a b) r R := by
  intro ρ hρ hR
  exact (ha ρ hρ hR).bilateralConvolution (hb ρ hρ hR) (hr.trans_lt hρ)

theorem DecaysAt.triple_slice_summable {a b c : LaurentCoefficients} {ρ : ℝ}
    (ha : DecaysAt a ρ) (hb : DecaysAt b ρ) (hc : DecaysAt c ρ)
    (hρ : 0 < ρ) (k : ℤ) :
    Summable (fun p : ℤ × ℤ => a p.1 * b p.2 * c (k - p.1 - p.2)) := by
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h := tendsto_mul_cofinite_nhds_zero
    (tendsto_mul_cofinite_nhds_zero ((decaysAt_iff_cofinite a ρ).mp ha)
      ((decaysAt_iff_cofinite b ρ).mp hb)) ((decaysAt_iff_cofinite c ρ).mp hc)
  have hi : Function.Injective (fun p : ℤ × ℤ => (p, k - p.1 - p.2)) :=
    fun _ _ h => congrArg Prod.fst h
  have ht := (h.comp hi.tendsto_cofinite).mul_const (ρ ^ (-k))
  simp only [zero_mul, Function.comp_def] at ht
  convert ht using 1
  funext p
  simp only [norm_mul, weightedCoefficient]
  have hw : ρ ^ p.1 * ρ ^ p.2 * ρ ^ (k - p.1 - p.2) * ρ ^ (-k) = 1 := by
    rw [← zpow_add₀ hρ.ne', ← zpow_add₀ hρ.ne', ← zpow_add₀ hρ.ne']
    simp
  linear_combination -(‖a p.1‖ * ‖b p.2‖ * ‖c (k - p.1 - p.2)‖) * hw

-- Elaborating the nested sums traverses the p-adic topological ring instances.
set_option maxHeartbeats 800000 in
theorem bilateralConvolution_assoc {a b c : LaurentCoefficients} {ρ : ℝ}
    (ha : DecaysAt a ρ) (hb : DecaysAt b ρ) (hc : DecaysAt c ρ) (hρ : 0 < ρ) :
    bilateralConvolution (bilateralConvolution a b) c =
      bilateralConvolution a (bilateralConvolution b c) := by
  ext k
  have hi : Function.Injective (fun p : ℤ × ℤ => (p.2, p.1 - p.2)) := by
    intro p q h
    obtain ⟨h1, h2⟩ := Prod.mk.inj h
    ext <;> dsimp at * <;> omega
  have hs := (ha.triple_slice_summable hb hc hρ k).comp_injective hi
  have he : Summable (fun p : ℤ × ℤ => a p.2 * (b (p.1 - p.2) * c (k - p.1))) := by
    apply hs.congr
    intro p
    dsimp only [Function.comp_def]
    rw [mul_assoc]
    congr 2
    congr 1
    omega
  simp only [bilateralConvolution]
  simp_rw [← tsum_mul_right, ← tsum_mul_left, mul_assoc]
  rw [← he.tsum_comm]
  apply tsum_congr
  intro j
  rw [← (Equiv.addLeft j).tsum_eq]
  apply tsum_congr
  intro l
  change a j * (b (j + l - j) * c (k - (j + l))) = a j * (b l * c (k - j - l))
  simp only [add_sub_cancel_left, sub_add_eq_sub_sub]

end Zeta7Annulus

import Zeta7Proof.AnnularConvolutionClosure

/-! Additive operations, Laurent monomials, and the genuine Euler Leibniz rule
for convergent bilateral coefficient families. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
open Filter Topology
namespace Zeta7Annulus
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

theorem DecaysAt.add {a b : LaurentCoefficients} {ρ : ℝ}
    (ha : DecaysAt a ρ) (hb : DecaysAt b ρ) (hρ : 0 < ρ) : DecaysAt (a + b) ρ := by
  rw [decaysAt_iff_cofinite]
  have ht := ((decaysAt_iff_cofinite a ρ).mp ha).max ((decaysAt_iff_cofinite b ρ).mp hb)
  apply squeeze_zero (fun k => weightedCoefficient_nonneg _ hρ k) (fun k => ?_)
    (by simpa only [max_self] using ht)
  simp only [weightedCoefficient, Pi.add_apply]
  calc
    _ ≤ max ‖a k‖ ‖b k‖ * ρ ^ k := mul_le_mul_of_nonneg_right
      (IsUltrametricDist.norm_add_le_max _ _) (zpow_pos hρ _).le
    _ = _ := max_mul_of_nonneg _ _ (zpow_pos hρ _).le

theorem DecaysAt.neg {a : LaurentCoefficients} {ρ : ℝ} (ha : DecaysAt a ρ) :
    DecaysAt (-a) ρ := by
  simpa only [DecaysAt, Pi.neg_apply, norm_neg] using ha

theorem DecaysAt.smul {a : LaurentCoefficients} {ρ : ℝ} (ha : DecaysAt a ρ) (z : ℚ_[7]) :
    DecaysAt (z • a) ρ := by
  rw [decaysAt_iff_cofinite]
  change Tendsto (fun k : ℤ => ‖z * a k‖ * ρ ^ k) cofinite (𝓝 0)
  simpa only [weightedCoefficient, norm_mul,
    mul_assoc, mul_zero] using ((decaysAt_iff_cofinite a ρ).mp ha).const_mul ‖z‖

def bilateralMonomial (n : ℤ) (z : ℚ_[7]) : LaurentCoefficients :=
  fun k => if k = n then z else 0

theorem bilateralMonomial_decays (n : ℤ) (z : ℚ_[7]) (ρ : ℝ) :
    DecaysAt (bilateralMonomial n z) ρ := by
  rw [decaysAt_iff_cofinite]
  apply tendsto_const_nhds.congr'
  filter_upwards [(Set.finite_singleton n).compl_mem_cofinite] with k hk
  have hk : k ≠ n := hk
  simp [weightedCoefficient, bilateralMonomial, hk]

theorem bilateralMonomial_convolution (n : ℤ) (z : ℚ_[7]) (a : LaurentCoefficients) (k : ℤ) :
    bilateralConvolution (bilateralMonomial n z) a k = z * a (k - n) := by
  simp [bilateralConvolution, bilateralMonomial, ite_mul]

theorem bilateralConvolution_monomial (a : LaurentCoefficients) (n : ℤ) (z : ℚ_[7]) (k : ℤ) :
    bilateralConvolution a (bilateralMonomial n z) k = a (k - n) * z := by
  rw [bilateralConvolution_comm, bilateralMonomial_convolution, mul_comm]

theorem bilateralConvolution_add_left {a b c : LaurentCoefficients} {ρ : ℝ}
    (ha : DecaysAt a ρ) (hb : DecaysAt b ρ) (hc : DecaysAt c ρ) (hρ : 0 < ρ) :
    bilateralConvolution (a + b) c = bilateralConvolution a c + bilateralConvolution b c := by
  ext k
  simp only [bilateralConvolution, Pi.add_apply, add_mul]
  exact (ha.convolution_summable hρ hc k).tsum_add (hb.convolution_summable hρ hc k)

theorem bilateralConvolution_add_right {a b c : LaurentCoefficients} {ρ : ℝ}
    (ha : DecaysAt a ρ) (hb : DecaysAt b ρ) (hc : DecaysAt c ρ) (hρ : 0 < ρ) :
    bilateralConvolution a (b + c) = bilateralConvolution a b + bilateralConvolution a c := by
  rw [bilateralConvolution_comm a (b + c), bilateralConvolution_add_left hb hc ha hρ,
    bilateralConvolution_comm b a, bilateralConvolution_comm c a]

def bilateralEuler (a : LaurentCoefficients) : LaurentCoefficients := fun k => (k : ℚ_[7]) * a k

theorem DecaysAt.euler {a : LaurentCoefficients} {ρ : ℝ}
    (ha : DecaysAt a ρ) (hρ : 0 < ρ) : DecaysAt (bilateralEuler a) ρ := by
  rw [decaysAt_iff_cofinite]
  apply squeeze_zero (fun k => weightedCoefficient_nonneg _ hρ k) (fun k => ?_)
    ((decaysAt_iff_cofinite a ρ).mp ha)
  simp only [weightedCoefficient, bilateralEuler, norm_mul]
  exact mul_le_mul_of_nonneg_right
    (mul_le_of_le_one_left (norm_nonneg _) (Padic.norm_int_le_one k)) (zpow_pos hρ _).le

theorem bilateralEuler_leibniz {a b : LaurentCoefficients} {ρ : ℝ}
    (ha : DecaysAt a ρ) (hb : DecaysAt b ρ) (hρ : 0 < ρ) :
    bilateralEuler (bilateralConvolution a b) =
      bilateralConvolution (bilateralEuler a) b + bilateralConvolution a (bilateralEuler b) := by
  ext k
  have h1 := (ha.euler hρ).convolution_summable hρ hb k
  have h2 := ha.convolution_summable hρ (hb.euler hρ) k
  simp only [bilateralEuler, bilateralConvolution, Pi.add_apply] at *
  rw [← tsum_mul_left, ← h1.tsum_add h2]
  apply tsum_congr
  intro i
  push_cast
  ring

end Zeta7Annulus

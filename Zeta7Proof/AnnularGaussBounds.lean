import Zeta7Proof.AnnularConvolutionCalculus

/-! Gauss bounds at arbitrary positive real radii for the actual bilateral
coefficient model. No restriction to radii in the value group is made. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
open Filter Topology
namespace Zeta7Annulus
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

def bilateralGauss (a : LaurentCoefficients) (ρ : ℝ) : ℝ :=
  ⨆ k : ℤ, weightedCoefficient a ρ k

theorem DecaysAt.weighted_bddAbove {a : LaurentCoefficients} {ρ : ℝ}
    (ha : DecaysAt a ρ) : BddAbove (Set.range (weightedCoefficient a ρ)) := by
  obtain ⟨C, _, hC⟩ := ha.weighted_bounded
  exact ⟨C, by rintro _ ⟨k, rfl⟩; exact hC k⟩

theorem weightedCoefficient_le_gauss {a : LaurentCoefficients} {ρ : ℝ}
    (ha : DecaysAt a ρ) (k : ℤ) : weightedCoefficient a ρ k ≤ bilateralGauss a ρ :=
  le_ciSup ha.weighted_bddAbove k

theorem bilateralGauss_nonneg {a : LaurentCoefficients} {ρ : ℝ}
    (ha : DecaysAt a ρ) (hρ : 0 < ρ) : 0 ≤ bilateralGauss a ρ :=
  (weightedCoefficient_nonneg a hρ 0).trans (weightedCoefficient_le_gauss ha 0)

theorem bilateralGauss_le {a : LaurentCoefficients} {ρ C : ℝ}
    (h : ∀ k, weightedCoefficient a ρ k ≤ C) : bilateralGauss a ρ ≤ C := ciSup_le h

theorem coefficient_norm_le_gauss {a : LaurentCoefficients} {ρ : ℝ}
    (ha : DecaysAt a ρ) (hρ : 0 < ρ) (k : ℤ) :
    ‖a k‖ ≤ bilateralGauss a ρ * ρ ^ (-k) := by
  have h := mul_le_mul_of_nonneg_right (weightedCoefficient_le_gauss ha k)
    (zpow_pos hρ (-k)).le
  simpa only [weightedCoefficient, mul_assoc, ← zpow_add₀ hρ.ne',
    add_neg_cancel, zpow_zero, mul_one] using h

theorem bilateralGauss_eq_zero_iff {a : LaurentCoefficients} {ρ : ℝ}
    (ha : DecaysAt a ρ) (hρ : 0 < ρ) : bilateralGauss a ρ = 0 ↔ a = 0 := by
  constructor
  · intro h
    funext k
    apply norm_eq_zero.mp
    exact le_antisymm (by simpa only [h, zero_mul] using coefficient_norm_le_gauss ha hρ k)
      (norm_nonneg _)
  · intro h; subst a
    simp [bilateralGauss, weightedCoefficient]

theorem bilateralGauss_pos {a : LaurentCoefficients} {ρ : ℝ}
    (ha : DecaysAt a ρ) (hρ : 0 < ρ) (hne : a ≠ 0) : 0 < bilateralGauss a ρ :=
  lt_of_le_of_ne (bilateralGauss_nonneg ha hρ)
    (fun h => hne ((bilateralGauss_eq_zero_iff ha hρ).mp h.symm))

theorem bilateralGauss_neg (a : LaurentCoefficients) (ρ : ℝ) :
    bilateralGauss (-a) ρ = bilateralGauss a ρ := by
  simp only [bilateralGauss, weightedCoefficient, Pi.neg_apply, norm_neg]

theorem bilateralGauss_add {a b : LaurentCoefficients} {ρ : ℝ}
    (ha : DecaysAt a ρ) (hb : DecaysAt b ρ) (hρ : 0 < ρ) :
    bilateralGauss (a + b) ρ ≤ max (bilateralGauss a ρ) (bilateralGauss b ρ) := by
  apply bilateralGauss_le
  intro k
  calc
    _ ≤ max ‖a k‖ ‖b k‖ * ρ ^ k := mul_le_mul_of_nonneg_right
      (IsUltrametricDist.norm_add_le_max _ _) (zpow_pos hρ k).le
    _ = max (weightedCoefficient a ρ k) (weightedCoefficient b ρ k) :=
      max_mul_of_nonneg _ _ (zpow_pos hρ k).le
    _ ≤ _ := max_le_max (weightedCoefficient_le_gauss ha k)
      (weightedCoefficient_le_gauss hb k)

theorem bilateralGauss_convolution {a b : LaurentCoefficients} {ρ : ℝ}
    (ha : DecaysAt a ρ) (hb : DecaysAt b ρ) (hρ : 0 < ρ) :
    bilateralGauss (bilateralConvolution a b) ρ ≤ bilateralGauss a ρ * bilateralGauss b ρ := by
  apply bilateralGauss_le
  exact bilateralConvolution_weighted_bound hρ ha hb (bilateralGauss_nonneg ha hρ)
    (bilateralGauss_nonneg hb hρ) (weightedCoefficient_le_gauss ha)
    (weightedCoefficient_le_gauss hb)

theorem bilateralGauss_euler {a : LaurentCoefficients} {ρ : ℝ}
    (ha : DecaysAt a ρ) (hρ : 0 < ρ) :
    bilateralGauss (bilateralEuler a) ρ ≤ bilateralGauss a ρ := by
  apply bilateralGauss_le
  intro k
  apply le_trans _ (weightedCoefficient_le_gauss ha k)
  simp only [weightedCoefficient, bilateralEuler, norm_mul]
  exact mul_le_mul_of_nonneg_right
    (mul_le_of_le_one_left (norm_nonneg _) (Padic.norm_int_le_one k)) (zpow_pos hρ k).le

theorem weightedCoefficient_intermediate (a : LaurentCoefficients) {r ρ R : ℝ}
    (hr : 0 < r) (hrρ : r ≤ ρ) (hρR : ρ ≤ R) (k : ℤ) :
    weightedCoefficient a ρ k ≤ max (weightedCoefficient a r k) (weightedCoefficient a R k) := by
  have hρ := hr.trans_le hrρ
  by_cases hk : 0 ≤ k
  · exact (mul_le_mul_of_nonneg_left (zpow_le_zpow_left₀ hk hρ.le hρR)
      (norm_nonneg _)).trans (le_max_right _ _)
  · apply le_trans _ (le_max_left _ _)
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    have hi : ρ⁻¹ ≤ r⁻¹ := inv_anti₀ hr hrρ
    have hp := zpow_le_zpow_left₀ (by omega : 0 ≤ -k) (inv_pos.mpr hρ).le hi
    simpa only [inv_zpow, zpow_neg, inv_inv] using hp

theorem DecaysAt.intermediate {a : LaurentCoefficients} {r ρ R : ℝ}
    (har : DecaysAt a r) (haR : DecaysAt a R)
    (hr : 0 < r) (hrρ : r ≤ ρ) (hρR : ρ ≤ R) : DecaysAt a ρ := by
  rw [decaysAt_iff_cofinite]
  apply squeeze_zero (weightedCoefficient_nonneg a (hr.trans_le hrρ))
    (weightedCoefficient_intermediate a hr hrρ hρR)
  simpa only [max_self] using ((decaysAt_iff_cofinite a r).mp har).max
    ((decaysAt_iff_cofinite a R).mp haR)

def closedAnnulusGauss (a : LaurentCoefficients) (r R : ℝ) : ℝ :=
  max (bilateralGauss a r) (bilateralGauss a R)

theorem intermediate_gauss_le {a : LaurentCoefficients} {r ρ R : ℝ}
    (har : DecaysAt a r) (haR : DecaysAt a R)
    (hr : 0 < r) (hrρ : r ≤ ρ) (hρR : ρ ≤ R) :
    bilateralGauss a ρ ≤ closedAnnulusGauss a r R := by
  apply bilateralGauss_le
  intro k
  exact (weightedCoefficient_intermediate a hr hrρ hρR k).trans
    (max_le_max (weightedCoefficient_le_gauss har k) (weightedCoefficient_le_gauss haR k))

theorem intermediate_coefficient_bound {a : LaurentCoefficients} {r ρ R : ℝ}
    (har : DecaysAt a r) (haR : DecaysAt a R)
    (hr : 0 < r) (hrρ : r ≤ ρ) (hρR : ρ ≤ R) (k : ℤ) :
    ‖a k‖ ≤ closedAnnulusGauss a r R * ρ ^ (-k) :=
  (coefficient_norm_le_gauss (har.intermediate haR hr hrρ hρR) (hr.trans_le hrρ) k).trans
    (mul_le_mul_of_nonneg_right (intermediate_gauss_le har haR hr hrρ hρR)
      (zpow_pos (hr.trans_le hrρ) (-k)).le)

end Zeta7Annulus

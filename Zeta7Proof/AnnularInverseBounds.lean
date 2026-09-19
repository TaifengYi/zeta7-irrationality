import Zeta7Proof.ClosedAnnulusInverses

/-! Nonarchimedean geometric-series bounds for the two constructed inverses. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
open Filter Topology
namespace Zeta7Annulus.ClosedAnnulus
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩
variable {r R : ℝ} [Fact (0 < r)] [Fact (0 < R)]

theorem norm_le_of_hasSum {ι : Type*} {f : ι → ClosedAnnulus r R} {a : ClosedAnnulus r R}
    (hf : HasSum f a) {C : ℝ} (hC : 0 ≤ C) (h : ∀ i, ‖f i‖ ≤ C) : ‖a‖ ≤ C := by
  apply le_of_tendsto hf.norm
  exact Eventually.of_forall (fun s =>
    IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hC (fun i _ => h i))

theorem nInverse_norm_le (hr : 1 < r) (hR : R < 49) (hrR : r ≤ R) :
    ‖nInverse (r := r) (R := R)‖ ≤ 1 := by
  apply norm_le_of_hasSum (nInverse_geometric hr hR hrR) zero_le_one
  intro n
  exact (norm_pow_le _ _).trans (pow_le_one₀ (norm_nonneg _)
    (by simpa only [norm_neg] using (nContraction_norm_lt_one hr hR hrR).le))

theorem pInverse_norm_le (hr : 1 < r) (hR : R < 49) (hrR : r ≤ R) :
    ‖pInverse (r := r) (R := R)‖ ≤ r⁻¹ := by
  have hm : ‖monomial (r := r) (R := R) (-1) (1 / 13)‖ = r⁻¹ := by
    rw [monomial_norm]
    simp only [norm_div, norm_one, norm_thirteen, div_one, one_mul, zpow_neg_one]
    exact max_eq_left (inv_anti₀ Fact.out hrR)
  apply norm_le_of_hasSum (pInverse_geometric hr hR hrR) (inv_pos.mpr Fact.out).le
  intro n
  calc
    _ ≤ ‖(-pContraction (r := r) (R := R)) ^ n‖ *
        ‖monomial (r := r) (R := R) (-1) (1 / 13)‖ := norm_mul_le _ _
    _ ≤ 1 * r⁻¹ := mul_le_mul
      ((norm_pow_le _ _).trans (pow_le_one₀ (norm_nonneg _)
        (by simpa only [norm_neg] using (pContraction_norm_lt_one hr hR hrR).le)))
      hm.le (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

end Zeta7Annulus.ClosedAnnulus

import Zeta7Proof.LevelSevenEtaCusps
import Zeta7Proof.LevelSevenNorm

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open UpperHalfPlane Matrix.SpecialLinearGroup ModularForm
open scoped ModularForm MatrixGroups Manifold
namespace Zeta7LevelSeven

theorem bounded_all_slashes_of_two_cusps {k : ℤ} (f : SlashInvariantForm GammaSeven k)
    (hinfty : IsBoundedAtImInfty f)
    (h0 : IsBoundedAtImInfty ((f : ℍ → ℂ) ∣[k] ModularGroup.S))
    (γ : SL(2, ℤ)) : IsBoundedAtImInfty ((f : ℍ → ℂ) ∣[k] γ) := by
  obtain ⟨δ, hδ, j, rfl⟩ := schreier_decomposition γ
  rw [SlashAction.slash_mul]
  have hd : (f : ℍ → ℂ) ∣[k] δ = f := by
    rw [SL_slash]
    exact SlashInvariantForm.slash_action_eqn f _ ⟨δ, schreierGroup_le hδ, rfl⟩
  rw [hd]
  by_cases hj : j = 0
  · subst j
    simpa [cosetRep] using hinfty
  · rw [cosetRep, if_neg hj, SlashAction.slash_mul, SL_slash]
    apply IsBoundedAtImInfty.slash k ?_ h0
    change (((ModularGroup.T ^ ((j.val : ℤ) - 1)).val 1 0 : ℤ) : ℝ) = 0
    rw [ModularGroup.coe_T_zpow]
    norm_num

/-- Packages a genuine form after checking modularity, holomorphy and the two cusp bounds. -/
def levelSevenFormOfTwoCusps {k : ℤ} (f : SlashInvariantForm GammaSeven k)
    (hh : MDiff (f : ℍ → ℂ)) (hinfty : IsBoundedAtImInfty f)
    (h0 : IsBoundedAtImInfty ((f : ℍ → ℂ) ∣[k] ModularGroup.S)) :
    ModularForm GammaSeven k where
  __ := f
  holo' := hh
  bdd_at_cusps' hc := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    intro γ _
    exact bounded_all_slashes_of_two_cusps f hinfty h0 γ

end Zeta7LevelSeven

import Zeta7Proof.LevelSevenGenerators
import Zeta7Proof.WidthSevenQExpansion
import Mathlib.NumberTheory.ModularForms.NormTrace
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula

/-! Specialization of the pinned, proved modular-form norm to Γ₀(7).
The order comparison between a form and its norm remains a separate obligation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open Matrix.SpecialLinearGroup UpperHalfPlane
open scoped MatrixGroups ModularForm
namespace Zeta7LevelSeven

abbrev GammaSeven : Subgroup (GL (Fin 2) ℝ) := CongruenceSubgroup.Gamma0 7

theorem GammaSeven_relIndex : GammaSeven.relIndex 𝒮ℒ = 8 := by
  have h := Subgroup.relIndex_map_map_of_injective (CongruenceSubgroup.Gamma0 7) ⊤
    (f := (mapGL ℝ : Matrix.SpecialLinearGroup (Fin 2) ℤ →* GL (Fin 2) ℝ))
    (mapGL_injective (S := ℝ))
  rw [← MonoidHom.range_eq_map, Subgroup.relIndex_top_right, Gamma0_seven_index] at h
  exact h

theorem norm_quotient_card : Nat.card (𝒮ℒ ⧸ GammaSeven.subgroupOf 𝒮ℒ) = 8 :=
  GammaSeven_relIndex

/-- The actual Mathlib norm has weight 8k at this level. -/
def levelSevenNorm {k : ℤ} (f : ModularForm GammaSeven k) : ModularForm 𝒮ℒ (8 * k) := by
  have h : k * (Nat.card (𝒮ℒ ⧸ GammaSeven.subgroupOf 𝒮ℒ) : ℤ) = 8 * k := by
    rw [norm_quotient_card]
    ring
  exact ModularForm.mcast h (ModularForm.norm 𝒮ℒ f)

theorem levelSevenNorm_eq_zero_iff {k : ℤ} (f : ModularForm GammaSeven k) :
    levelSevenNorm f = 0 ↔ f = 0 := by
  simp [levelSevenNorm, ModularForm.norm_eq_zero_iff, FunLike.coe_zero_iff]

end Zeta7LevelSeven

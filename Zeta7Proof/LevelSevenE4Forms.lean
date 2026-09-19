import Zeta7Proof.LevelSevenACusps

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open UpperHalfPlane Matrix.SpecialLinearGroup HeckeRing.GL2 ModularForm Function
open scoped MatrixGroups ModularForm Manifold
namespace Zeta7LevelSeven

abbrev classicalE4 := ModularForm.E (k := 4) (by decide)

theorem classicalE4_slash (γ : SL(2, ℤ)) :
    (classicalE4 : ℍ → ℂ) ∣[(4 : ℤ)] γ = classicalE4 := by
  rw [SL_slash]
  exact SlashInvariantForm.slash_action_eqn classicalE4 _ ⟨γ, rfl⟩

def E4SlashInvariant : SlashInvariantForm GammaSeven 4 where
  toFun := classicalE4
  slash_action_eq' γ hγ := by
    obtain ⟨δ, _, rfl⟩ := hγ
    simpa [SL_slash, mapGL] using classicalE4_slash δ

def E4ModularForm : ModularForm GammaSeven 4 :=
  levelSevenFormOfTwoCusps E4SlashInvariant (ModularFormClass.holo classicalE4)
    (ModularFormClass.bdd_at_infty classicalE4)
    (ModularFormClass.bdd_at_infty_slash classicalE4 ModularGroup.S)

theorem E4_periodic : Periodic ((classicalE4 : ℍ → ℂ) ∘ ofComplex) 1 :=
  SlashInvariantFormClass.periodic_comp_ofComplex classicalE4 (by simp)

theorem E4_seven_slash (γ : CongruenceSubgroup.Gamma0 7) :
    levelRaiseFun 7 4 classicalE4 ∣[(4 : ℤ)] γ.val = levelRaiseFun 7 4 classicalE4 := by
  rw [SL_slash]
  change levelRaiseFun 7 4 classicalE4 ∣[(4 : ℤ)] mapGL ℝ γ.val = _
  rw [slash_mapGL_levelRaiseFun 7 4 γ.val
    ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (CongruenceSubgroup.Gamma0_mem.mp γ.property))]
  change levelRaiseFun 7 4 ((classicalE4 : ℍ → ℂ) ∣[(4 : ℤ)] sevenConj γ) = _
  rw [classicalE4_slash]

def E4SevenSlashInvariant : SlashInvariantForm GammaSeven 4 where
  toFun := levelRaiseFun 7 4 classicalE4
  slash_action_eq' γ hγ := by
    obtain ⟨δ, hδ, rfl⟩ := hγ
    simpa [SL_slash, mapGL] using E4_seven_slash ⟨δ, hδ⟩

theorem E4_S_value (τ : ℍ) : classicalE4 (ModularGroup.S • τ) =
    (τ : ℂ) ^ 4 * classicalE4 τ := by
  have h := congrFun (classicalE4_slash ModularGroup.S) τ
  rw [SL_slash_apply] at h
  have hd : denom ModularGroup.S (τ : ℂ) = (τ : ℂ) := by simp [denom, ModularGroup.S]
  rw [hd] at h
  norm_num only [zpow_neg, zpow_ofNat] at h
  field_simp [τ.ne_zero] at h
  linear_combination h

theorem E4_seven_S_value (τ : ℍ) :
    (levelRaiseFun 7 4 classicalE4 ∣[(4 : ℤ)] ModularGroup.S) τ =
      (7 : ℂ)⁻¹ ^ 4 * classicalE4 (divSeven τ) := by
  rw [SL_slash_apply, levelRaiseFun_apply, levelRaise_S_divSeven, E4_S_value]
  have hd : denom ModularGroup.S (τ : ℂ) = (τ : ℂ) := by simp [denom, ModularGroup.S]
  rw [hd]
  change (((τ : ℂ) / 7) ^ 4 * classicalE4 (divSeven τ)) * (τ : ℂ) ^ (-4 : ℤ) = _
  field_simp [τ.ne_zero]

def E4SevenModularForm : ModularForm GammaSeven 4 :=
  levelSevenFormOfTwoCusps E4SevenSlashInvariant
    (levelRaise_seven_holo E4_periodic (ModularFormClass.holo classicalE4)
      (ModularFormClass.bdd_at_infty classicalE4) 4)
    (levelRaise_seven_bounded (ModularFormClass.bdd_at_infty classicalE4) 4) (by
      have h := Filter.BoundedAtFilter.smul ((7 : ℂ)⁻¹ ^ 4)
        (divSeven_bounded E4_periodic (ModularFormClass.holo classicalE4)
          (ModularFormClass.bdd_at_infty classicalE4))
      have he : (levelRaiseFun 7 4 classicalE4 ∣[(4 : ℤ)] ModularGroup.S) =
          (7 : ℂ)⁻¹ ^ 4 • (fun τ => classicalE4 (divSeven τ)) := by
        funext τ
        exact E4_seven_S_value τ
      change IsBoundedAtImInfty (levelRaiseFun 7 4 classicalE4 ∣[(4 : ℤ)] ModularGroup.S)
      rw [he]
      exact h)

theorem E4_seven_qExpansion : qExpansion 1 E4SevenModularForm =
    (PowerSeries.expand 7 (by decide) Zeta7Common.eisensteinFourQ).map (algebraMap ℚ ℂ) := by
  change qExpansion 1 (levelRaiseFun 7 4 classicalE4) = _
  rw [levelRaise_seven_qExpansion E4_periodic (ModularFormClass.holo classicalE4)
    (ModularFormClass.bdd_at_infty classicalE4),
    ← Zeta7Common.eisensteinFourQ_classical, PowerSeries.map_expand]

end Zeta7LevelSeven

import Zeta7Proof.LevelRaiseQExpansion
import Zeta7Proof.RamanujanTwo
import Zeta7Proof.LevelSevenNormOrder

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open Complex hiding eta
open UpperHalfPlane hiding I
open Matrix.SpecialLinearGroup HeckeRing.GL2 Zeta7Classical
open EisensteinSeries Function ModularForm Filter
open scoped Real MatrixGroups ModularForm Manifold Topology
namespace Zeta7LevelSeven

def actualA : ℍ → ℂ := (1 / 6 : ℂ) • ((7 : ℂ) • levelRaiseFun 7 2 E2 - E2)

theorem e2Shift_sevenConj (γ : CongruenceSubgroup.Gamma0 7) :
    (7 : ℂ) • levelRaiseFun 7 2 (e2Shift (sevenConj γ)) = e2Shift γ.val := by
  have hd : (7 : ℤ) ∣ γ.val.val 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (CongruenceSubgroup.Gamma0_mem.mp γ.property)
  have he : ((γ.val.val 1 0 / 7 : ℤ) : ℂ) * 7 = (γ.val.val 1 0 : ℂ) := by
    exact_mod_cast Int.ediv_mul_cancel hd
  funext τ
  simp only [Pi.smul_apply, smul_eq_mul, levelRaiseFun_apply, e2Shift]
  have hc : denom (sevenConj γ) ((levelRaiseMatrix 7 • τ : ℍ) : ℂ) =
      ((γ.val.val 1 0 / 7 : ℤ) : ℂ) * (7 * (τ : ℂ)) + γ.val.val 1 1 := by
    simp [denom, sevenConj, levelRaiseConjOfDvd, mapGL, coe_levelRaiseMatrix_smul]
  rw [hc]
  simp only [sevenConj, levelRaiseConjOfDvd, denom, mapGL, zpow_neg_one]
  norm_num
  rw [← mul_assoc _ 7 (τ : ℂ), he]
  rw [← he]
  ring

theorem actualA_slash (γ : CongruenceSubgroup.Gamma0 7) :
    actualA ∣[(2 : ℤ)] γ.val = actualA := by
  have hd : (7 : ℤ) ∣ γ.val.val 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (CongruenceSubgroup.Gamma0_mem.mp γ.property)
  have he : levelRaiseFun 7 2 E2 ∣[(2 : ℤ)] γ.val =
      levelRaiseFun 7 2 E2 + levelRaiseFun 7 2 (e2Shift (sevenConj γ)) := by
    rw [SL_slash]
    change levelRaiseFun 7 2 E2 ∣[(2 : ℤ)] mapGL ℝ γ.val = _
    rw [slash_mapGL_levelRaiseFun 7 2 γ.val hd]
    change levelRaiseFun 7 2 (E2 ∣[(2 : ℤ)] sevenConj γ) = _
    rw [E2_slash_add_shift]
    funext τ
    simp [levelRaiseFun_apply]
  simp only [actualA, sub_eq_add_neg, SL_smul_slash, SlashAction.add_slash,
    SlashAction.neg_slash, he, E2_slash_add_shift]
  simp only [smul_add, e2Shift_sevenConj, smul_neg, neg_add]
  abel

def actualASlashInvariant : SlashInvariantForm GammaSeven 2 where
  toFun := actualA
  slash_action_eq' γ hγ := by
    obtain ⟨δ, hδ, rfl⟩ := hγ
    simpa [SL_slash, mapGL] using actualA_slash ⟨δ, hδ⟩

theorem E2_seven_cusp_analytic :
    AnalyticAt ℂ (cuspFunction 1 (levelRaiseFun 7 2 E2)) 0 := by
  rw [levelRaise_seven_qLift Zeta7Common.E2_periodic_comp_ofComplex]
  exact qLift_cusp_analytic
    ((differentiableOn_cuspFunction_ball (by norm_num : (0 : ℝ) < 1)
      Zeta7Common.E2_periodic_comp_ofComplex E2_mdifferentiable isBoundedAtImInfty_E2).comp
      (by fun_prop) (fun _ hz => pow_seven_ball hz))

theorem actualA_qExpansion :
    qExpansion 1 actualA = Zeta7Main.ASeries.map (algebraMap ℚ ℂ) := by
  have he := Zeta7Common.E2_analyticAt_cusp
  have he7 := E2_seven_cusp_analytic
  have h7 : AnalyticAt ℂ (cuspFunction 1 ((7 : ℂ) • levelRaiseFun 7 2 E2)) 0 := by
    rw [cuspFunction_smul he7.continuousAt]
    exact he7.const_smul
  have hs : AnalyticAt ℂ (cuspFunction 1 ((7 : ℂ) • levelRaiseFun 7 2 E2 - E2)) 0 := by
    rw [cuspFunction_sub h7.continuousAt he.continuousAt]
    exact h7.sub he
  rw [actualA, qExpansion_smul hs, qExpansion_sub h7 he, qExpansion_smul he7,
    E2_seven_qExpansion, ← Zeta7Common.eisensteinTwoQ_classical]
  have h := congrArg (PowerSeries.map (algebraMap ℚ ℂ)) Zeta7Common.ASeries_eisensteinTwo
  simp only [map_mul, map_sub, PowerSeries.map_C] at h
  ext n
  have hn := congrArg (PowerSeries.coeff n) h
  simp only [map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_smul] at hn ⊢
  norm_num only [map_ofNat, smul_eq_mul] at hn ⊢
  linear_combination (-1 / 6 : ℂ) * hn

end Zeta7LevelSeven

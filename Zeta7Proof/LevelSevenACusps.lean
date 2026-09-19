import Zeta7Proof.LevelSevenAForm
import Zeta7Proof.LevelSevenTwoCusps

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open Complex hiding eta
open UpperHalfPlane hiding I
open Matrix.SpecialLinearGroup HeckeRing.GL2 Zeta7Classical
open EisensteinSeries Function ModularForm Filter
open scoped Real MatrixGroups ModularForm Manifold Topology
namespace Zeta7LevelSeven

theorem levelRaise_seven_holo {f : ℍ → ℂ}
    (hp : Periodic (f ∘ ofComplex) 1) (hh : MDiff f)
    (hb : IsBoundedAtImInfty f) (k : ℤ) : MDiff (levelRaiseFun 7 k f) := by
  rw [levelRaise_seven_qLift hp]
  exact qLift_holo ((differentiableOn_cuspFunction_ball
    (by norm_num : (0 : ℝ) < 1) hp hh hb).comp
      (by fun_prop) (fun _ hz => pow_seven_ball hz))

theorem levelRaise_seven_bounded {f : ℍ → ℂ} (hb : IsBoundedAtImInfty f) (k : ℤ) :
    IsBoundedAtImInfty (levelRaiseFun 7 k f) := by
  have ht : Tendsto (fun τ : ℍ => levelRaiseMatrix 7 • τ) atImInfty atImInfty :=
    tendsto_smul_atImInfty (by simp [levelRaiseMatrix])
  have he : levelRaiseFun 7 k f = fun τ => f (levelRaiseMatrix 7 • τ) := by
    funext τ
    exact levelRaiseFun_apply 7 k f τ
  rw [he]
  exact hb.comp_tendsto ht

theorem divSeven_bounded {f : ℍ → ℂ} (hp : Periodic (f ∘ ofComplex) 1)
    (hh : MDiff f) (hb : IsBoundedAtImInfty f) :
    IsBoundedAtImInfty (fun τ => f (divSeven τ)) := by
  have ha := analyticAt_cuspFunction_zero (by norm_num : (0 : ℝ) < 1) hp hh hb
  have ht := ha.continuousAt.tendsto.comp
    (qParam_tendsto_atImInfty (by norm_num : (0 : ℝ) < 7))
  have he : (fun τ : ℍ => cuspFunction 1 f (Periodic.qParam 7 τ)) =
      (fun τ => f (divSeven τ)) := by
    funext τ
    rw [← qParam_divSeven, eq_cuspFunction _ (by norm_num : (1 : ℝ) ≠ 0) hp]
  rw [Function.comp_def, he] at ht
  exact ht.isBigO_one ℝ

theorem levelRaise_S_divSeven (τ : ℍ) :
    levelRaiseMatrix 7 • (ModularGroup.S • τ) = ModularGroup.S • divSeven τ := by
  apply UpperHalfPlane.ext
  rw [coe_levelRaiseMatrix_smul, modular_S_smul, modular_S_smul]
  change (7 : ℂ) * (-(τ : ℂ))⁻¹ = (-((τ : ℂ) / 7))⁻¹
  field_simp

theorem E2_S_value (τ : ℍ) :
    E2 (ModularGroup.S • τ) = (τ : ℂ) ^ 2 * E2 τ + 12 * (2 * π * I)⁻¹ * τ := by
  have h := congrFun (E2_slash_add_shift ModularGroup.S) τ
  simp only [SL_slash_apply, Pi.add_apply, e2Shift] at h
  have hd : denom ModularGroup.S (τ : ℂ) = (τ : ℂ) := by simp [denom, ModularGroup.S]
  rw [hd] at h
  have hs : ((ModularGroup.S.val 1 0 : ℤ) : ℂ) = 1 := by norm_num [ModularGroup.S]
  rw [hs] at h
  simp only [mul_one, zpow_neg, zpow_ofNat, pow_one] at h
  calc
    _ = (E2 (ModularGroup.S • τ) * ((τ : ℂ) ^ 2)⁻¹) * (τ : ℂ) ^ 2 := by
      rw [mul_assoc, inv_mul_cancel₀ (pow_ne_zero 2 τ.ne_zero), mul_one]
    _ = (E2 τ + 12 * (2 * π * I)⁻¹ * (τ : ℂ)⁻¹) * (τ : ℂ) ^ 2 := by rw [h]
    _ = _ := by field_simp [τ.ne_zero] <;> ring

theorem actualA_S_value (τ : ℍ) :
    (actualA ∣[(2 : ℤ)] ModularGroup.S) τ =
      (1 / 6 : ℂ) * ((1 / 7 : ℂ) * E2 (divSeven τ) - E2 τ) := by
  rw [SL_slash_apply]
  simp only [actualA, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
    levelRaiseFun_apply, levelRaise_S_divSeven, E2_S_value]
  have hd : denom ModularGroup.S (τ : ℂ) = (τ : ℂ) := by simp [denom, ModularGroup.S]
  rw [hd]
  change ((1 / 6 : ℂ) *
    (7 * (((τ : ℂ) / 7) ^ 2 * E2 (divSeven τ) + 12 * (2 * π * I)⁻¹ * ((τ : ℂ) / 7)) -
      ((τ : ℂ) ^ 2 * E2 τ + 12 * (2 * π * I)⁻¹ * τ))) * (τ : ℂ) ^ (-2 : ℤ) = _
  field_simp [τ.ne_zero]
  ring

theorem actualA_holo : MDiff actualA := by
  exact ((levelRaise_seven_holo Zeta7Common.E2_periodic_comp_ofComplex
    E2_mdifferentiable isBoundedAtImInfty_E2 2).const_smul (7 : ℂ) |>.sub
      E2_mdifferentiable).const_smul (1 / 6 : ℂ)

theorem actualA_bounded : IsBoundedAtImInfty actualA := by
  simpa only [IsBoundedAtImInfty, actualA, sub_eq_add_neg] using
    BoundedAtFilter.smul (1 / 6 : ℂ)
      ((BoundedAtFilter.smul (7 : ℂ) (levelRaise_seven_bounded isBoundedAtImInfty_E2 2)).add
        isBoundedAtImInfty_E2.neg)

theorem actualA_S_bounded : IsBoundedAtImInfty (actualA ∣[(2 : ℤ)] ModularGroup.S) := by
  have h := BoundedAtFilter.smul (1 / 6 : ℂ)
    ((BoundedAtFilter.smul (1 / 7 : ℂ) (divSeven_bounded
      Zeta7Common.E2_periodic_comp_ofComplex E2_mdifferentiable isBoundedAtImInfty_E2)).add
        isBoundedAtImInfty_E2.neg)
  have he : (actualA ∣[(2 : ℤ)] ModularGroup.S) =
      (1 / 6 : ℂ) • ((1 / 7 : ℂ) • (fun τ => E2 (divSeven τ)) - E2) := by
    funext τ
    exact actualA_S_value τ
  rw [he]
  exact h

def actualAModularForm : ModularForm GammaSeven 2 :=
  levelSevenFormOfTwoCusps actualASlashInvariant actualA_holo actualA_bounded actualA_S_bounded

end Zeta7LevelSeven

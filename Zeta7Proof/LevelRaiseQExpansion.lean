import Zeta7Proof.QParameterLift
import Zeta7Proof.ActualEisensteinClassical

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open UpperHalfPlane Function
open HeckeRing.GL2
open scoped Manifold
namespace Zeta7LevelSeven

theorem levelRaise_seven_qLift {f : ℍ → ℂ}
    (hfper : Periodic (f ∘ ofComplex) 1) (k : ℤ) :
    levelRaiseFun 7 k f = qLift (fun z => cuspFunction 1 f (z ^ 7)) := by
  funext τ
  rw [levelRaiseFun_apply, qLift, ← eq_cuspFunction
    (levelRaiseMatrix 7 • τ) (by norm_num : (1 : ℝ) ≠ 0) hfper]
  rw [coe_levelRaiseMatrix_smul]
  norm_num only [Nat.cast_ofNat]
  rw [qParam_one_seven]

/-- Full level-raising identity, with width one retained on both sides. -/
theorem levelRaise_seven_qExpansion {f : ℍ → ℂ}
    (hfper : Periodic (f ∘ ofComplex) 1) (hfhol : MDiff f)
    (hfbdd : IsBoundedAtImInfty f) (k : ℤ) :
    qExpansion 1 (levelRaiseFun 7 k f) =
      PowerSeries.expand 7 (by decide) (qExpansion 1 f) := by
  rw [levelRaise_seven_qLift hfper k]
  have hd := differentiableOn_cuspFunction_ball (by norm_num : (0 : ℝ) < 1)
    hfper hfhol hfbdd
  apply qLift_qExpansion (hd.comp (by fun_prop) (fun _ hz => pow_seven_ball hz))
  intro z hz
  apply hasSum_expand_seven
  have hs := Complex.hasSum_taylorSeries_on_ball hd
    (pow_seven_ball (by simpa using hz))
  convert hs using 1 <;> try rfl
  funext n
  simp only [qExpansion_coeff, smul_eq_mul, sub_zero]
  ring

theorem E2_seven_qExpansion :
    qExpansion 1 (levelRaiseFun 7 2 EisensteinSeries.E2) =
      (PowerSeries.expand 7 (by decide) Zeta7Common.eisensteinTwoQ).map
        (algebraMap ℚ ℂ) := by
  rw [levelRaise_seven_qExpansion Zeta7Common.E2_periodic_comp_ofComplex
    E2_mdifferentiable EisensteinSeries.isBoundedAtImInfty_E2,
    ← Zeta7Common.eisensteinTwoQ_classical, PowerSeries.map_expand]

end Zeta7LevelSeven

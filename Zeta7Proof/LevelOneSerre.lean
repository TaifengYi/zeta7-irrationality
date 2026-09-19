import Zeta7Proof.ClassicalEulerTransport
import Zeta7Proof.ActualEisensteinClassical
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula

/-! Genuine level-one modular forms obtained by Serre differentiation.
This supplies the level-one part of the Ramanujan argument; it does not
assert a level-seven Sturm bound. -/
noncomputable section
open UpperHalfPlane Derivative ModularForm Filter
open scoped MatrixGroups ModularForm Manifold
namespace Zeta7Classical

def levelOneForm {k : ℤ} (f : ℍ → ℂ) (hf : MDiff f)
    (hs : ∀ γ : SL(2, ℤ), f ∣[k] γ = f) (hb : IsBoundedAtImInfty f) :
    ModularForm 𝒮ℒ k where
  toFun := f
  slash_action_eq' := by
    intro g hg
    obtain ⟨γ, rfl⟩ := hg
    exact hs γ
  holo' := hf
  bdd_at_cusps' := by
    intro c hc
    apply (OnePoint.isBoundedAt_iff_forall_SL2Z hc).mpr
    intro γ hγ
    rw [hs γ]
    exact hb

theorem serre_bounded {k : ℤ} (f : ModularForm 𝒮ℒ k) :
    IsBoundedAtImInfty (serreDerivative k f) := by
  have hd := (normalizedDeriv_zero_at_infty (by norm_num : (0 : ℝ) < 1)
    (SlashInvariantFormClass.periodic_comp_ofComplex f one_mem_strictPeriods_SL)
    (ModularFormClass.holo f) (ModularFormClass.bdd_at_infty f)).isBoundedAtImInfty
  have hp : BoundedAtFilter atImInfty (EisensteinSeries.E2 * (f : ℍ → ℂ)) :=
    BoundedAtFilter.mul EisensteinSeries.isBoundedAtImInfty_E2 (ModularFormClass.bdd_at_infty f)
  have hb := BoundedAtFilter.add hd (BoundedAtFilter.neg (hp.smul ((k : ℂ) * 12⁻¹)))
  change BoundedAtFilter atImInfty (fun z => normalizedDerivOfComplex f z -
    (k : ℂ) * 12⁻¹ * EisensteinSeries.E2 z * f z)
  simpa only [IsBoundedAtImInfty, serreDerivative, Pi.add_def, Pi.neg_def,
    Pi.smul_def, Pi.mul_def, smul_eq_mul, sub_eq_add_neg, mul_assoc] using hb

/-- This is an actual Mathlib modular form, with all cusp bounds proved. -/
def serreLevelOne {k : ℤ} (f : ModularForm 𝒮ℒ k) : ModularForm 𝒮ℒ (k + 2) :=
  levelOneForm (serreDerivative k f) (serreDerivative_mdifferentiable k (ModularFormClass.holo f))
    (fun γ => serreDerivative_slash_invariant (ModularFormClass.holo f)
      (show (f : ℍ → ℂ) ∣[k] γ = f from
        SlashInvariantFormClass.slash_action_eq f _ ⟨γ, rfl⟩))
    (serre_bounded f)

theorem levelOne_eq_of_coeff_zero {k : ℕ} (hk : k < 12)
    (f g : ModularForm 𝒮ℒ (k : ℤ))
    (h : PowerSeries.coeff 0 (qExpansion 1 f) = PowerSeries.coeff 0 (qExpansion 1 g)) : f = g := by
  apply sub_eq_zero.mp
  apply ModularForm.sturm_bound_levelOne_nat
  rw [Nat.div_eq_of_lt hk]
  have ho : (1 : ℕ∞) ≤ (qExpansion 1 (f - g)).order := by
    apply PowerSeries.nat_le_order _ 1
    intro i hi
    have hi0 : i = 0 := by omega
    subst i
    rw [ModularForm.qExpansion_sub (by norm_num) one_mem_strictPeriods_SL,
      map_sub, h, sub_self]
  exact lt_of_lt_of_le (by norm_num) ho

end Zeta7Classical

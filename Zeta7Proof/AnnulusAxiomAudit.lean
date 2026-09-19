import Zeta7Proof.AnnulusEstimates
import Lean.Elab.Print

/-! Full declarations, explicit premises and transitive kernel dependencies.
Generic decay hypotheses below are audited as hypotheses; none is instantiated
as an assumed target continuation theorem. -/

set_option linter.style.setOption false
set_option pp.proofs true
set_option pp.maxSteps 1000000
set_option format.width 120

#check @Zeta7Annulus.LaurentCoefficients
#print Zeta7Annulus.LaurentCoefficients
#print axioms Zeta7Annulus.LaurentCoefficients

#check @Zeta7Annulus.DecaysAt
#print Zeta7Annulus.DecaysAt
#print axioms Zeta7Annulus.DecaysAt

#check @Zeta7Annulus.DecaysOn
#print Zeta7Annulus.DecaysOn
#print axioms Zeta7Annulus.DecaysOn

#check @Zeta7Annulus.reverse
#print Zeta7Annulus.reverse
#print axioms Zeta7Annulus.reverse

#check @Zeta7Annulus.reverse_reverse
#print Zeta7Annulus.reverse_reverse
#print axioms Zeta7Annulus.reverse_reverse

#check @Zeta7Annulus.reverse_decaysAt_iff
#print Zeta7Annulus.reverse_decaysAt_iff
#print axioms Zeta7Annulus.reverse_decaysAt_iff

#check @Zeta7Annulus.DecaysAt.summable_tails
#print Zeta7Annulus.DecaysAt.summable_tails
#print axioms Zeta7Annulus.DecaysAt.summable_tails

#check @Zeta7Annulus.eval
#print Zeta7Annulus.eval
#print axioms Zeta7Annulus.eval

#check @Zeta7Annulus.eval_reverse
#print Zeta7Annulus.eval_reverse
#print axioms Zeta7Annulus.eval_reverse

#check @Zeta7Annulus.ofPowerSeries
#print Zeta7Annulus.ofPowerSeries
#print axioms Zeta7Annulus.ofPowerSeries

#check @Zeta7Annulus.ofPowerSeries_nat
#print Zeta7Annulus.ofPowerSeries_nat
#print axioms Zeta7Annulus.ofPowerSeries_nat

#check @Zeta7Annulus.ofPowerSeries_negSucc
#print Zeta7Annulus.ofPowerSeries_negSucc
#print axioms Zeta7Annulus.ofPowerSeries_negSucc

#check @Zeta7Annulus.ofPowerSeries_decaysAt_iff
#print Zeta7Annulus.ofPowerSeries_decaysAt_iff
#print axioms Zeta7Annulus.ofPowerSeries_decaysAt_iff

#check @Zeta7Annulus.hasGaussNorm_of_decay
#print Zeta7Annulus.hasGaussNorm_of_decay
#print axioms Zeta7Annulus.hasGaussNorm_of_decay

#check @Zeta7Main.normalisedHSeries
#print Zeta7Main.normalisedHSeries
#print axioms Zeta7Main.normalisedHSeries

#check @Zeta7Main.oppositeH
#print Zeta7Main.oppositeH
#print axioms Zeta7Main.oppositeH

#check @Zeta7Main.HSeries_eq_eisenstein_subst
#print Zeta7Main.HSeries_eq_eisenstein_subst
#print axioms Zeta7Main.HSeries_eq_eisenstein_subst

#check @Zeta7Main.HSeries_constant
#print Zeta7Main.HSeries_constant
#print axioms Zeta7Main.HSeries_constant

#check @Zeta7Main.normalisedHSeries_coeff
#print Zeta7Main.normalisedHSeries_coeff
#print axioms Zeta7Main.normalisedHSeries_coeff

#check @Zeta7Main.normalisedHSeries_constant
#print Zeta7Main.normalisedHSeries_constant
#print axioms Zeta7Main.normalisedHSeries_constant

#check @Zeta7Main.oppositeH_nonpositive_coeff
#print Zeta7Main.oppositeH_nonpositive_coeff
#print axioms Zeta7Main.oppositeH_nonpositive_coeff

#check @Zeta7Main.oppositeH_positive_coeff
#print Zeta7Main.oppositeH_positive_coeff
#print axioms Zeta7Main.oppositeH_positive_coeff

#check @Zeta7Main.oppositeH_constant
#print Zeta7Main.oppositeH_constant
#print axioms Zeta7Main.oppositeH_constant

#check @Zeta7Main.norm_seven_square
#print Zeta7Main.norm_seven_square
#print axioms Zeta7Main.norm_seven_square

#check @Zeta7Main.normalisedHSeries_weighted_coeff
#print Zeta7Main.normalisedHSeries_weighted_coeff
#print axioms Zeta7Main.normalisedHSeries_weighted_coeff

#check @Zeta7Main.normalisedHSeries_decay_iff
#print Zeta7Main.normalisedHSeries_decay_iff
#print axioms Zeta7Main.normalisedHSeries_decay_iff

#check @Zeta7Main.oppositeH_decay_iff
#print Zeta7Main.oppositeH_decay_iff
#print axioms Zeta7Main.oppositeH_decay_iff

#check @Zeta7Main.oppositeH_decaysOn_iff
#print Zeta7Main.oppositeH_decaysOn_iff
#print axioms Zeta7Main.oppositeH_decaysOn_iff

#check @Zeta7Main.seven_free_divisors_mul_seven
#print Zeta7Main.seven_free_divisors_mul_seven
#print axioms Zeta7Main.seven_free_divisors_mul_seven

#check @Zeta7Main.eisensteinMinusTwo_coeff_seven_mul
#print Zeta7Main.eisensteinMinusTwo_coeff_seven_mul
#print axioms Zeta7Main.eisensteinMinusTwo_coeff_seven_mul

#check @Zeta7Main.qExpansionUSeven
#print Zeta7Main.qExpansionUSeven
#print axioms Zeta7Main.qExpansionUSeven

#check @Zeta7Main.qExpansionUSeven_eisenstein
#print Zeta7Main.qExpansionUSeven_eisenstein
#print axioms Zeta7Main.qExpansionUSeven_eisenstein

#check @Zeta7Main.eisensteinMinusTwo_coeff_one
#print Zeta7Main.eisensteinMinusTwo_coeff_one
#print axioms Zeta7Main.eisensteinMinusTwo_coeff_one

#check @Zeta7Main.eisensteinMinusTwo_coeff_seven_pow
#print Zeta7Main.eisensteinMinusTwo_coeff_seven_pow
#print axioms Zeta7Main.eisensteinMinusTwo_coeff_seven_pow

#check @Zeta7Main.eisensteinMinusTwo_q_not_weighted_decay
#print Zeta7Main.eisensteinMinusTwo_q_not_weighted_decay
#print axioms Zeta7Main.eisensteinMinusTwo_q_not_weighted_decay

#check @Zeta7Main.eisensteinMinusTwo_nonconstant_norm
#print Zeta7Main.eisensteinMinusTwo_nonconstant_norm
#print axioms Zeta7Main.eisensteinMinusTwo_nonconstant_norm

#check @Zeta7Main.eisensteinMinusTwo_all_coefficients_norm
#print Zeta7Main.eisensteinMinusTwo_all_coefficients_norm
#print axioms Zeta7Main.eisensteinMinusTwo_all_coefficients_norm

#check @Zeta7Main.eisensteinMinusTwo_q_weighted_decay
#print Zeta7Main.eisensteinMinusTwo_q_weighted_decay
#print axioms Zeta7Main.eisensteinMinusTwo_q_weighted_decay

#check @Zeta7Main.eisensteinMinusTwo_q_summable
#print Zeta7Main.eisensteinMinusTwo_q_summable
#print axioms Zeta7Main.eisensteinMinusTwo_q_summable

#check @Zeta7Main.eisensteinMinusTwo_q_hasGaussNorm
#print Zeta7Main.eisensteinMinusTwo_q_hasGaussNorm
#print axioms Zeta7Main.eisensteinMinusTwo_q_hasGaussNorm

/- This only checks the TYPE of the missing scalar continuation statement.
No theorem or assumption of this type is introduced. -/
section MissingSignatureTypeOnly
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩
#check (∀ ρ : ℝ, 0 < ρ → ρ < 49 →
  Filter.Tendsto
    (fun n : ℕ => ‖PowerSeries.coeff n Zeta7Main.HSeries‖ * ρ ^ n)
    Filter.atTop (nhds 0) : Prop)
end MissingSignatureTypeOnly

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let modName := env.header.moduleNames[idx]!
    if (`PadicLFunctions).isPrefixOf modName ||
        (`LeanModularForms).isPrefixOf modName || (`Zeta7Proof).isPrefixOf modName then
      let axioms ← Lean.collectAxioms name
      for ax in axioms do
        unless allowed.contains ax do
          throwError "Unapproved kernel dependency {ax} in {name}"
      count := count + 1
  logInfo m!"ANNULUS AXIOM AUDIT: {count} declarations; all dependencies on the whitelist."

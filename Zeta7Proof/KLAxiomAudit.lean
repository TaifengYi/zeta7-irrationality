import Zeta7Proof.KubotaLeopoldt
import PadicLFunctions.KubotaLeopoldt.ZetaValuesComplex
import Lean.Elab.Print

/-! Kernel-dependency audit of the concrete construction and its imported closure.
The exhaustive command also checks internal helper declarations in each module.
The theorem types below expose the scope of the mathematical hypotheses. -/

#print axioms PadicMeasure.ofPowerSeries
#print axioms PadicMeasure.mahlerLinearEquiv
#print axioms PadicMeasure.muA
#print axioms PadicMeasure.padicZeta
#print axioms PadicMeasure.padicZeta_isPseudoMeasure
#print axioms PadicMeasure.padicZeta_moments
#print axioms PadicMeasure.kubotaLeopoldt
#print axioms PadicLFunctions.zetaPBranch
#print axioms PadicLFunctions.zetaPBranch_interpolation
#print axioms zetaNeg_eq_riemannZeta
#print axioms Zeta7Main.zeta7Three
#print axioms Zeta7Main.branch_four_neg_two_eq_inv_square
#print axioms Zeta7Main.zeta7Three_denominator_ne_zero
#print axioms Zeta7Main.zetaSevenBranch_interpolation_bernoulli
#print axioms Zeta7Main.continuousAt_zetaSevenBranch_three
#print axioms Zeta7Main.bernoulli_approximants_tendsto_zeta7Three

#check @PadicMeasure.kubotaLeopoldt
#check @PadicMeasure.padicZeta_moments
#check @Zeta7Main.zeta7Three_denominator_ne_zero
#check @Zeta7Main.bernoulli_approximants_tendsto_zeta7Three

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let modName := env.header.moduleNames[idx]!
    if (`PadicLFunctions).isPrefixOf modName || modName == `Zeta7Proof.KubotaLeopoldt then
      let axioms ← Lean.collectAxioms name
      for ax in axioms do
        unless allowed.contains ax do
          throwError "Unapproved kernel dependency {ax} in {name}"
      count := count + 1
  logInfo m!"KL EXHAUSTIVE AUDIT: {count} declarations; all dependencies on the whitelist."

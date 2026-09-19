import Zeta7Proof.EisensteinLimit
import Lean.Elab.Print

/-! Kernel closure and explicit-premise audit for the supplied files and
the exact target specialization. Foundational axioms are checked separately
from mathematical hypotheses printed below. -/

#print axioms PadicLFunctions.unitsTwist
#print axioms PadicLFunctions.twistedZetaHalf_witness_eq
#print axioms PadicLFunctions.eisensteinFamily_interpolation
#print axioms HeckeRing.GL2.modularFormLevelRaise
#print axioms HeckeRing.GL2.levelRaiseMatrix_mul_mapGL
#print axioms PadicLFunctions.hasSum_stabilisedEisenstein
#print axioms PadicLFunctions.stabilisedEisenstein
#print axioms PadicLFunctions.stabilisedEisenstein_smul_apply
#print axioms Zeta7Main.seven_product_multipliable
#print axioms Zeta7Main.x_subst_q
#print axioms Zeta7Main.q_subst_x
#print axioms Zeta7Main.ASeries_mul_xSeries
#print axioms Zeta7Main.GSeries_hasSum_lambert
#print axioms Zeta7Main.inverse_cube_twist
#print axioms Zeta7Main.eisenstein_constant_witness
#print axioms Zeta7Main.eisenstein_denominator_ne_zero
#print axioms Zeta7Main.eisensteinMinusTwo_constant
#print axioms Zeta7Main.eisensteinMinusTwo_coeff
#print axioms Zeta7Main.eisensteinMinusTwo_eq_G_add_eta
#print axioms Zeta7Main.eisenstein_constant_evaluation_unique
#print axioms Zeta7Main.target_family_specialization
#print axioms Zeta7Main.classical_constant_tendsto_eta
#print axioms Zeta7Main.classical_coefficients_tendsto

#check @PadicLFunctions.eisensteinFamily_interpolation
#check @PadicLFunctions.twistedZetaHalf_moments
#check @PadicLFunctions.hasSum_stabilisedEisenstein
#check @PadicLFunctions.stabilisedEisenstein_smul_apply
#check @Zeta7Main.GSeries_hasSum_lambert
#check @Zeta7Main.eisensteinMinusTwo_eq_G_add_eta
#check @Zeta7Main.eisenstein_constant_evaluation_unique
#check @Zeta7Main.target_family_specialization
#check @Zeta7Main.classical_coefficients_tendsto

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
  logInfo m!"EISENSTEIN EXHAUSTIVE AUDIT: {count} declarations; all dependencies on the whitelist."

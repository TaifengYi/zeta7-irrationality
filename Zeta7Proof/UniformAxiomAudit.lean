import Zeta7Proof.UniformEndpoints
import Lean.Elab.Print

/-! Both explicit theorem types and full kernel dependency closures are checked.
The new Serre presentation has no unproved convergence or modularity premise. -/

#print axioms Zeta7UniformTopology.uniformSpace
#print axioms Zeta7UniformTopology.tendsto_iff_tendstoUniformly
#print axioms rationalModularForms
#print axioms pAdicModularFormStruct
#print axioms PowerSeries.isPAdicModularForm
#print axioms PadicLFunctions.rjw_normalisation
#print axioms Zeta7Main.serreWeight_ge_four
#print axioms Zeta7Main.serreWeight_even
#print axioms Zeta7Main.serreWeight_exponent_ge
#print axioms Zeta7Main.serreWeight_weightSpace_tendsto
#print axioms Zeta7Main.serreWeight_characters_tendsto
#print axioms Zeta7Main.seven_unit_power_dvd
#print axioms Zeta7Main.seven_unit_power_valuation
#print axioms Zeta7Main.seven_unit_inverse_cube_error
#print axioms Zeta7Main.seven_nonunit_power_valuation
#print axioms Zeta7Main.classical_nonconstant_uniform_norm
#print axioms Zeta7Main.classical_nonconstant_uniform_valuation
#print axioms Zeta7Main.classical_nonconstant_all_precisions
#print axioms Zeta7Main.serre_euler_factor_ne_zero
#print axioms Zeta7Main.full_constant_eq_stabilised_div
#print axioms Zeta7Main.full_classical_constant_tendsto_eta
#print axioms Zeta7Main.classical_all_coefficients_norm
#print axioms Zeta7Main.classical_eisenstein_tendstoUniformly
#print axioms Zeta7Main.classical_eisenstein_tendsto_uniform_topology
#print axioms Zeta7Main.classicalEisensteinForm_qExpansion
#print axioms Zeta7Main.classicalEisensteinForm_apply
#print axioms Zeta7Main.classicalRationalEisenstein_qExpansion
#print axioms Zeta7Main.eisensteinMinusTwo_serrePresentation
#print axioms Zeta7Main.eisensteinMinusTwo_isPAdicModularForm
#print axioms Zeta7Main.serre_weight_characters_tendstoUniformly
#print axioms Zeta7Main.classical_all_coefficients_all_precisions
#print axioms Zeta7Main.original_classical_coefficients_tendstoUniformly
#print axioms Zeta7Main.target_G_add_eta_isPAdicModularForm

#check @Zeta7UniformTopology.tendsto_iff_tendstoUniformly
#check @Zeta7Main.serreWeight_weightSpace_tendsto
#check @Zeta7Main.serreWeight_characters_tendsto
#check @Zeta7Main.seven_unit_power_dvd
#check @Zeta7Main.seven_unit_power_valuation
#check @Zeta7Main.seven_nonunit_power_valuation
#check @Zeta7Main.classical_nonconstant_uniform_norm
#check @Zeta7Main.classical_nonconstant_all_precisions
#check @Zeta7Main.full_classical_constant_tendsto_eta
#check @Zeta7Main.classical_all_coefficients_norm
#check @Zeta7Main.classical_eisenstein_tendstoUniformly
#check @Zeta7Main.classical_eisenstein_tendsto_uniform_topology
#check @Zeta7Main.classicalEisensteinForm_qExpansion
#check @Zeta7Main.classicalEisensteinForm_apply
#check @Zeta7Main.classicalRationalEisenstein_qExpansion
#check @Zeta7Main.eisensteinMinusTwo_serrePresentation
#check @Zeta7Main.eisensteinMinusTwo_isPAdicModularForm
#check @Zeta7Main.serre_weight_characters_tendstoUniformly
#check @Zeta7Main.classical_all_coefficients_all_precisions
#check @Zeta7Main.original_classical_coefficients_tendstoUniformly
#check @Zeta7Main.target_G_add_eta_isPAdicModularForm
#print PowerSeries.isModularForm
#print pAdicModularFormStruct
#print PowerSeries.isPAdicModularForm
#print Zeta7Main.classicalRationalEisenstein
#print Zeta7Main.eisensteinMinusTwo_serrePresentation

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
      logInfo m!"KERNEL CLOSURE {name}: {axioms.toList}"
      count := count + 1
  logInfo m!"UNIFORM EXHAUSTIVE AUDIT: {count} declarations; all dependencies on the whitelist."

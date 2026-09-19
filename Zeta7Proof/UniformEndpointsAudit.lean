import Zeta7Proof.UniformEndpoints
import Lean.Elab.Print

/-! Kernel and explicit-premise audit of the uniform continuation endpoints. -/

#print axioms Zeta7Main.serre_unit_power_norm
#print axioms Zeta7Main.serre_weight_character_uniform_norm
#print axioms Zeta7Main.serre_weight_characters_tendstoUniformly
#print axioms Zeta7Main.classical_all_coefficients_all_precisions
#print axioms Zeta7Main.stabilised_nonconstant_uniform_norm
#print axioms Zeta7Main.stabilised_eisenstein_tendstoUniformly
#print axioms Zeta7Main.original_classical_coefficients_tendstoUniformly
#print axioms Zeta7Main.target_G_add_eta_isPAdicModularForm
#print axioms Zeta7Main.eisensteinMinusTwo_serrePresentation

#check @Zeta7Main.serre_unit_power_norm
#check @Zeta7Main.serre_weight_character_uniform_norm
#check @Zeta7Main.serre_weight_characters_tendstoUniformly
#check @Zeta7Main.classical_all_coefficients_all_precisions
#check @Zeta7Main.stabilised_nonconstant_uniform_norm
#check @Zeta7Main.stabilised_eisenstein_tendstoUniformly
#check @Zeta7Main.original_classical_coefficients_tendstoUniformly
#check @Zeta7Main.target_G_add_eta_isPAdicModularForm

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
  logInfo m!"UNIFORM ENDPOINT AUDIT: {count} declarations; all dependencies on the whitelist."

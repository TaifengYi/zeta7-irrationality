import Zeta7Proof.AuxiliaryThirdLayer
import Zeta7Proof.AuxiliaryPrimitiveLayers
import Zeta7Proof.AuxiliarySimultaneousCounts
import Zeta7Proof.AuxiliaryEstimateStatement
import Lean

/-! Full types and transitive-axiom audit for every declaration in this increment. -/
set_option pp.proofs false
set_option pp.universes true
set_option pp.explicit true
set_option pp.deepTerms false
set_option pp.maxSteps 100000

set_option maxHeartbeats 0 in
-- Traverse and audit the complete declaration set, including generated helpers.
open Lean Elab Command in
run_cmd do
  let modules := #[`Zeta7Proof.AuxiliaryLambertDepletion, `Zeta7Proof.AuxiliaryActualDepletion,
    `Zeta7Proof.AuxiliaryResidueCalculus, `Zeta7Proof.AuxiliaryThirdLayer,
    `Zeta7Proof.AuxiliaryPrimitiveLayers, `Zeta7Proof.AuxiliarySimultaneousCounts,
    `Zeta7Proof.AuxiliaryEstimateStatement]
  let foundations := #[``propext, ``Classical.choice, ``Quot.sound]
  let env ← getEnv
  let mut names : Array Name := #[]
  for idx in [:env.header.moduleNames.size] do
    let moduleName := env.header.moduleNames[idx]!
    unless modules.contains moduleName do continue
    let data := env.header.moduleData[idx]!
    for name in data.constNames ++ data.extraConstNames do
      if names.contains name then continue
      let some info := env.find? name | continue
      names := names.push name
      if let .axiomInfo _ := info then throwError "New mathematical axiom: {name}"
      elabCommand (← `(command| #check @$(mkIdent name)))
      elabCommand (← `(command| #print $(mkIdent name)))
      elabCommand (← `(command| #print axioms $(mkIdent name)))
      let axs ← Lean.collectAxioms name
      for ax in axs do
        unless foundations.contains ax do
          throwError "Unexpected transitive axiom {ax} in {name}"
      logInfo ("AUXILIARY_LAYERS_AXIOM_JSON " ++ (Json.mkObj [
        ("name", toJson name.toString), ("module", toJson moduleName.toString),
        ("axioms", toJson (axs.toList.map Name.toString))]).compress)
  logInfo m!"AUXILIARY LAYERS AUDIT PASSED: {names.size} declarations."

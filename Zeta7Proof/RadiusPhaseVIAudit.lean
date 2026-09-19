import Zeta7Proof.Radius49Bridge
import Zeta7Proof.Radius49Tube
import Zeta7Proof.Radius49USeven
import Lean

/-! Transitive-axiom audit of the Phase VI radius-internalization modules (R1, R2, R3-formal).
Every declaration may use only `propext`, `Classical.choice` and `Quot.sound`; in particular
none may use `Zeta7Main.published_radius49_geometric_continuation`. -/
set_option pp.proofs false

#check @Zeta7Main.hasRadius49_of_HSeries_decay
#print axioms Zeta7Main.hasRadius49_of_HSeries_decay
#check @Zeta7Main.hasRadius49_of_valueGroup_decay
#print axioms Zeta7Main.hasRadius49_of_valueGroup_decay
#check @Zeta7Main.hasRadius49_iff_HSeries_decay
#print axioms Zeta7Main.hasRadius49_iff_HSeries_decay
#check @Zeta7Radius49.exists_discAlgebra_of_decay
#print axioms Zeta7Radius49.exists_discAlgebra_of_decay
#check @Zeta7Radius49.supersingular_tube
#print axioms Zeta7Radius49.supersingular_tube
#check @Zeta7Radius49.reduced_model_supersingular
#print axioms Zeta7Radius49.reduced_model_supersingular
#check @Zeta7Main.uSeven_eisensteinMinusTwo
#print axioms Zeta7Main.uSeven_eisensteinMinusTwo

set_option maxHeartbeats 0 in
open Lean Elab Command in
run_cmd do
  let modules := #[`Zeta7Proof.Radius49Bridge, `Zeta7Proof.Radius49Tube,
    `Zeta7Proof.Radius49USeven]
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
      let axs ← Lean.collectAxioms name
      for ax in axs do
        unless foundations.contains ax do
          throwError "Unexpected transitive axiom {ax} in {name}"
  logInfo m!"PHASE VI AUDIT PASSED: {names.size} declarations."

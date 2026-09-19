import Zeta7Proof.FinalTheorem
import Zeta7Proof.ArchC3Audit
import Lean

/-! Full types and transitive-axiom audit for the completion of C, the six-circle energy bound,
the kernel-checked numerical margin and the final irrationality theorems, including generated
helpers. The earlier C1/C2/C3 audits are imported unchanged.

Every declaration of the new modules, including `FinalConditional` and `FinalTheorem`, may use
only `propext`, `Classical.choice` and `Quot.sound`. The radius input is the internal theorem
`Zeta7Main.internal_radius49_geometric_continuation`; no other axiom is admitted. -/
set_option pp.proofs false
set_option pp.universes true
set_option pp.explicit true
set_option pp.deepTerms false
set_option pp.maxSteps 100000

#check @Zeta7Main.zeta7Three_irrational
#print axioms Zeta7Main.zeta7Three_irrational
#check @Zeta7Main.eta_irrational
#print axioms Zeta7Main.eta_irrational
#check @Zeta7Main.c_theorem_explicit
#print axioms Zeta7Main.c_theorem_explicit
#check @Zeta7Arch.c30
#print axioms Zeta7Arch.c30
#check @Zeta7Arch.c_theorem
#print axioms Zeta7Arch.c_theorem
#check @Zeta7Arch.gram_det_re_pos
#print axioms Zeta7Arch.gram_det_re_pos
#check @Zeta7Valence.energyI_le_explicitI
#print axioms Zeta7Valence.energyI_le_explicitI
#check @Zeta7Cert.surplusS_gt
#print axioms Zeta7Cert.surplusS_gt
#print axioms Zeta7Auxiliary.actualAuxiliaryEstimate
#print axioms Zeta7Cert.log_seven_lt_two

set_option maxHeartbeats 0 in
-- Traverse and audit the complete declaration set, including generated helpers.
open Lean Elab Command in
run_cmd do
  let modules := #[`Zeta7Proof.ArchC30, `Zeta7Proof.ArchCTheorem, `Zeta7Proof.CertArctan,
    `Zeta7Proof.CertEnergyDefs, `Zeta7Proof.CertEnergyTerms, `Zeta7Proof.CertEnergyPairs,
    `Zeta7Proof.CertSurplus, `Zeta7Proof.ValenceWeierstrass, `Zeta7Proof.LevelSevenE6Quotient,
    `Zeta7Proof.LevelSevenFunctionIdentities, `Zeta7Proof.ValenceLattice,
    `Zeta7Proof.ValenceGeneric, `Zeta7Proof.ValenceQDisc, `Zeta7Proof.ValenceCosets,
    `Zeta7Proof.ValenceJensen, `Zeta7Proof.ValenceIntegral, `Zeta7Proof.EnergyCircle,
    `Zeta7Proof.EnergyOrbit, `Zeta7Proof.EnergyUpper, `Zeta7Proof.FinalConditional,
    `Zeta7Proof.FinalTheorem]
  let radiusModules : Array Name := #[]
  let foundations := #[``propext, ``Classical.choice, ``Quot.sound]
  let radius := `Zeta7Main.published_radius49_geometric_continuation
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
      elabCommand (← `(command| #print axioms $(mkIdent name)))
      let axs ← Lean.collectAxioms name
      for ax in axs do
        let ok := foundations.contains ax || (ax == radius && radiusModules.contains moduleName)
        unless ok do
          throwError "Unexpected transitive axiom {ax} in {name}"
      logInfo ("FINAL_AXIOM_JSON " ++ (Json.mkObj [
        ("name", toJson name.toString), ("module", toJson moduleName.toString),
        ("axioms", toJson (axs.toList.map Name.toString))]).compress)
  logInfo m!"FINAL AUDIT PASSED: {names.size} declarations."

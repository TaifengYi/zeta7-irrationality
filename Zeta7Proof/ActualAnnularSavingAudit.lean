import Zeta7Proof.ActualAnnularTargetBridge
import Zeta7Proof.AuxiliaryEisensteinCongruence
import Lean

/-! Exact types and complete transitive axiom audit of the actual annular saving. -/
set_option pp.proofs false
set_option pp.universes true
set_option pp.deepTerms false
set_option pp.maxSteps 100000

set_option maxHeartbeats 0 in
open Lean Elab Command in
run_cmd do
  let modules := #[`Zeta7Proof.AnnularPowerSeriesTransport,
    `Zeta7Proof.AnnularOppositeTarget,
    `Zeta7Proof.AnnularOppositeEquation,
    `Zeta7Proof.AnnularActualConcomitant,
    `Zeta7Proof.AnnularReflectionCompatibility,
    `Zeta7Proof.AnnularActualLaurentRelation,
    `Zeta7Proof.AnnularActualColumnIdentity,
    `Zeta7Proof.AnnularCompletedMatrix,
    `Zeta7Proof.AnnularDeterminantLogBound,
    `Zeta7Proof.ActualAnnularSaving,
    `Zeta7Proof.ActualAnnularTargetBridge, `Zeta7Proof.AuxiliaryEisensteinCongruence]
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
      elabCommand (← `(command| #print $(mkIdent name)))
      elabCommand (← `(command| #print axioms $(mkIdent name)))
      let axs ← Lean.collectAxioms name
      for ax in axs do
        unless foundations.contains ax ||
            (moduleName != `Zeta7Proof.AnnularPowerSeriesTransport &&
              moduleName != `Zeta7Proof.AuxiliaryEisensteinCongruence && ax == radius) do
          throwError "Unexpected transitive axiom {ax} in {name}"
      logInfo ("ACTUAL_ANNULAR_SAVING_AXIOM_JSON " ++ (Json.mkObj [
        ("name", toJson name.toString), ("module", toJson moduleName.toString),
        ("axioms", toJson (axs.toList.map Name.toString))]).compress)
  logInfo m!"ACTUAL ANNULAR SAVING AUDIT PASSED: {names.size} declarations."

#check @Zeta7Annulus.actualAnnularLaurentRelation_above
#print Zeta7Annulus.actualAnnularLaurentRelation_above
#print axioms Zeta7Annulus.actualAnnularLaurentRelation_above
#check @Zeta7Annulus.actualSourceColumn_image
#print Zeta7Annulus.actualSourceColumn_image
#print axioms Zeta7Annulus.actualSourceColumn_image
#check @Zeta7Annulus.actualNormalizedDeterminant_log_bound
#print Zeta7Annulus.actualNormalizedDeterminant_log_bound
#print axioms Zeta7Annulus.actualNormalizedDeterminant_log_bound
#check @Zeta7Annulus.actualNormalizedDeterminant_annular_bound
#print Zeta7Annulus.actualNormalizedDeterminant_annular_bound
#print axioms Zeta7Annulus.actualNormalizedDeterminant_annular_bound
#check @Zeta7Annulus.actualCommonDeterminant_annular_saving
#print Zeta7Annulus.actualCommonDeterminant_annular_saving
#print axioms Zeta7Annulus.actualCommonDeterminant_annular_saving
#check @Zeta7Common.actual_annular_family_of_rationality
#print Zeta7Common.actual_annular_family_of_rationality
#print axioms Zeta7Common.actual_annular_family_of_rationality
#check @Zeta7Main.HasRadius49GeometricContinuation
#print Zeta7Main.HasRadius49GeometricContinuation
#print axioms Zeta7Main.HasRadius49GeometricContinuation
#check @Zeta7Main.HSeries_radius49
#print Zeta7Main.HSeries_radius49
#print axioms Zeta7Main.HSeries_radius49

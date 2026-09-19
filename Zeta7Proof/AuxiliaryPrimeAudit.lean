import Zeta7Proof.AuxiliaryActualLowRows
import Zeta7Proof.AuxiliaryLayerMap
import Zeta7Proof.AuxiliaryAPIProbe
import Zeta7Proof.ActualAnnularSaving
import Lean

/-! Complete declaration and transitive-axiom audit for the auxiliary-prime increment. -/
set_option pp.proofs false
set_option pp.universes true
set_option pp.deepTerms false
set_option pp.maxSteps 100000

set_option maxHeartbeats 0 in
open Lean Elab Command in
run_cmd do
  let modules := #[`Zeta7Proof.AuxiliaryCaps, `Zeta7Proof.AuxiliaryThresholdCount,
    `Zeta7Proof.AuxiliaryDeterminantBound, `Zeta7Proof.AuxiliaryActualRows,
    `Zeta7Proof.AuxiliaryLayerMap, `Zeta7Proof.AuxiliaryLambertCaps,
    `Zeta7Proof.AuxiliaryIntegralCoordinates, `Zeta7Proof.AuxiliaryTransportCaps,
    `Zeta7Proof.AuxiliaryActualGermCaps, `Zeta7Proof.AuxiliaryActualDeterminantBound,
    `Zeta7Proof.AuxiliaryActualLowRows]
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
      logInfo ("AUXILIARY_PRIME_AXIOM_JSON " ++ (Json.mkObj [
        ("name", toJson name.toString), ("module", toJson moduleName.toString),
        ("axioms", toJson (axs.toList.map Name.toString))]).compress)
  logInfo m!"AUXILIARY PRIME AUDIT PASSED: {names.size} declarations."

#check @Zeta7Auxiliary.actual_first_three_caps
#print Zeta7Auxiliary.actual_first_three_caps
#print axioms Zeta7Auxiliary.actual_first_three_caps
#check @Zeta7Auxiliary.rationalK_cap_four
#print Zeta7Auxiliary.rationalK_cap_four
#print axioms Zeta7Auxiliary.rationalK_cap_four
#check @Zeta7Auxiliary.actual_germs_cap_zero
#print Zeta7Auxiliary.actual_germs_cap_zero
#print axioms Zeta7Auxiliary.actual_germs_cap_zero
#check @Zeta7Auxiliary.actualCommonDeterminant_bound_of_compatible_caps
#print Zeta7Auxiliary.actualCommonDeterminant_bound_of_compatible_caps
#print axioms Zeta7Auxiliary.actualCommonDeterminant_bound_of_compatible_caps
#check @Zeta7Auxiliary.actualCommonDeterminant_valuation_large_prime
#print Zeta7Auxiliary.actualCommonDeterminant_valuation_large_prime
#print axioms Zeta7Auxiliary.actualCommonDeterminant_valuation_large_prime
#check @Zeta7Main.HasRadius49GeometricContinuation
#print Zeta7Main.HasRadius49GeometricContinuation
#print axioms Zeta7Main.HasRadius49GeometricContinuation
#check @Zeta7Main.HSeries_radius49
#print Zeta7Main.HSeries_radius49
#print axioms Zeta7Main.HSeries_radius49
#check @Zeta7Annulus.actualCommonDeterminant_annular_saving
#print axioms Zeta7Annulus.actualCommonDeterminant_annular_saving

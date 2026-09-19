import Zeta7Proof.ArchC1Endpoint
import Zeta7Proof.AuxiliaryEstimateAudit
import Zeta7Proof.CertLogSeven
import Lean

/-! Full types and transitive-axiom audit for every declaration of the C1 potential theory
(sublevel sets, local multiplicity, small-ball estimate, the actual six-circle measure, tail
bound, continuity and finite energy), of C2 (modulus of continuity, area submean, (40), boundary
estimate, (41) for the adapted flag vectors), of the C3 Gram/Vandermonde identity (42), the
diagonal-corrected empirical bound (44) and the Gram bound, and of the preserved certificate
`Zeta7Cert.log_seven_lt_two`, including generated helpers. -/
set_option pp.proofs false
set_option pp.universes true
set_option pp.explicit true
set_option pp.deepTerms false
set_option pp.maxSteps 100000

/-- `P` is unchanged. -/
example : Zeta7Auxiliary.ActualAuxiliaryEstimate := Zeta7Auxiliary.actualAuxiliaryEstimate

#check @Zeta7Auxiliary.actualAuxiliaryEstimate
#print axioms Zeta7Auxiliary.actualAuxiliaryEstimate
#check @Zeta7Cert.log_seven_lt_two
#print axioms Zeta7Cert.log_seven_lt_two
#check @Zeta7Arch.c1_endpoint
#print axioms Zeta7Arch.c1_endpoint
#check @Zeta7Arch.potentialMeasure_small_ball
#print axioms Zeta7Arch.potentialMeasure_small_ball
#check @Zeta7Arch.weighted_submean
#print axioms Zeta7Arch.weighted_submean
#check @Zeta7Arch.boundary_bound
#print axioms Zeta7Arch.boundary_bound
#check @Zeta7Arch.actualDeterminant_adapted_coefficient_bound
#print axioms Zeta7Arch.actualDeterminant_adapted_coefficient_bound
#check @Zeta7Arch.gram_det_eq_integral_density
#print axioms Zeta7Arch.gram_det_eq_integral_density
#check @Zeta7Arch.gram_det_le
#print axioms Zeta7Arch.gram_det_le

set_option maxHeartbeats 0 in
-- Traverse and audit the complete declaration set, including generated helpers.
open Lean Elab Command in
run_cmd do
  let modules := #[`Zeta7Proof.ArchSublevel, `Zeta7Proof.ArchCircleAnalytic,
    `Zeta7Proof.ArchCircleSmallBall, `Zeta7Proof.ArchCircleMeasure, `Zeta7Proof.ArchPotentialTail,
    `Zeta7Proof.ArchPotential, `Zeta7Proof.ArchModulus, `Zeta7Proof.ArchSubmean,
    `Zeta7Proof.ArchBoundary, `Zeta7Proof.ArchC2Endpoint, `Zeta7Proof.ArchAndreief,
    `Zeta7Proof.ArchGramVandermonde, `Zeta7Proof.ArchEmpirical, `Zeta7Proof.ArchC1Endpoint,
    `Zeta7Proof.CertLogSeven]
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
      elabCommand (← `(command| #print axioms $(mkIdent name)))
      let axs ← Lean.collectAxioms name
      for ax in axs do
        unless foundations.contains ax do
          throwError "Unexpected transitive axiom {ax} in {name}"
      logInfo ("ARCH_POTENTIAL_AXIOM_JSON " ++ (Json.mkObj [
        ("name", toJson name.toString), ("module", toJson moduleName.toString),
        ("axioms", toJson (axs.toList.map Name.toString))]).compress)
  logInfo m!"ARCH POTENTIAL AUDIT PASSED: {names.size} declarations."

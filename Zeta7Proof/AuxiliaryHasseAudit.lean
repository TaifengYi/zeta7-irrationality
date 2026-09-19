import Zeta7Proof.AuxiliaryHasseFrobenius
import Zeta7Proof.ActualAnnularSaving
import Lean

/-! Exact types and exhaustive transitive-axiom checks for the Hasse quotient increment. -/
set_option pp.proofs false
set_option pp.universes true
set_option pp.deepTerms false
set_option pp.maxSteps 100000

set_option maxHeartbeats 0 in
open Lean Elab Command in
run_cmd do
  let modules := #[`Zeta7Proof.AuxiliaryLevelOneGeneration,
    `Zeta7Proof.AuxiliaryQuotientPolynomials, `Zeta7Proof.AuxiliaryActualE6Quotient,
    `Zeta7Proof.AuxiliaryClearedExpansion, `Zeta7Proof.AuxiliaryRationalHasseQuotient,
    `Zeta7Proof.AuxiliaryIntegralHasseQuotient, `Zeta7Proof.AuxiliaryHasseReduction,
    `Zeta7Proof.AuxiliaryHasseFrobenius]
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
      logInfo ("AUXILIARY_HASSE_AXIOM_JSON " ++ (Json.mkObj [
        ("name", toJson name.toString), ("module", toJson moduleName.toString),
        ("axioms", toJson (axs.toList.map Name.toString))]).compress)
  logInfo m!"AUXILIARY HASSE AUDIT PASSED: {names.size} declarations."

#check @Zeta7Auxiliary.integralQuotientPolynomial_identity
#print Zeta7Auxiliary.integralQuotientPolynomial_identity
#print axioms Zeta7Auxiliary.integralQuotientPolynomial_identity
#check @Zeta7Auxiliary.integralQuotientPolynomial_degree
#print Zeta7Auxiliary.integralQuotientPolynomial_degree
#print axioms Zeta7Auxiliary.integralQuotientPolynomial_degree
#check @Zeta7Auxiliary.integralQuotientPolynomial_lead
#print Zeta7Auxiliary.integralQuotientPolynomial_lead
#print axioms Zeta7Auxiliary.integralQuotientPolynomial_lead
#check @Zeta7Auxiliary.reducedB_expansion_cleared
#print Zeta7Auxiliary.reducedB_expansion_cleared
#print axioms Zeta7Auxiliary.reducedB_expansion_cleared
#check @Zeta7Auxiliary.reducedB_logarithmic_derivative
#print Zeta7Auxiliary.reducedB_logarithmic_derivative
#print axioms Zeta7Auxiliary.reducedB_logarithmic_derivative
#check @Zeta7Main.HasRadius49GeometricContinuation
#print Zeta7Main.HasRadius49GeometricContinuation
#print axioms Zeta7Main.HasRadius49GeometricContinuation
#check @Zeta7Main.HSeries_radius49
#print Zeta7Main.HSeries_radius49
#print axioms Zeta7Main.HSeries_radius49
#check @Zeta7Annulus.actualCommonDeterminant_annular_saving
#print axioms Zeta7Annulus.actualCommonDeterminant_annular_saving

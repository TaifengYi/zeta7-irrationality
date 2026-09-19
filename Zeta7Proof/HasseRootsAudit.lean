import Zeta7Proof.ActualHasseRoots
import Zeta7Proof.ActualHasseCartier
import Zeta7Proof.AuxiliaryPrimitiveCaps
import Zeta7Proof.ActualAnnularSaving
import Lean

/-! Exhaustive type and transitive-axiom audit for the roots/Cartier increment. -/
set_option pp.proofs false
set_option pp.universes true
set_option pp.deepTerms false
set_option pp.maxSteps 100000

set_option maxHeartbeats 0 in
open Lean Elab Command in
run_cmd do
  let modules := #[`Zeta7Proof.HasseIndicial, `Zeta7Proof.HasseReducedRiccati,
    `Zeta7Proof.HasseClearingCalculus, `Zeta7Proof.HassePolynomialEquation,
    `Zeta7Proof.HasseResidueArithmetic, `Zeta7Proof.HassePolynomialRoots,
    `Zeta7Proof.ActualHasseRoots, `Zeta7Proof.ActualHasseCartier,
    `Zeta7Proof.AuxiliaryPrimitiveCaps]
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
      logInfo ("HASSE_ROOTS_AXIOM_JSON " ++ (Json.mkObj [
        ("name", toJson name.toString), ("module", toJson moduleName.toString),
        ("axioms", toJson (axs.toList.map Name.toString))]).compress)
  logInfo m!"HASSE ROOTS AUDIT PASSED: {names.size} declarations."

#check @Zeta7Auxiliary.reducedQuotient_degree
#print axioms Zeta7Auxiliary.reducedQuotient_degree
#check @Zeta7Auxiliary.reducedQuotient_coprime
#print Zeta7Auxiliary.reducedQuotient_coprime
#print axioms Zeta7Auxiliary.reducedQuotient_coprime
#check @Zeta7Auxiliary.reducedQuotient_squarefree
#print Zeta7Auxiliary.reducedQuotient_squarefree
#print axioms Zeta7Auxiliary.reducedQuotient_squarefree
#check @Zeta7Auxiliary.rationalD_zero_iff_frobenius
#print Zeta7Auxiliary.rationalD_zero_iff_frobenius
#print axioms Zeta7Auxiliary.rationalD_zero_iff_frobenius
#check @Zeta7Auxiliary.cartierRational_frobenius_mul
#print Zeta7Auxiliary.cartierRational_frobenius_mul
#print axioms Zeta7Auxiliary.cartierRational_frobenius_mul
#check @Zeta7Auxiliary.cartierRational_euler
#print Zeta7Auxiliary.cartierRational_euler
#print axioms Zeta7Auxiliary.cartierRational_euler
#check @Zeta7Auxiliary.cartierRational_hasseGamma_inverse
#print Zeta7Auxiliary.cartierRational_hasseGamma_inverse
#print axioms Zeta7Auxiliary.cartierRational_hasseGamma_inverse
#check @Zeta7Auxiliary.hasseOperatorRational_kernel
#print Zeta7Auxiliary.hasseOperatorRational_kernel
#print axioms Zeta7Auxiliary.hasseOperatorRational_kernel
#check @Zeta7Auxiliary.hasseOperatorRational_polynomial_degree
#print Zeta7Auxiliary.hasseOperatorRational_polynomial_degree
#print axioms Zeta7Auxiliary.hasseOperatorRational_polynomial_degree
#check @Zeta7Auxiliary.hasseCarryPolynomial_fraction
#print axioms Zeta7Auxiliary.hasseCarryPolynomial_fraction
#check @Zeta7Auxiliary.rationalJ1_cap_four
#print axioms Zeta7Auxiliary.rationalJ1_cap_four
#check @Zeta7Auxiliary.rationalJ2_cap_four
#print axioms Zeta7Auxiliary.rationalJ2_cap_four
#check @Zeta7Auxiliary.actualCommonDeterminant_ordinary_caps
#print Zeta7Auxiliary.actualCommonDeterminant_ordinary_caps
#print axioms Zeta7Auxiliary.actualCommonDeterminant_ordinary_caps
#check @Zeta7Main.HasRadius49GeometricContinuation
#print Zeta7Main.HasRadius49GeometricContinuation
#print axioms Zeta7Main.HasRadius49GeometricContinuation
#check @Zeta7Main.HSeries_radius49
#print axioms Zeta7Main.HSeries_radius49
#check @Zeta7Annulus.actualCommonDeterminant_annular_saving
#print axioms Zeta7Annulus.actualCommonDeterminant_annular_saving

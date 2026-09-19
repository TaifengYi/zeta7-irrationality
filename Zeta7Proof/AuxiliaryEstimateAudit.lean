import Zeta7Proof.AuxiliaryEstimateProof
import Zeta7Proof.AuxiliaryCommonDenominator
import Zeta7Proof.ArchWeightedGram
import Zeta7Proof.ArchPulledSource
import Lean

/-! Full types and transitive-axiom audit for every declaration of the P8 completion
(exact profile, uniform error, general denominators, the ported weak prime number theorem,
the weighted prime sum and `ActualAuxiliaryEstimate`) and of the first Archimedean (C)
endpoints, including generated helpers. -/
set_option pp.proofs false
set_option pp.universes true
set_option pp.explicit true
set_option pp.deepTerms false
set_option pp.maxSteps 100000

/-- The exact endpoint type: the unchanged proposition for the unchanged determinant. -/
example : Zeta7Auxiliary.ActualAuxiliaryEstimate = ∀ c : ℚ, ∀ ε : ℝ, 0 < ε →
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
      Zeta7ProductFormula.auxiliary (Zeta7Common.actualCommonDeterminant d c) ≤
        (12325/168 + ε) * (d : ℝ)^2 := rfl

example : Zeta7Auxiliary.ActualAuxiliaryEstimate := Zeta7Auxiliary.actualAuxiliaryEstimate

#print Zeta7Auxiliary.ActualAuxiliaryEstimate
#print Zeta7Common.actualCommonDeterminant
#check @Zeta7Auxiliary.actualAuxiliaryEstimate
#print axioms Zeta7Auxiliary.actualAuxiliaryEstimate
#check @Zeta7Arch.actualDeterminant_gram_representation
#print axioms Zeta7Arch.actualDeterminant_gram_representation
#check @Zeta7Arch.actualDeterminant_weighted_representation
#print axioms Zeta7Arch.actualDeterminant_weighted_representation
#check @Zeta7Arch.flag_leading_jensen
#print axioms Zeta7Arch.flag_leading_jensen
#check @Zeta7Arch.cleared_germs_holomorphic
#print axioms Zeta7Arch.cleared_germs_holomorphic
#check @Zeta7Auxiliary.actualCommonDeterminant_common_denominator
#print axioms Zeta7Auxiliary.actualCommonDeterminant_common_denominator
#check @Zeta7PNT.WeakPNT
#print axioms Zeta7PNT.WeakPNT

set_option maxHeartbeats 0 in
-- Traverse and audit the complete declaration set, including generated helpers.
open Lean Elab Command in
run_cmd do
  let modules := #[`Zeta7Proof.AuxiliaryProfile, `Zeta7Proof.AuxiliaryProfileError,
    `Zeta7Proof.AuxiliaryDenominatorBound, `Zeta7Proof.AuxiliaryCommonDenominator,
    `Zeta7Proof.AuxiliaryProfileSum,
    `Zeta7Proof.AuxiliaryEstimateProof,
    `Zeta7Proof.PNT.Asymptotics, `Zeta7Proof.PNT.SmoothExistence, `Zeta7Proof.PNT.Sobolev,
    `Zeta7Proof.PNT.Fourier, `Zeta7Proof.PNT.Wiener1, `Zeta7Proof.PNT.Wiener2,
    `Zeta7Proof.PNT.Wiener3, `Zeta7Proof.PNT.Wiener4, `Zeta7Proof.PNT.ThetaAsymptotic,
    `Zeta7Proof.ArchTempered, `Zeta7Proof.ArchQPullback, `Zeta7Proof.ArchGramDeterminant,
    `Zeta7Proof.ArchSourceFlag, `Zeta7Proof.ArchPulledSource, `Zeta7Proof.ArchWeightedGram]
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
      logInfo ("AUXILIARY_ESTIMATE_AXIOM_JSON " ++ (Json.mkObj [
        ("name", toJson name.toString), ("module", toJson moduleName.toString),
        ("axioms", toJson (axs.toList.map Name.toString))]).compress)
  logInfo m!"AUXILIARY ESTIMATE AUDIT PASSED: {names.size} declarations."

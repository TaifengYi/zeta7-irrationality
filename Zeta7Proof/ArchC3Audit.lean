import Zeta7Proof.ArchC3Endpoint
import Zeta7Proof.ArchPotentialAudit
import Lean

/-! Full types and transitive-axiom audit for every declaration of the C3 energy theory:
Gaussian positive definiteness, the regularized logarithm, the conditionally negative definite
kernel `L_t`, the energy inequality (43) and the Gram limsup (45), including generated helpers.
The C1/C2 audit `ArchPotentialAudit` (which also re-audits `Zeta7Cert.log_seven_lt_two`) is
imported unchanged. -/
set_option pp.proofs false
set_option pp.universes true
set_option pp.explicit true
set_option pp.deepTerms false
set_option pp.maxSteps 100000

/-- `P` is unchanged. -/
example : Zeta7Auxiliary.ActualAuxiliaryEstimate := Zeta7Auxiliary.actualAuxiliaryEstimate

#print axioms Zeta7Auxiliary.actualAuxiliaryEstimate
#print axioms Zeta7Cert.log_seven_lt_two
#check @Zeta7Arch.gauss_pd
#print axioms Zeta7Arch.gauss_pd
#check @Zeta7Arch.regPhi_gauss_mix
#print axioms Zeta7Arch.regPhi_gauss_mix
#check @Zeta7Arch.regL_cnd
#print axioms Zeta7Arch.regL_cnd
#check @Zeta7Arch.energyI_le_regEnergy
#print axioms Zeta7Arch.energyI_le_regEnergy
#check @Zeta7Arch.regPot_sub_le
#print axioms Zeta7Arch.regPot_sub_le
#check @Zeta7Arch.empiricalEnergy_le
#print axioms Zeta7Arch.empiricalEnergy_le
#check @Zeta7Arch.gram_limsup
#print axioms Zeta7Arch.gram_limsup
#check @Zeta7Arch.gram_limsup_log
#print axioms Zeta7Arch.gram_limsup_log
#check @Zeta7Arch.c3_endpoint
#print axioms Zeta7Arch.c3_endpoint

set_option maxHeartbeats 0 in
-- Traverse and audit the complete declaration set, including generated helpers.
open Lean Elab Command in
run_cmd do
  let modules := #[`Zeta7Proof.ArchGaussPD, `Zeta7Proof.ArchRegLog, `Zeta7Proof.ArchRegKernel,
    `Zeta7Proof.ArchEnergyIneq, `Zeta7Proof.ArchC3Endpoint]
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
      logInfo ("ARCH_C3_AXIOM_JSON " ++ (Json.mkObj [
        ("name", toJson name.toString), ("module", toJson moduleName.toString),
        ("axioms", toJson (axs.toList.map Name.toString))]).compress)
  logInfo m!"ARCH C3 AUDIT PASSED: {names.size} declarations."

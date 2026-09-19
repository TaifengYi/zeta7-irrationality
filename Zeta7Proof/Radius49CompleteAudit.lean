import Zeta7Proof.Radius49Internal
import Zeta7Proof.Radius49InternalAudit
import Lean

/-! Non-circularity and axiom audit of the complete internal radius-49 proof.

Every declaration of the modules below (including generated helpers) may use only `propext`,
`Classical.choice` and `Quot.sound`; the audit fails on any other axiom and on any `axiom`
declaration in these modules. The import closure contains no final, conditional or C-theorem
module, so the radius proof cannot depend on the irrationality endpoints. -/
set_option pp.proofs false

#check @Zeta7Radius49.twistMatrix_bound
#print axioms Zeta7Radius49.twistMatrix_bound
#check @Zeta7Radius49.initial_HSeries_overconvergent
#print axioms Zeta7Radius49.initial_HSeries_overconvergent
#check @Zeta7Main.internal_radius49_geometric_continuation
#print axioms Zeta7Main.internal_radius49_geometric_continuation
#check @Zeta7Main.HSeries_radius49
#print axioms Zeta7Main.HSeries_radius49
#check @Zeta7Radius49.g_fixed
#print axioms Zeta7Radius49.g_fixed
#check @Zeta7Radius49.gA_poly
#print axioms Zeta7Radius49.gA_poly
#check @Zeta7Radius49.gA_close
#print axioms Zeta7Radius49.gA_close
#check @Zeta7Radius49.gA_bound
#print axioms Zeta7Radius49.gA_bound
#check @Zeta7Radius49.twistLin_near
#print axioms Zeta7Radius49.twistLin_near
#check @Zeta7Radius49.psi_xSeries_vSeven
#print axioms Zeta7Radius49.psi_xSeries_vSeven
#check @Zeta7Radius49.twistLin_jacobian
#print axioms Zeta7Radius49.twistLin_jacobian
#check @Zeta7Radius49.katz_formal
#print axioms Zeta7Radius49.katz_formal
#check @Zeta7Radius49.uSeven_Fst
#print axioms Zeta7Radius49.uSeven_Fst

set_option maxHeartbeats 0 in
open Lean Elab Command in
run_cmd do
  let modules := #[`Zeta7Proof.Radius49Bridge, `Zeta7Proof.Radius49Tube,
    `Zeta7Proof.Radius49USeven, `Zeta7Proof.Radius49Coordinate, `Zeta7Proof.Radius49Bootstrap,
    `Zeta7Proof.Radius49Twisted, `Zeta7Proof.Radius49U7Data, `Zeta7Proof.Radius49U7Analytic,
    `Zeta7Proof.Radius49U7Formal, `Zeta7Proof.Radius49U7PowerSums, `Zeta7Proof.Radius49U7Psi,
    `Zeta7Proof.Radius49U7Jacobian, `Zeta7Proof.Radius49U7Norm, `Zeta7Proof.Radius49HM,
    `Zeta7Proof.Radius49HONear, `Zeta7Proof.Radius49HOFricke, `Zeta7Proof.Radius49HOGen,
    `Zeta7Proof.Radius49HOAlg, `Zeta7Proof.Radius49HOBnd, `Zeta7Proof.Radius49HOChain,
    `Zeta7Proof.Radius49FromPublishedGeometry, `Zeta7Proof.Radius49Internal,
    `Zeta7Proof.Radius49GeometryCore]
  let forbiddenImports := #[`Zeta7Proof.FinalTheorem, `Zeta7Proof.FinalConditional,
    `Zeta7Proof.ArchCTheorem, `Zeta7Proof.ArchC30, `Zeta7Proof.PublishedRadius49GeometricInput]
  let foundations := #[``propext, ``Classical.choice, ``Quot.sound]
  let env ← getEnv
  for m in forbiddenImports do
    if env.header.moduleNames.contains m then
      throwError "Circular dependency risk: {m} is in the import closure"
  for m in modules do
    unless env.header.moduleNames.contains m do
      throwError "Audited module missing from the import closure: {m}"
  let mut names : Array Name := #[]
  for idx in [:env.header.moduleNames.size] do
    let moduleName := env.header.moduleNames[idx]!
    unless modules.contains moduleName do continue
    let data := env.header.moduleData[idx]!
    for name in data.constNames ++ data.extraConstNames do
      if names.contains name then continue
      let some info := env.find? name | continue
      names := names.push name
      if let .axiomInfo _ := info then throwError "Mathematical axiom declared: {name}"
      let axs ← Lean.collectAxioms name
      for ax in axs do
        unless foundations.contains ax do
          throwError "Unexpected transitive axiom {ax} in {name}"
  logInfo m!"RADIUS COMPLETE AUDIT PASSED: {names.size} declarations."

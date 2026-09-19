import Zeta7Proof.Radius49Coordinate
import Zeta7Proof.Radius49Twisted
import Zeta7Proof.RadiusPhaseVIAudit
import Lean

/-! Non-circularity and axiom audit of the radius-internalization modules.

Every declaration of the modules below may use only `propext`, `Classical.choice` and
`Quot.sound`. In particular none depends on `Zeta7Main.published_radius49_geometric_continuation`,
on the irrationality endpoints, or on the C endpoint (checked: the audit fails on any other
axiom, and the imports below contain no final or C-theorem module). -/
set_option pp.proofs false

#check @Zeta7Main.hasRadius49_of_matrix_bound_and_initial
#print axioms Zeta7Main.hasRadius49_of_matrix_bound_and_initial
#check @Zeta7Main.HSeries_twisted_fixed
#print axioms Zeta7Main.HSeries_twisted_fixed
#check @Zeta7Main.twistLin_HSeries
#print axioms Zeta7Main.twistLin_HSeries
#check @Zeta7Radius49.decay_all_below_two
#print axioms Zeta7Radius49.decay_all_below_two
#check @Zeta7Radius49.projectX_fricke
#print axioms Zeta7Radius49.projectX_fricke
#check @Zeta7Radius49.norm_fricke
#print axioms Zeta7Radius49.norm_fricke
#check @Zeta7Main.uSeven_G_add_const
#print axioms Zeta7Main.uSeven_G_add_const

-- Traverse every declaration (including auxiliary ones) of the radius-internalization modules.
set_option maxHeartbeats 0 in
open Lean Elab Command in
run_cmd do
  let modules := #[`Zeta7Proof.Radius49Bridge, `Zeta7Proof.Radius49Tube,
    `Zeta7Proof.Radius49USeven, `Zeta7Proof.Radius49Coordinate, `Zeta7Proof.Radius49Bootstrap,
    `Zeta7Proof.Radius49Twisted]
  let forbiddenImports := #[`Zeta7Proof.FinalTheorem, `Zeta7Proof.FinalConditional,
    `Zeta7Proof.ArchCTheorem, `Zeta7Proof.ArchC30]
  let foundations := #[``propext, ``Classical.choice, ``Quot.sound]
  let env ← getEnv
  for m in forbiddenImports do
    if env.header.moduleNames.contains m then
      throwError "Circular dependency risk: {m} is in the import closure"
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
  logInfo m!"RADIUS INTERNAL AUDIT PASSED: {names.size} declarations."

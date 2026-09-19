import Zeta7Proof.FinalTheorem
import Zeta7Proof.FinalAudit
import Zeta7Proof.Radius49CompleteAudit
import Lean

/-! **Final audit of the fully internal proof.**

A. The irrationality endpoints use exactly `propext`, `Classical.choice`, `Quot.sound`.
B. The radius endpoints (HM, HO, the internal continuation, the coefficient decay) likewise.
C. No module of the project (`Zeta7Proof`, `Zeta7Main`, `PadicLFunctions`, `LeanModularForms`,
   `Stage2*`) in the import closure of the endpoints declares an `axiom`.
D. No endpoint depends on the archived `Zeta7Main.published_radius49_geometric_continuation`.
E. The archival module `Zeta7Proof.PublishedRadius49GeometricInput` is not in the import closure.
F. Non-circularity: `Radius49CompleteAudit` (imported) checks that the radius proof's import
   closure contains none of `FinalTheorem`, `FinalConditional`, `ArchCTheorem`, `ArchC30`. -/
set_option pp.proofs false

#check @Zeta7Main.zeta7Three_irrational
#print axioms Zeta7Main.zeta7Three_irrational
#check @Zeta7Main.eta_irrational
#print axioms Zeta7Main.eta_irrational
#print axioms Zeta7Radius49.twistMatrix_bound
#print axioms Zeta7Radius49.initial_HSeries_overconvergent
#print axioms Zeta7Main.internal_radius49_geometric_continuation
#print axioms Zeta7Main.HSeries_radius49
#print axioms Zeta7Main.c_theorem_explicit
#print axioms Zeta7Cert.surplusS_gt
#print axioms Zeta7Valence.energyI_le_explicitI

set_option maxHeartbeats 0 in
open Lean Elab Command in
run_cmd do
  let foundations := #[``propext, ``Classical.choice, ``Quot.sound]
  let published := `Zeta7Main.published_radius49_geometric_continuation
  let endpoints := #[``Zeta7Main.zeta7Three_irrational, ``Zeta7Main.eta_irrational,
    ``Zeta7Radius49.twistMatrix_bound, ``Zeta7Radius49.initial_HSeries_overconvergent,
    ``Zeta7Main.internal_radius49_geometric_continuation, ``Zeta7Main.HSeries_radius49,
    ``Zeta7Main.c_theorem_explicit, ``Zeta7Cert.surplusS_gt,
    ``Zeta7Valence.energyI_le_explicitI]
  -- A, B, D
  for e in endpoints do
    let axs ← Lean.collectAxioms e
    if axs.contains published then
      throwError "Endpoint {e} depends on the archived published radius input"
    for ax in axs do
      unless foundations.contains ax do
        throwError "Endpoint {e} uses the non-foundational axiom {ax}"
    for ax in foundations do
      unless axs.contains ax do
        throwError "Endpoint {e}: axiom set differs from [propext, Classical.choice, Quot.sound]"
    logInfo m!"ENDPOINT {e}: AXIOMS = {axs.toList}"
  let env ← getEnv
  -- E
  if env.header.moduleNames.contains `Zeta7Proof.PublishedRadius49GeometricInput then
    throwError "Archived axiom module is in the import closure"
  if env.contains published then
    throwError "The archived axiom is present in the environment"
  -- C
  let projectRoots := [`Zeta7Proof, `Zeta7Main, `PadicLFunctions, `LeanModularForms,
    `Stage2A, `Stage2B, `Stage2Operator, `Zeta7AxiomAudit]
  let mut projectDecls : Nat := 0
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let modName := env.header.moduleNames[idx]!
    unless projectRoots.any (·.isPrefixOf modName) do continue
    projectDecls := projectDecls + 1
    if let .axiomInfo _ := info then
      throwError "Project axiom declaration {name} in {modName}"
  logInfo m!"FINAL INTERNAL AUDIT PASSED: {endpoints.size} endpoints with exactly \
    [propext, Classical.choice, Quot.sound]; {projectDecls} project declarations in the import \
    closure, none an axiom; archived radius axiom absent."

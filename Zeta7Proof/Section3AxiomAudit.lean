import Zeta7Proof.Section3ScalarCriterion
import Zeta7Proof.Section3DomainEstimates
import Lean.Elab.Print

set_option linter.style.setOption false
set_option pp.proofs true
set_option pp.maxSteps 1000000
set_option format.width 120

#check @Zeta7Section3.exists_small_exponent
#print Zeta7Section3.exists_small_exponent
#print axioms Zeta7Section3.exists_small_exponent

#check @Zeta7Section3.weighted_decay_of_epsilon_bound
#print Zeta7Section3.weighted_decay_of_epsilon_bound
#print axioms Zeta7Section3.weighted_decay_of_epsilon_bound

#check @Zeta7Section3.weighted_rescale_identity
#print Zeta7Section3.weighted_rescale_identity
#print axioms Zeta7Section3.weighted_rescale_identity

#check @Zeta7Section3.radius49_of_epsilon_bound
#print Zeta7Section3.radius49_of_epsilon_bound
#print axioms Zeta7Section3.radius49_of_epsilon_bound

#check @Zeta7Section3.norm_bound_of_valuation
#print Zeta7Section3.norm_bound_of_valuation
#print axioms Zeta7Section3.norm_bound_of_valuation

#check @Zeta7Section3.radius49_of_valuation_estimate
#print Zeta7Section3.radius49_of_valuation_estimate
#print axioms Zeta7Section3.radius49_of_valuation_estimate

#check @Zeta7Section3.rescale_valuation
#print Zeta7Section3.rescale_valuation
#print axioms Zeta7Section3.rescale_valuation

#check @Zeta7Section3.radius49_of_unscaled_valuation_estimate
#print Zeta7Section3.radius49_of_unscaled_valuation_estimate
#print axioms Zeta7Section3.radius49_of_unscaled_valuation_estimate

#check @Zeta7Section3.domainP
#print Zeta7Section3.domainP
#print axioms Zeta7Section3.domainP

#check @Zeta7Section3.domainN
#print Zeta7Section3.domainN
#print axioms Zeta7Section3.domainN

#check @Zeta7Section3.domainT
#print Zeta7Section3.domainT
#print axioms Zeta7Section3.domainT

#check @Zeta7Section3.domainJ
#print Zeta7Section3.domainJ
#print axioms Zeta7Section3.domainJ

#check @Zeta7Section3.norm_nat_unit
#print Zeta7Section3.norm_nat_unit
#print axioms Zeta7Section3.norm_nat_unit

#check @Zeta7Section3.norm_seven
#print Zeta7Section3.norm_seven
#print axioms Zeta7Section3.norm_seven

#check @Zeta7Section3.norm_unit_seven_power
#print Zeta7Section3.norm_unit_seven_power
#print axioms Zeta7Section3.norm_unit_seven_power

#check @Zeta7Section3.domain_coefficient_norms
#print Zeta7Section3.domain_coefficient_norms
#print axioms Zeta7Section3.domain_coefficient_norms

#check @Zeta7Section3.domainP_norm
#print Zeta7Section3.domainP_norm
#print axioms Zeta7Section3.domainP_norm

#check @Zeta7Section3.domainN_norm
#print Zeta7Section3.domainN_norm
#print axioms Zeta7Section3.domainN_norm

#check @Zeta7Section3.domainT_norm_bound
#print Zeta7Section3.domainT_norm_bound
#print axioms Zeta7Section3.domainT_norm_bound

#check @Zeta7Section3.domain_polynomial_identity
#print Zeta7Section3.domain_polynomial_identity
#print axioms Zeta7Section3.domain_polynomial_identity

#check @Zeta7Section3.domainJ_sub
#print Zeta7Section3.domainJ_sub
#print axioms Zeta7Section3.domainJ_sub

#check @Zeta7Section3.domainJ_sub_norm_bound
#print Zeta7Section3.domainJ_sub_norm_bound
#print axioms Zeta7Section3.domainJ_sub_norm_bound

#check @Zeta7Section3.domainJ_supersingular_norm
#print Zeta7Section3.domainJ_supersingular_norm
#print axioms Zeta7Section3.domainJ_supersingular_norm

#check @Zeta7Section3.domainT_sub_one_norm
#print Zeta7Section3.domainT_sub_one_norm
#print axioms Zeta7Section3.domainT_sub_one_norm

#check @Zeta7Section3.domainT_norm_unit_disc
#print Zeta7Section3.domainT_norm_unit_disc
#print axioms Zeta7Section3.domainT_norm_unit_disc

#check @Zeta7Section3.domainJ_sub_norm_unit_disc
#print Zeta7Section3.domainJ_sub_norm_unit_disc
#print axioms Zeta7Section3.domainJ_sub_norm_unit_disc

#check @Zeta7Section3.domainJ_sub_norm_boundary
#print Zeta7Section3.domainJ_sub_norm_boundary
#print axioms Zeta7Section3.domainJ_sub_norm_boundary

/- Type-check the missing estimate only. No declaration or assumption of it. -/
section MissingSignatureTypeOnly
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩
#check (∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧
  ∀ n : ℕ, PowerSeries.coeff n Zeta7Main.normalisedHSeries ≠ 0 →
    -ε * (n : ℝ) - B ≤
      (Padic.valuation (PowerSeries.coeff n Zeta7Main.normalisedHSeries) : ℝ) : Prop)
end MissingSignatureTypeOnly
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let modName := env.header.moduleNames[idx]!
    if (`PadicLFunctions).isPrefixOf modName ||
        (`LeanModularForms).isPrefixOf modName || (`Zeta7Proof).isPrefixOf modName then
      let axioms ← Lean.collectAxioms name
      for ax in axioms do
        unless allowed.contains ax do
          throwError "Unapproved kernel dependency {ax} in {name}"
      count := count + 1
  logInfo m!"SECTION3 AXIOM AUDIT: {count} declarations; all dependencies on the whitelist."

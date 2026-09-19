import Zeta7Proof.Radius49Compatibility
import Zeta7Proof.Radius49Trace
import Zeta7Proof.Radius49Hasse
import Zeta7Proof.Radius49Restricted
import Zeta7Proof.Radius49DiscArithmetic
import Zeta7Proof.GenusSevenCoordinate
import Zeta7Proof.GenusSevenGateAudit
import Lean.Elab.Print
import Lean.Util.FoldConsts

set_option linter.style.setOption false
set_option pp.proofs true
set_option pp.maxSteps 1000000
set_option format.width 120

#check @Zeta7Radius49.paperEulerZeta
#print Zeta7Radius49.paperEulerZeta
#print axioms Zeta7Radius49.paperEulerZeta

#check @Zeta7Radius49.paperEulerZeta_eq_stabilised
#print Zeta7Radius49.paperEulerZeta_eq_stabilised
#print axioms Zeta7Radius49.paperEulerZeta_eq_stabilised

#check @Zeta7Radius49.paperEulerZeta_tendsto
#print Zeta7Radius49.paperEulerZeta_tendsto
#print axioms Zeta7Radius49.paperEulerZeta_tendsto

#check @Zeta7Radius49.paperEta
#print Zeta7Radius49.paperEta
#print axioms Zeta7Radius49.paperEta

#check @Zeta7Radius49.paperEta_eq
#print Zeta7Radius49.paperEta_eq
#print axioms Zeta7Radius49.paperEta_eq

#check @Zeta7Radius49.paperEta_eq_eta
#print Zeta7Radius49.paperEta_eq_eta
#print axioms Zeta7Radius49.paperEta_eq_eta

#check @Zeta7Radius49.paperH
#print Zeta7Radius49.paperH
#print axioms Zeta7Radius49.paperH

#check @Zeta7Radius49.paperH_eq
#print Zeta7Radius49.paperH_eq
#print axioms Zeta7Radius49.paperH_eq

#check @Zeta7Radius49.paperH_eisenstein
#print Zeta7Radius49.paperH_eisenstein
#print axioms Zeta7Radius49.paperH_eisenstein

#check @Zeta7Radius49.normalisedHSeries_eq_paper_rescale
#print Zeta7Radius49.normalisedHSeries_eq_paper_rescale
#print axioms Zeta7Radius49.normalisedHSeries_eq_paper_rescale

#check @Zeta7Radius49.normalisedHSeries_coeff_zpow
#print Zeta7Radius49.normalisedHSeries_coeff_zpow
#print axioms Zeta7Radius49.normalisedHSeries_coeff_zpow

#check @Zeta7Radius49.nonzero_norm_valuation
#print Zeta7Radius49.nonzero_norm_valuation
#print axioms Zeta7Radius49.nonzero_norm_valuation

#check @Zeta7Radius49.normalizedTrace
#print Zeta7Radius49.normalizedTrace
#print axioms Zeta7Radius49.normalizedTrace

#check @Zeta7Radius49.scalar_trace
#print Zeta7Radius49.scalar_trace
#print axioms Zeta7Radius49.scalar_trace

#check @Zeta7Radius49.normalizedTrace_scalar
#print Zeta7Radius49.normalizedTrace_scalar
#print axioms Zeta7Radius49.normalizedTrace_scalar

#check @Zeta7Radius49.normalizedTrace_one
#print Zeta7Radius49.normalizedTrace_one
#print axioms Zeta7Radius49.normalizedTrace_one

#check @Zeta7Radius49.scalar_inclusion_injective
#print Zeta7Radius49.scalar_inclusion_injective
#print axioms Zeta7Radius49.scalar_inclusion_injective

#check @Zeta7Radius49.normalizedTrace_descends
#print Zeta7Radius49.normalizedTrace_descends
#print axioms Zeta7Radius49.normalizedTrace_descends

#check @Zeta7Radius49.normalizedTrace_idempotent
#print Zeta7Radius49.normalizedTrace_idempotent
#print axioms Zeta7Radius49.normalizedTrace_idempotent

#check @Zeta7Radius49.descended_idempotent_zero_or_one
#print Zeta7Radius49.descended_idempotent_zero_or_one
#print axioms Zeta7Radius49.descended_idempotent_zero_or_one

#check @Zeta7Radius49.idempotent_eq_one_of_nonzero
#print Zeta7Radius49.idempotent_eq_one_of_nonzero
#print axioms Zeta7Radius49.idempotent_eq_one_of_nonzero

#check @Zeta7Radius49.trace_baseChange
#print Zeta7Radius49.trace_baseChange
#print axioms Zeta7Radius49.trace_baseChange

#check @Zeta7Radius49.algebra_trace_baseChange
#print Zeta7Radius49.algebra_trace_baseChange
#print axioms Zeta7Radius49.algebra_trace_baseChange

#check @Zeta7Radius49.normalizedTrace_baseChange
#print Zeta7Radius49.normalizedTrace_baseChange
#print axioms Zeta7Radius49.normalizedTrace_baseChange

#check @Zeta7Radius49.restricted_idempotent_zero_or_one
#print Zeta7Radius49.restricted_idempotent_zero_or_one
#print axioms Zeta7Radius49.restricted_idempotent_zero_or_one

#check @Zeta7Radius49.shortCurve
#print Zeta7Radius49.shortCurve
#print axioms Zeta7Radius49.shortCurve

#check @Zeta7Radius49.cubic_cube_coeff_six
#print Zeta7Radius49.cubic_cube_coeff_six
#print axioms Zeta7Radius49.cubic_cube_coeff_six

#check @Zeta7Radius49.cubic_cube_coeff_six_eq_zero
#print Zeta7Radius49.cubic_cube_coeff_six_eq_zero
#print axioms Zeta7Radius49.cubic_cube_coeff_six_eq_zero

#check @Zeta7Radius49.shortCurve_discriminant
#print Zeta7Radius49.shortCurve_discriminant
#print axioms Zeta7Radius49.shortCurve_discriminant

#check @Zeta7Radius49.shortCurve_c_four
#print Zeta7Radius49.shortCurve_c_four
#print axioms Zeta7Radius49.shortCurve_c_four

#check @Zeta7Radius49.shortCurve_j_eq_1728_iff
#print Zeta7Radius49.shortCurve_j_eq_1728_iff
#print axioms Zeta7Radius49.shortCurve_j_eq_1728_iff

#check @Zeta7Radius49.cubic_cube_coeff_zero_iff_j
#print Zeta7Radius49.cubic_cube_coeff_zero_iff_j
#print axioms Zeta7Radius49.cubic_cube_coeff_zero_iff_j

#check @Zeta7Radius49.restricted_coeff_bound
#print Zeta7Radius49.restricted_coeff_bound
#print axioms Zeta7Radius49.restricted_coeff_bound

#check @Zeta7Radius49.restricted_coeff_epsilon_bound
#print Zeta7Radius49.restricted_coeff_epsilon_bound
#print axioms Zeta7Radius49.restricted_coeff_epsilon_bound

#check @Zeta7Radius49.equation12_of_rational_restrictions
#print Zeta7Radius49.equation12_of_rational_restrictions
#print axioms Zeta7Radius49.equation12_of_rational_restrictions

#check @Zeta7Radius49.isRestricted_map_iff
#print Zeta7Radius49.isRestricted_map_iff
#print axioms Zeta7Radius49.isRestricted_map_iff

#check @Zeta7Radius49.domainP_norm_small
#print Zeta7Radius49.domainP_norm_small
#print axioms Zeta7Radius49.domainP_norm_small

#check @Zeta7Radius49.domainJ_norm_small
#print Zeta7Radius49.domainJ_norm_small
#print axioms Zeta7Radius49.domainJ_norm_small

#check @Zeta7Radius49.domainP_norm_le_one
#print Zeta7Radius49.domainP_norm_le_one
#print axioms Zeta7Radius49.domainP_norm_le_one

#check @Zeta7Radius49.domainJ_norm_boundary
#print Zeta7Radius49.domainJ_norm_boundary
#print axioms Zeta7Radius49.domainJ_norm_boundary

#check @Zeta7Radius49.domainJ_norm_annulus
#print Zeta7Radius49.domainJ_norm_annulus
#print axioms Zeta7Radius49.domainJ_norm_annulus

#check @Zeta7GenusSeven.euler_multipliable
#print Zeta7GenusSeven.euler_multipliable
#print axioms Zeta7GenusSeven.euler_multipliable

#check @Zeta7GenusSeven.euler
#print Zeta7GenusSeven.euler
#print axioms Zeta7GenusSeven.euler

#check @Zeta7GenusSeven.delta
#print Zeta7GenusSeven.delta
#print axioms Zeta7GenusSeven.delta

#check @Zeta7GenusSeven.euler_constant
#print Zeta7GenusSeven.euler_constant
#print axioms Zeta7GenusSeven.euler_constant

#check @Zeta7GenusSeven.continuous_expand_seven
#print Zeta7GenusSeven.continuous_expand_seven
#print axioms Zeta7GenusSeven.continuous_expand_seven

#check @Zeta7GenusSeven.sevenMultipleIndex
#print Zeta7GenusSeven.sevenMultipleIndex
#print axioms Zeta7GenusSeven.sevenMultipleIndex

#check @Zeta7GenusSeven.euler_seven_factorization
#print Zeta7GenusSeven.euler_seven_factorization
#print axioms Zeta7GenusSeven.euler_seven_factorization

#check @Zeta7GenusSeven.d7
#print Zeta7GenusSeven.d7
#print axioms Zeta7GenusSeven.d7

#check @Zeta7GenusSeven.euler_quotient
#print Zeta7GenusSeven.euler_quotient
#print axioms Zeta7GenusSeven.euler_quotient

#check @Zeta7GenusSeven.d7_eq_xSeries
#print Zeta7GenusSeven.d7_eq_xSeries
#print axioms Zeta7GenusSeven.d7_eq_xSeries

#check @Zeta7GenusSeven.d7_constant
#print Zeta7GenusSeven.d7_constant
#print axioms Zeta7GenusSeven.d7_constant

#check @Zeta7GenusSeven.d7_linear
#print Zeta7GenusSeven.d7_linear
#print axioms Zeta7GenusSeven.d7_linear

#check @Zeta7GenusSeven.d7_sixth_delta
#print Zeta7GenusSeven.d7_sixth_delta
#print axioms Zeta7GenusSeven.d7_sixth_delta

#check @Zeta7GenusSeven.delta_linear
#print Zeta7GenusSeven.delta_linear
#print axioms Zeta7GenusSeven.delta_linear

#check @Zeta7GenusSeven.delta_ne_zero
#print Zeta7GenusSeven.delta_ne_zero
#print axioms Zeta7GenusSeven.delta_ne_zero

#check @Zeta7GenusSeven.sixth_power_injective_constant_one
#print Zeta7GenusSeven.sixth_power_injective_constant_one
#print axioms Zeta7GenusSeven.sixth_power_injective_constant_one

#check @Zeta7GenusSeven.d7_unique
#print Zeta7GenusSeven.d7_unique
#print axioms Zeta7GenusSeven.d7_unique

#check @Zeta7GenusSeven.normalisedHSeries_exact_scale
#print Zeta7GenusSeven.normalisedHSeries_exact_scale
#print axioms Zeta7GenusSeven.normalisedHSeries_exact_scale

#check @Zeta7GenusSeven.d7_subst_q
#print Zeta7GenusSeven.d7_subst_q
#print axioms Zeta7GenusSeven.d7_subst_q

#check @Zeta7GenusSeven.q_subst_d7
#print Zeta7GenusSeven.q_subst_d7
#print axioms Zeta7GenusSeven.q_subst_d7

#check @Zeta7GenusSeven.t7
#print Zeta7GenusSeven.t7
#print axioms Zeta7GenusSeven.t7

#check @Zeta7GenusSeven.t7_eq_scaled_xSeries
#print Zeta7GenusSeven.t7_eq_scaled_xSeries
#print axioms Zeta7GenusSeven.t7_eq_scaled_xSeries

#check @Zeta7GenusSeven.t7_subst_q
#print Zeta7GenusSeven.t7_subst_q
#print axioms Zeta7GenusSeven.t7_subst_q

#check @Zeta7GenusSeven.oppositeH_exact_scale
#print Zeta7GenusSeven.oppositeH_exact_scale
#print axioms Zeta7GenusSeven.oppositeH_exact_scale

#check @Zeta7GenusSeven.unitTwo
#print Zeta7GenusSeven.unitTwo
#print axioms Zeta7GenusSeven.unitTwo

#check @Zeta7GenusSeven.unitTwo_value
#print Zeta7GenusSeven.unitTwo_value
#print axioms Zeta7GenusSeven.unitTwo_value

#check @Zeta7GenusSeven.genuine_weight_at_two
#print Zeta7GenusSeven.genuine_weight_at_two
#print axioms Zeta7GenusSeven.genuine_weight_at_two

#check @Zeta7GenusSeven.genuine_weight_not_zero
#print Zeta7GenusSeven.genuine_weight_not_zero
#print axioms Zeta7GenusSeven.genuine_weight_not_zero

#check @Zeta7GenusSeven.canonical_radius_gap
#print Zeta7GenusSeven.canonical_radius_gap
#print axioms Zeta7GenusSeven.canonical_radius_gap

#check @Zeta7GenusSeven.ellipticFactor
#print Zeta7GenusSeven.ellipticFactor
#print axioms Zeta7GenusSeven.ellipticFactor

#check @Zeta7GenusSeven.ellipticFactor_at_one
#print Zeta7GenusSeven.ellipticFactor_at_one
#print axioms Zeta7GenusSeven.ellipticFactor_at_one

#check @Zeta7GenusSeven.ellipticFactor_derivative_at_one
#print Zeta7GenusSeven.ellipticFactor_derivative_at_one
#print axioms Zeta7GenusSeven.ellipticFactor_derivative_at_one

#check @Zeta7GenusSeven.ellipticFactor_hensel_data
#print Zeta7GenusSeven.ellipticFactor_hensel_data
#print axioms Zeta7GenusSeven.ellipticFactor_hensel_data

#check @Zeta7GenusSeven.ellipticFactor_root_on_unit_circle
#print Zeta7GenusSeven.ellipticFactor_root_on_unit_circle
#print axioms Zeta7GenusSeven.ellipticFactor_root_on_unit_circle

#check @Zeta7GenusSeven.no_pointwise_reciprocal_on_unit_disc
#print Zeta7GenusSeven.no_pointwise_reciprocal_on_unit_disc
#print axioms Zeta7GenusSeven.no_pointwise_reciprocal_on_unit_disc

-- Previously proved inputs; no new external repository is imported.
#check @Zeta7Main.eisensteinMinusTwo
#print Zeta7Main.eisensteinMinusTwo
#print axioms Zeta7Main.eisensteinMinusTwo

#check @Zeta7Main.HSeries
#print Zeta7Main.HSeries
#print axioms Zeta7Main.HSeries

#check @Zeta7Main.normalisedHSeries
#print Zeta7Main.normalisedHSeries
#print axioms Zeta7Main.normalisedHSeries

#check @Zeta7Main.HSeries_eq_eisenstein_subst
#print Zeta7Main.HSeries_eq_eisenstein_subst
#print axioms Zeta7Main.HSeries_eq_eisenstein_subst

#check @Zeta7Main.qExpansionUSeven_eisenstein
#print Zeta7Main.qExpansionUSeven_eisenstein
#print axioms Zeta7Main.qExpansionUSeven_eisenstein

#check @hensels_lemma
#print hensels_lemma
#print axioms hensels_lemma

#check @PowerSeries.isRestricted_iff'
#print PowerSeries.isRestricted_iff'
#print axioms PowerSeries.isRestricted_iff'

#check @Zeta7Section3.radius49_of_valuation_estimate
#print Zeta7Section3.radius49_of_valuation_estimate
#print axioms Zeta7Section3.radius49_of_valuation_estimate

open Lean Elab Command in
run_cmd do
  let env <- getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let modName := env.header.moduleNames[idx]!
    if (`PadicLFunctions).isPrefixOf modName ||
        (`LeanModularForms).isPrefixOf modName || (`Zeta7Proof).isPrefixOf modName then
      let axioms <- Lean.collectAxioms name
      for ax in axioms do
        unless allowed.contains ax do
          throwError "Unapproved kernel dependency {ax} in {name}"
      count := count + 1
  logInfo m!"RADIUS49 AXIOM AUDIT: {count} declarations; all dependencies on the whitelist."
  let endpoints : Array Name := #[``Zeta7Radius49.paperEulerZeta, ``Zeta7Radius49.paperEulerZeta_eq_stabilised, ``Zeta7Radius49.paperEulerZeta_tendsto, ``Zeta7Radius49.paperEta, ``Zeta7Radius49.paperEta_eq, ``Zeta7Radius49.paperEta_eq_eta, ``Zeta7Radius49.paperH, ``Zeta7Radius49.paperH_eq, ``Zeta7Radius49.paperH_eisenstein, ``Zeta7Radius49.normalisedHSeries_eq_paper_rescale, ``Zeta7Radius49.normalisedHSeries_coeff_zpow, ``Zeta7Radius49.nonzero_norm_valuation, ``Zeta7Radius49.normalizedTrace, ``Zeta7Radius49.scalar_trace, ``Zeta7Radius49.normalizedTrace_scalar, ``Zeta7Radius49.normalizedTrace_one, ``Zeta7Radius49.scalar_inclusion_injective, ``Zeta7Radius49.normalizedTrace_descends, ``Zeta7Radius49.normalizedTrace_idempotent, ``Zeta7Radius49.descended_idempotent_zero_or_one, ``Zeta7Radius49.idempotent_eq_one_of_nonzero, ``Zeta7Radius49.trace_baseChange, ``Zeta7Radius49.algebra_trace_baseChange, ``Zeta7Radius49.normalizedTrace_baseChange, ``Zeta7Radius49.restricted_idempotent_zero_or_one, ``Zeta7Radius49.shortCurve, ``Zeta7Radius49.cubic_cube_coeff_six, ``Zeta7Radius49.cubic_cube_coeff_six_eq_zero, ``Zeta7Radius49.shortCurve_discriminant, ``Zeta7Radius49.shortCurve_c_four, ``Zeta7Radius49.shortCurve_j_eq_1728_iff, ``Zeta7Radius49.cubic_cube_coeff_zero_iff_j, ``Zeta7Radius49.restricted_coeff_bound, ``Zeta7Radius49.restricted_coeff_epsilon_bound, ``Zeta7Radius49.equation12_of_rational_restrictions, ``Zeta7Radius49.isRestricted_map_iff, ``Zeta7Radius49.domainP_norm_small, ``Zeta7Radius49.domainJ_norm_small, ``Zeta7Radius49.domainP_norm_le_one, ``Zeta7Radius49.domainJ_norm_boundary, ``Zeta7Radius49.domainJ_norm_annulus, ``Zeta7GenusSeven.euler_multipliable, ``Zeta7GenusSeven.euler, ``Zeta7GenusSeven.delta, ``Zeta7GenusSeven.euler_constant, ``Zeta7GenusSeven.continuous_expand_seven, ``Zeta7GenusSeven.sevenMultipleIndex, ``Zeta7GenusSeven.euler_seven_factorization, ``Zeta7GenusSeven.d7, ``Zeta7GenusSeven.euler_quotient, ``Zeta7GenusSeven.d7_eq_xSeries, ``Zeta7GenusSeven.d7_constant, ``Zeta7GenusSeven.d7_linear, ``Zeta7GenusSeven.d7_sixth_delta, ``Zeta7GenusSeven.delta_linear, ``Zeta7GenusSeven.delta_ne_zero, ``Zeta7GenusSeven.sixth_power_injective_constant_one, ``Zeta7GenusSeven.d7_unique, ``Zeta7GenusSeven.normalisedHSeries_exact_scale, ``Zeta7GenusSeven.d7_subst_q, ``Zeta7GenusSeven.q_subst_d7, ``Zeta7GenusSeven.t7, ``Zeta7GenusSeven.t7_eq_scaled_xSeries, ``Zeta7GenusSeven.t7_subst_q, ``Zeta7GenusSeven.oppositeH_exact_scale, ``Zeta7GenusSeven.unitTwo, ``Zeta7GenusSeven.unitTwo_value, ``Zeta7GenusSeven.genuine_weight_at_two, ``Zeta7GenusSeven.genuine_weight_not_zero, ``Zeta7GenusSeven.canonical_radius_gap, ``Zeta7GenusSeven.ellipticFactor, ``Zeta7GenusSeven.ellipticFactor_at_one, ``Zeta7GenusSeven.ellipticFactor_derivative_at_one, ``Zeta7GenusSeven.ellipticFactor_hensel_data, ``Zeta7GenusSeven.ellipticFactor_root_on_unit_circle, ``Zeta7GenusSeven.no_pointwise_reciprocal_on_unit_disc]
  for name in endpoints do
    let some info := env.find? name | throwError "Missing endpoint {name}"
    let deps := info.getUsedConstantsAsSet.toList.mergeSort Name.quickLt
    logInfo m!"RADIUS49 DIRECT DEPENDENCIES {name}: {deps}"
    logInfo ("RADIUS49_DEP_JSON " ++ (Json.mkObj
      [("endpoint", toJson name.toString), ("dependencies", toJson (deps.map Name.toString))]).compress)
  for forbidden in #[`Zeta7Main.HSeries_radius49, `Zeta7Main.HSeries_equation12] do
    if env.contains forbidden then throwError "Unexpected target declaration {forbidden}"
  logInfo "RADIUS49 TARGET AUDIT: no target theorem or target axiom introduced."

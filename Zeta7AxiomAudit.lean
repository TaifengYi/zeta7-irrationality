import Zeta7Main
import Zeta7Proof.KLAxiomAudit
import Zeta7Proof.EisensteinAxiomAudit
import Zeta7Proof.UniformAxiomAudit
import Zeta7Proof.UniformEndpointsAudit
import Zeta7Proof.AnnulusAxiomAudit
import Zeta7Proof.Section3AxiomAudit
import Zeta7Proof.Radius49AxiomAudit

/-! Audit of every named project definition, theorem and instance.
Explicit theorem hypotheses must also be read; they are not extra axioms. -/

-- Zeta7Proof/Basic.lean
#print axioms hello

-- Zeta7Proof/ExactAlgebra.lean
#print axioms Zeta7Exact.P
#print axioms Zeta7Exact.N
#print axioms Zeta7Exact.T
#print axioms Zeta7Exact.modular_polynomial_identity
#print axioms Zeta7Exact.P_pos
#print axioms Zeta7Exact.P_ne_zero
#print axioms Zeta7Exact.obstructionNumerator
#print axioms Zeta7Exact.obstruction_pivot
#print axioms Zeta7Exact.obstruction_pivot_ne_zero
#print axioms Zeta7Exact.bandBracket
#print axioms Zeta7Exact.band_minus_two
#print axioms Zeta7Exact.annularResonance
#print axioms Zeta7Exact.annular_correction_pivot
#print axioms Zeta7Exact.annular_correction_pivot_ne_zero
#print axioms Zeta7Exact.affineValue
#print axioms Zeta7Exact.profile_continuous_at_breakpoints
#print axioms Zeta7Exact.profile_vanishes_at_seven
#print axioms Zeta7Exact.affineArea
#print axioms Zeta7Exact.profileArea
#print axioms Zeta7Exact.profile_area_exact
#print axioms Zeta7Exact.six_masses_sum
#print axioms Zeta7Exact.assigned_partition_lengths
#print axioms Zeta7Exact.twice_sum_range
#print axioms Zeta7Exact.baseline_tail_row_sum

-- Zeta7Proof/Zeta7_Lean_Partial.lean
#print axioms Zeta7Partial.twiceOperator
#print axioms Zeta7Partial.concomitant
#print axioms Zeta7Partial.concomitant_identity
#print axioms Zeta7Partial.twiceK
#print axioms Zeta7Partial.twiceK_identity
#print axioms Zeta7Partial.quadraticPrimitive
#print axioms Zeta7Partial.quadraticPrimitive_identity
#print axioms Zeta7Partial.affineArea
#print axioms Zeta7Partial.profileArea
#print axioms Zeta7Partial.profileArea_exact
#print axioms Zeta7Partial.six_masses_sum
#print axioms Zeta7Partial.correction_pivot
#print axioms Zeta7Partial.correction_pivot_nonzero
#print axioms Zeta7Partial.twice_sum_range
#print axioms Zeta7Partial.baseline_row_sum
#print axioms Zeta7Partial.surplus
#print axioms Zeta7Partial.surplus_bounds_from_enclosures
#print axioms Zeta7Partial.surplus_positive_from_enclosures
#print axioms Zeta7Partial.QuadraticUpper
#print axioms Zeta7Partial.no_three_place_data
#print axioms Zeta7Partial.no_data_from_enclosures
#print axioms Zeta7Partial.seven_prime
#print axioms Zeta7Partial.IsRationalSeven
#print axioms Zeta7Partial.conditional_exclusion

-- Zeta7Proof/DifferentialOperator.lean
#print axioms Zeta7Differential.unit_potential_relation
#print axioms Zeta7Differential.unit_potential_derivative
#print axioms Zeta7Differential.twice_cleared_operator
#print axioms Zeta7Differential.cleared_operator

-- Stage2A.lean
#print axioms Zeta7Stage2A.normalizeCoefficients
#print axioms Zeta7Stage2A.shifted_coefficient_rescaling
#print axioms Zeta7Stage2A.normalizeMatrix
#print axioms Zeta7Stage2A.normalizeMatrix_eq_diagonal
#print axioms Zeta7Stage2A.det_normalizeMatrix
#print axioms Zeta7Stage2A.det_normalizeMatrix_ne_zero
#print axioms Zeta7Stage2A.det_after_source_change
#print axioms Zeta7Stage2A.tailMatrix
#print axioms Zeta7Stage2A.normalizedTailMatrix
#print axioms Zeta7Stage2A.normalizedTailMatrix_eq
#print axioms Zeta7Stage2A.det_normalizedTailMatrix
#print axioms Zeta7Stage2A.identity_block_det
#print axioms Zeta7Stage2A.annular_weight_sum
#print axioms Zeta7Stage2A.baseline_plus_annular_weights
#print axioms Zeta7Stage2A.annularQ
#print axioms Zeta7Stage2A.annularQ_rescaling
#print axioms Zeta7Stage2A.annularQ_reciprocal

-- Stage2B.lean
#print axioms Zeta7Stage2B.p
#print axioms Zeta7Stage2B.c₁
#print axioms Zeta7Stage2B.c₀
#print axioms Zeta7Stage2B.forcing
#print axioms Zeta7Stage2B.recurrenceWeight
#print axioms Zeta7Stage2B.solution
#print axioms Zeta7Stage2B.solution_zero
#print axioms Zeta7Stage2B.solution_recurrence
#print axioms Zeta7Stage2B.H
#print axioms Zeta7Stage2B.euler
#print axioms Zeta7Stage2B.primitive
#print axioms Zeta7Stage2B.potential
#print axioms Zeta7Stage2B.quadratic
#print axioms Zeta7Stage2B.germs
#print axioms Zeta7Stage2B.coefficients
#print axioms Zeta7Stage2B.coeff_euler
#print axioms Zeta7Stage2B.coeff_primitive_zero
#print axioms Zeta7Stage2B.coeff_primitive_succ
#print axioms Zeta7Stage2B.derivative_primitive
#print axioms Zeta7Stage2B.coeff_jet
#print axioms Zeta7Stage2B.coeff_primitive_blocks
#print axioms Zeta7Stage2B.levelMatrix
#print axioms Zeta7Stage2B.normalizedLevelMatrix
#print axioms Zeta7Stage2B.levelMatrix_entry
#print axioms Zeta7Stage2B.normalizedLevelMatrix_eq
#print axioms Zeta7Stage2B.det_normalizedLevelMatrix
#print axioms Zeta7Stage2B.consecutiveRow
#print axioms Zeta7Stage2B.consecutiveRow_bounds
#print axioms Zeta7Stage2B.shiftedEuler
#print axioms Zeta7Stage2B.band
#print axioms Zeta7Stage2B.cleared_band_identity
#print axioms Zeta7Stage2B.cleared_potential_derivative
#print axioms Zeta7Stage2B.solution_linear
#print axioms Zeta7Stage2B.normalized_coefficients
#print axioms Zeta7Stage2B.primitive_rescaling
#print axioms Zeta7Stage2B.double_primitive_rescaling
#print axioms Zeta7Stage2B.fullMatrix
#print axioms Zeta7Stage2B.topRight
#print axioms Zeta7Stage2B.fullMatrix_blocks
#print axioms Zeta7Stage2B.det_fullMatrix
#print axioms Zeta7Stage2B.clearedOperator
#print axioms Zeta7Stage2B.coeff_poly_mul
#print axioms Zeta7Stage2B.coeff_clearedOperator
#print axioms Zeta7Stage2B.recurrenceWeight_zero
#print axioms Zeta7Stage2B.cleared_solution
#print axioms Zeta7Stage2B.cleared_H
#print axioms Zeta7Stage2B.quadratic_constant
#print axioms Zeta7Stage2B.germs_constants

-- Stage2Operator.lean
#print axioms Zeta7Stage2B.polynomial_coe_ofNat
#print axioms Zeta7Stage2B.potentialNumerator
#print axioms Zeta7Stage2B.p_constantCoeff
#print axioms Zeta7Stage2B.pUnit
#print axioms Zeta7Stage2B.eulerHom
#print axioms Zeta7Stage2B.euler_mul
#print axioms Zeta7Stage2B.potential_eq_unit
#print axioms Zeta7Stage2B.c₁_eq_potentialNumerator
#print axioms Zeta7Stage2B.c₀_eq_potentialNumerator_derivative
#print axioms Zeta7Stage2B.clearedOperator_identity

-- Zeta7Main.lean
#print axioms Zeta7Main.rational_cast_eq_algebraMap
#print axioms Zeta7Main.rational_embedding_injective
#print axioms Zeta7Main.isRationalSeven_iff_mem_range
#print axioms Zeta7Main.isRationalSeven_ratCast
#print axioms Zeta7Main.IrrationalityClaim

#print axioms Zeta7Partial.Enclosures
#print axioms Zeta7Partial.ThreePlaceData
#check @Zeta7Differential.cleared_operator
#check @Zeta7Stage2B.clearedOperator_identity
#check @Zeta7Partial.conditional_exclusion

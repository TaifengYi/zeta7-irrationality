import Zeta7Proof.ActualN4BoundedRows
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.NumberTheory.PrimeCounting

/-! Pinned local API inventory. No analytic or prime-asymptotic assertion. -/
#check @PadicInt.toZMod
#check @PadicInt.ker_toZMod
#check @PadicInt.norm_le_pow_iff_mem_span_pow
#check @Subtype.coe_injective
#check @Padic.norm_eq_zpow_neg_valuation
#check @Padic.valuation_ratCast
#check @Module.free_of_finite_type_torsion_free'
#check @Matrix.det_apply
#check @Matrix.det_mul
#check @Zeta7Common.commonDeterminant_eq_tail
#check @Zeta7Common.det_tailMatrix_map
#check @Zeta7Common.actualTailRow_lt
#check @Zeta7Jump.fullJumpRow
#print axioms Zeta7Common.actualTailRow_lt
#check @Nat.tendsto_primeCounting
#print axioms Nat.tendsto_primeCounting
#print axioms PadicInt.ker_toZMod
#print axioms Module.free_of_finite_type_torsion_free'
#print axioms Matrix.det_apply

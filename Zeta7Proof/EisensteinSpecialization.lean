import Zeta7Proof.TargetSeries
import PadicLFunctions.EisensteinFamily

/-! Evaluation of the constructed measure-valued Eisenstein family at weight
minus two. The constant is evaluated through an explicit regularizing witness;
it is not inserted as an assumed value. This is a formal family comparison. -/

set_option autoImplicit false
namespace Zeta7Main
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩
open PowerSeries PadicInt PadicLFunctions

theorem branch_three_neg_three_mul_cube (x : ℤ_[7]ˣ) :
    branchChar 7 3 (-3) x * (x : ℤ_[7]) ^ 3 = 1 := by
  have ht : (teichmuller 7 x : ℤ_[7]) ^ 6 = 1 := by
    simpa only [teichmuller_coe] using teichmullerFun_pow_card_sub_one 7 x
  have hx : (x : ℤ_[7]) =
      (teichmuller 7 x : ℤ_[7]) * (angleUnit 7 x : ℤ_[7]) :=
    (congrArg Units.val (teichmuller_mul_angleUnit 7 x)).symm
  have he := onePAdicPow_neg_nat_mul 7 (angleUnit 7 x : ℤ_[7])
    (angleUnit_sub_one_mem 7 x) 3
  norm_num only [Nat.cast_ofNat] at he
  rw [branchChar_apply, hx]
  calc
    _ = (teichmuller 7 x : ℤ_[7]) ^ 6 *
        (onePAdicPow 7 (angleUnit 7 x : ℤ_[7]) (angleUnit_sub_one_mem 7 x) (-3) *
          (angleUnit 7 x : ℤ_[7]) ^ 3) := by ring
    _ = 1 := by rw [ht, one_mul, he]

theorem branch_three_neg_three_eq_inv_cube (x : ℤ_[7]ˣ) :
    ((branchChar 7 3 (-3) x : ℤ_[7]) : ℚ_[7]) =
      ((((x : ℤ_[7]) : ℚ_[7]) ^ 3))⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  have h := congrArg (fun a : ℤ_[7] => (a : ℚ_[7])) (branch_three_neg_three_mul_cube x)
  simpa only [PadicInt.coe_mul, PadicInt.coe_pow, PadicInt.coe_one] using h

/-- The x-twist changes the inverse-cube character to the inverse square. -/
theorem inverse_cube_twist :
    PadicMeasure.unitsPowCM 7 1 * branchChar 7 3 (-3) = branchChar 7 4 (-2) := by
  ext x
  apply mul_right_cancel₀ (pow_ne_zero 2 x.ne_zero)
  change ((x : ℤ_[7]) ^ 1 * branchChar 7 3 (-3) x) * (x : ℤ_[7]) ^ 2 = _
  rw [branch_four_neg_two_mul_square]
  convert branch_three_neg_three_mul_cube x using 1 <;> ring

/-- Canonical numerator for the constant coefficient of the Eisenstein family. -/
noncomputable def eisensteinConstantNumerator : PadicMeasure 7 ℤ_[7]ˣ :=
  (((isUnit_two_padicInt 7 (by decide)).unit⁻¹ : ℤ_[7]ˣ) : ℤ_[7]) •
    unitsTwist 7 (PadicMeasure.zetaNum 7
      (PadicMeasure.exists_nat_topological_generator 7 (by decide)).choose)

theorem eisenstein_constant_witness :
    algebraMap _ (PadicMeasure.QuotientField 7)
        ((zetaSevenGenerator : ℤ_[7]) • PadicMeasure.dirac 7 zetaSevenGenerator - 1) *
      constantCoeff (eisensteinFamily 7 (by decide)) =
      algebraMap _ _ eisensteinConstantNumerator := by
  apply twistedZetaHalf_witness_eq
  rw [PadicMeasure.padicZeta]
  exact IsLocalization.mk'_spec' (PadicMeasure.QuotientField 7) _ _

noncomputable def eisensteinDenominator : ℚ_[7] :=
  ((zetaSevenGenerator : ℤ_[7]) : ℚ_[7]) *
    ((branchChar 7 3 (-3) zetaSevenGenerator : ℤ_[7]) : ℚ_[7]) - 1

theorem eisenstein_denominator_eq : eisensteinDenominator =
    ((branchChar 7 4 (1 - (3 : ℤ_[7])) zetaSevenGenerator : ℤ_[7]) : ℚ_[7]) - 1 := by
  have h := congrArg (fun f : C(ℤ_[7]ˣ, ℤ_[7]) =>
    ((f zetaSevenGenerator : ℤ_[7]) : ℚ_[7])) inverse_cube_twist
  change _ * _ = _ at h
  simpa [eisensteinDenominator, PadicMeasure.unitsPowCM,
    show 1 - (3 : ℤ_[7]) = -2 by ring] using
    congrArg (fun a : ℚ_[7] => a - 1) h

theorem eisenstein_denominator_ne_zero : eisensteinDenominator ≠ 0 := by
  rw [eisenstein_denominator_eq]
  exact zeta7Three_denominator_ne_zero

/-- Specialize the canonical witness at x^-3 and divide by its nonzero
regularizing factor; positive coefficients are evaluated divisor measures. -/
noncomputable def eisensteinMinusTwo : ℚ_[7]⟦X⟧ := mk fun n =>
  if n = 0 then
    eisensteinDenominator⁻¹ *
      ((eisensteinConstantNumerator (branchChar 7 3 (-3)) : ℤ_[7]) : ℚ_[7])
  else ((divisorMeasure 7 n (branchChar 7 3 (-3)) : ℤ_[7]) : ℚ_[7])

theorem eisensteinMinusTwo_constant : constantCoeff eisensteinMinusTwo = eta := by
  change eisensteinDenominator⁻¹ * _ = zeta7Three / 2
  have ht : unitsTwist 7 (PadicMeasure.zetaNum 7
      (PadicMeasure.exists_nat_topological_generator 7 (by decide)).choose)
      (branchChar 7 3 (-3)) =
    PadicMeasure.zetaNum 7
      (PadicMeasure.exists_nat_topological_generator 7 (by decide)).choose
      (branchChar 7 4 (-2)) := by
    change PadicMeasure.unitsCmul _ _ _ _ = _
    rw [PadicMeasure.unitsCmul_apply, inverse_cube_twist]
  rw [eisensteinConstantNumerator, LinearMap.smul_apply, smul_eq_mul, ht,
    PadicInt.coe_mul, coe_inv_two 7 (by decide), eisenstein_denominator_eq]
  unfold zeta7Three zetaSevenBranch zetaPBranch zetaSevenGenerator
  rw [show 1 - (3 : ℤ_[7]) = -2 by ring]
  ring

theorem divisorMeasure_inverse_cube (n : ℕ) :
    ((divisorMeasure 7 n (branchChar 7 3 (-3)) : ℤ_[7]) : ℚ_[7]) =
      (GCoeff n : ℚ_[7]) := by
  rw [divisorMeasure, LinearMap.coe_sum, Finset.sum_apply]
  simp only [PadicInt.coe_sum, PadicMeasure.dirac_apply, GCoeff,
    Rat.cast_sum, Rat.cast_inv, Rat.cast_pow, Rat.cast_natCast]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [branch_three_neg_three_eq_inv_cube, unitOfNat_coe 7 (Finset.mem_filter.mp hd).2]
  simp

theorem eisensteinMinusTwo_coeff {n : ℕ} (hn : n ≠ 0) :
    coeff n eisensteinMinusTwo =
      ∑ a ∈ n.divisors.filter (fun a => ¬ 7 ∣ a), ((a : ℚ_[7]) ^ 3)⁻¹ := by
  rw [eisensteinMinusTwo, coeff_mk, if_neg hn, divisorMeasure_inverse_cube]
  simp [GCoeff]

/-- All coefficients, including the independently evaluated constant witness. -/
theorem eisensteinMinusTwo_eq_G_add_eta :
    eisensteinMinusTwo = GSeries.map (algebraMap ℚ ℚ_[7]) + C eta := by
  ext n
  cases n with
  | zero =>
      simp only [map_add, coeff_map, coeff_C, ite_true]
      rw [coeff_zero_eq_constantCoeff, eisensteinMinusTwo_constant]
      simp [GSeries, GCoeff]
  | succ n =>
      simp [eisensteinMinusTwo, divisorMeasure_inverse_cube, GSeries, GCoeff]

/-- Any numerator representing this same localized coefficient has the same
evaluation. The witness premise is instantiated by eisenstein_constant_witness. -/
theorem eisenstein_constant_evaluation_unique (ν : PadicMeasure 7 ℤ_[7]ˣ)
    (hν : algebraMap _ (PadicMeasure.QuotientField 7)
        ((zetaSevenGenerator : ℤ_[7]) • PadicMeasure.dirac 7 zetaSevenGenerator - 1) *
      constantCoeff (eisensteinFamily 7 (by decide)) = algebraMap _ _ ν) :
    eisensteinDenominator⁻¹ * ((ν (branchChar 7 3 (-3)) : ℤ_[7]) : ℚ_[7]) = eta := by
  have h : ν = eisensteinConstantNumerator := by
    apply IsFractionRing.injective (PadicMeasure 7 ℤ_[7]ˣ) (PadicMeasure.QuotientField 7)
    rw [← hν, eisenstein_constant_witness]
  subst ν
  exact eisensteinMinusTwo_constant

/-- Closed comparison with the actual localized family: existence of the
constant witness, valid division, its target value, and all positive measures. -/
theorem target_family_specialization :
    eisensteinDenominator ≠ 0 ∧
    (∃ ν : PadicMeasure 7 ℤ_[7]ˣ,
      algebraMap _ (PadicMeasure.QuotientField 7)
          ((zetaSevenGenerator : ℤ_[7]) • PadicMeasure.dirac 7 zetaSevenGenerator - 1) *
        constantCoeff (eisensteinFamily 7 (by decide)) = algebraMap _ _ ν ∧
      eisensteinDenominator⁻¹ * ((ν (branchChar 7 3 (-3)) : ℤ_[7]) : ℚ_[7]) = eta) ∧
    ∀ n : ℕ, n ≠ 0 →
      coeff n (eisensteinFamily 7 (by decide)) =
        algebraMap _ (PadicMeasure.QuotientField 7) (divisorMeasure 7 n) ∧
      ((divisorMeasure 7 n (branchChar 7 3 (-3)) : ℤ_[7]) : ℚ_[7]) =
        coeff n (GSeries.map (algebraMap ℚ ℚ_[7]) + C eta) := by
  refine ⟨eisenstein_denominator_ne_zero,
    ⟨eisensteinConstantNumerator, eisenstein_constant_witness, eisensteinMinusTwo_constant⟩,
    fun n hn => ⟨?_, ?_⟩⟩
  · simp [eisensteinFamily, hn]
  · simp [divisorMeasure_inverse_cube, GSeries, coeff_C, hn]

end Zeta7Main

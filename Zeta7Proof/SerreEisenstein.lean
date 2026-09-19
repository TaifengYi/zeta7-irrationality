import Zeta7Proof.EisensteinUniform
import Zeta7Proof.SerreModularForm

/-! The actual level-one classical modular forms supplying the uniform limit.
Their rational expansions have constant zeta(1-k)/2 and full divisor sums.
The endpoint concerns the preserved measure specialization with constant eta. -/

set_option autoImplicit false
noncomputable section
namespace Zeta7Main
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩
open PowerSeries PadicLFunctions UpperHalfPlane
open scoped MatrixGroups

def classicalEisensteinForm (r : ℕ) : ModularForm 𝒮ℒ (serreWeight r : ℤ) :=
  (((zetaNeg (serreWeight r - 1) : ℚ) : ℂ) / 2) •
    ModularForm.E (by have := serreWeight_ge_four r; omega)

/-- Agreement with the pre-existing classical Eisenstein normalization. -/
theorem classicalEisensteinForm_apply (r : ℕ) (z : ℍ) :
    classicalEisensteinForm r z =
      rjwEisenstein (k := serreWeight r) (by have := serreWeight_ge_four r; omega) z := rfl

/-- The classical source is a genuine modular form, with the exact rational expansion. -/
theorem classicalEisensteinForm_qExpansion (r : ℕ) :
    qExpansion 1 (classicalEisensteinForm r) =
      (classicalRationalSeries r).map (algebraMap ℚ ℂ) := by
  ext n
  rw [classicalEisensteinForm, FunLike.coe_smul,
    ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL]
  simp only [coeff_smul, EisensteinSeries.E_qExpansion_coeff _ (serreWeight_even r),
    coeff_map, classicalRationalSeries, coeff_mk, fullEisensteinCoeff]
  by_cases hn : n = 0
  · simp [hn]
  · simp only [hn, ite_false, smul_eq_mul, map_sum, map_pow, map_natCast]
    have h := rjw_normalisation (serreWeight_ge_four r) (serreWeight_even r)
    have hs : (ArithmeticFunction.sigma (serreWeight r - 1) n : ℂ) =
        ∑ d ∈ n.divisors, (d : ℂ) ^ (serreWeight r - 1) := by
      rw [ArithmeticFunction.sigma_apply]
      push_cast
      rfl
    rw [← hs]
    linear_combination (ArithmeticFunction.sigma (serreWeight r - 1) n : ℂ) * h

def classicalRationalEisenstein (r : ℕ) : rationalModularForms (serreWeight r : ℤ) :=
  ⟨classicalRationalSeries r, classicalEisensteinForm r, classicalEisensteinForm_qExpansion r⟩

theorem classicalRationalEisenstein_qExpansion (r : ℕ) :
    (ModularForm.rationalQExpansion (classicalRationalEisenstein r)).map
      (algebraMap ℚ ℚ_[7]) = classicalEisensteinSeries r := rfl

/-- Every field is constructed; uniform convergence is the proved target theorem. -/
def eisensteinMinusTwo_serrePresentation : pAdicModularFormStruct eisensteinMinusTwo where
  w r := serreWeight r
  F := classicalRationalEisenstein
  tendsTo := by
    convert classical_eisenstein_tendstoUniformly using 1
    funext r n
    change ((coeff n (classicalRationalSeries r) : ℚ) : ℚ_[7]) =
      coeff n ((classicalRationalSeries r).map (algebraMap ℚ ℚ_[7]))
    simp

/-- Serre seven-adic modularity of the already evaluated family, unconditionally. -/
theorem eisensteinMinusTwo_isPAdicModularForm :
    PowerSeries.isPAdicModularForm 7 eisensteinMinusTwo :=
  ⟨eisensteinMinusTwo_serrePresentation⟩

end Zeta7Main

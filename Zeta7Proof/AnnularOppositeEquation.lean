import Zeta7Proof.AnnularOppositeTarget

/-! The actual target equation on the existing y-annulus, with geometric P inverse. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
namespace Zeta7Annulus.ClosedAnnulus
local instance AnnularOppositeEquation_prime : Fact (Nat.Prime 7) := ⟨by decide⟩
local instance AnnularOppositeEquation_radius : Fact (0 < (7 : ℝ)) := ⟨by norm_num⟩

def oppositeMultiplier : ClosedAnnulus 7 7 := monomial (r := 7) (R := 7) (-2) (1 / 49)
def oppositeForcingNumerator : ClosedAnnulus 7 7 := constant (10 / 49) + monomial (r := 7) (R := 7) 1 1
def oppositeForcing : ClosedAnnulus 7 7 := oppositeForcingNumerator * pInverse
def potentialNumerator : ClosedAnnulus 7 7 :=
  8 * monomial (r := 7) (R := 7) 1 1 * (1 + 16 * monomial (r := 7) (R := 7) 1 1 + 49 * (monomial (r := 7) (R := 7) 1 1) ^ 2)

theorem oppositeP_factorization : oppositeP = oppositeMultiplier * annularP := by
  unfold oppositeP oppositeX oppositeMultiplier annularP
  rw [← map_ofNat constant 13, ← map_ofNat constant 49]
  change monomial (r := 7) (R := 7) 0 1 + monomial (r := 7) (R := 7) 0 13 * monomial (r := 7) (R := 7) (-1) (49 : ℚ_[7])⁻¹ +
    monomial (r := 7) (R := 7) 0 49 * (monomial (r := 7) (R := 7) (-1) (49 : ℚ_[7])⁻¹) ^ 2 =
      monomial (r := 7) (R := 7) (-2) (1 / 49) * (monomial (r := 7) (R := 7) 0 1 + monomial (r := 7) (R := 7) 1 13 + monomial (r := 7) (R := 7) 2 49)
  simp only [pow_two, mul_add, monomial_mul]
  norm_num
  abel

theorem oppositeW_factorization : oppositeW = oppositeMultiplier ^ 2 * potentialNumerator := by
  unfold oppositeW oppositeX oppositeMultiplier potentialNumerator
  simp only [← map_ofNat constant 8, ← map_ofNat constant 16, ← map_ofNat constant 49]
  change monomial (r := 7) (R := 7) 0 8 * monomial (r := 7) (R := 7) (-1) (49 : ℚ_[7])⁻¹ *
      (monomial (r := 7) (R := 7) 0 1 + monomial (r := 7) (R := 7) 0 16 * monomial (r := 7) (R := 7) (-1) (49 : ℚ_[7])⁻¹ +
        monomial (r := 7) (R := 7) 0 49 * (monomial (r := 7) (R := 7) (-1) (49 : ℚ_[7])⁻¹) ^ 2) =
    (monomial (r := 7) (R := 7) (-2) (1 / 49)) ^ 2 * (monomial (r := 7) (R := 7) 0 8 * monomial (r := 7) (R := 7) 1 1 *
      (monomial (r := 7) (R := 7) 0 1 + monomial (r := 7) (R := 7) 0 16 * monomial (r := 7) (R := 7) 1 1 + monomial (r := 7) (R := 7) 0 49 * (monomial (r := 7) (R := 7) 1 1) ^ 2))
  simp only [pow_two, mul_add, monomial_mul]
  norm_num
  abel

theorem oppositeS_factorization : oppositeS = oppositeMultiplier * oppositeForcingNumerator := by
  unfold oppositeS oppositeX oppositeMultiplier oppositeForcingNumerator
  rw [← map_ofNat constant 10]
  change monomial (r := 7) (R := 7) (-1) (49 : ℚ_[7])⁻¹ *
      (monomial (r := 7) (R := 7) 0 1 + monomial (r := 7) (R := 7) 0 10 * monomial (r := 7) (R := 7) (-1) (49 : ℚ_[7])⁻¹) =
    monomial (r := 7) (R := 7) (-2) (1 / 49) * (monomial (r := 7) (R := 7) 0 (10 / 49) + monomial (r := 7) (R := 7) 1 1)
  simp only [mul_add, monomial_mul]
  norm_num
  abel

theorem oppositeP_isUnit : IsUnit oppositeP := by
  rw [oppositeP_factorization]
  exact (monomial_isUnit (-2) (by norm_num : (1 / 49 : ℚ_[7]) ≠ 0)).mul
    (annularP_isUnit (by norm_num) (by norm_num) le_rfl)

theorem potentialNumerator_clear :
    annularP ^ 2 * annularPotential (r := 7) (R := 7) = potentialNumerator := by
  rw [annularPotential_clear (by norm_num) (by norm_num) le_rfl]
  simp only [Zeta7AnnularRows.V_numerator, map_mul, map_add, map_pow, map_one, map_ofNat,
    rationalPolynomialMap_X, potentialNumerator]

theorem oppositePotential_clear : oppositeP ^ 2 * annularPotential = oppositeW := by
  rw [oppositeP_factorization, oppositeW_factorization]
  linear_combination oppositeMultiplier ^ 2 * potentialNumerator_clear

theorem oppositeForcing_clear : oppositeP * oppositeForcing = oppositeS := by
  rw [oppositeP_factorization, oppositeS_factorization, oppositeForcing]
  have hp := annularP_mul_inverse (r := 7) (R := 7) (by norm_num) (by norm_num) le_rfl
  linear_combination oppositeMultiplier * oppositeForcingNumerator * hp

theorem oppositePotential_derivative_clear :
    oppositeP ^ 3 * euler (annularPotential (r := 7) (R := 7)) =
      oppositeP * euler oppositeW - 2 * oppositeW * euler oppositeP := by
  have he := congrArg euler oppositePotential_clear
  simp only [pow_two, euler_mul] at he
  linear_combination oppositeP * he - 2 * euler oppositeP * oppositePotential_clear

theorem oppositeTarget_differential_equation : annularL (oppositeGerm 0) = -oppositeForcing := by
  apply (oppositeP_isUnit.pow 3).mul_left_cancel
  have hhalf : (constant (r := 7) (R := 7) (1 / 2 : ℚ_[7])) * 2 = 1 := by
    rw [← map_ofNat constant 2, ← map_mul]; norm_num
  unfold annularL
  linear_combination -oppositeTarget_cleared_equation -
    oppositeP * euler (oppositeGerm 0) * oppositePotential_clear -
    constant (1 / 2 : ℚ_[7]) * oppositeGerm 0 * oppositePotential_derivative_clear +
    oppositeP ^ 2 * oppositeForcing_clear +
    oppositeW * euler oppositeP * oppositeGerm 0 * hhalf

theorem oppositeK_derivative : euler (oppositeGerm 3) = -oppositeForcing * oppositeGerm 0 := by
  apply oppositeP_isUnit.mul_left_cancel
  linear_combination oppositeK_cleared_derivative + oppositeGerm 0 * oppositeForcing_clear

theorem correctedSolution_opposite_forcing :
    annularL (correctedSolutionOn (r := 7) (R := 7) (by norm_num) le_rfl) =
      -annularQuadraticAtInverse * oppositeForcing := by
  rw [correctedSolutionOn_forcing (by norm_num) (by norm_num) le_rfl]
  have he : constant (r := 7) (R := 7) (1 / 49 : ℚ_[7]) * (10 + 49 * monomial (r := 7) (R := 7) 1 1) =
      oppositeForcingNumerator := by
    rw [oppositeForcingNumerator, mul_add, ← map_ofNat constant 10, ← map_ofNat constant 49,
      ← mul_assoc, ← map_mul, map_mul]
    have h1 : constant (r := 7) (R := 7) (1 / 49 : ℚ_[7]) * constant 49 = 1 := by
      rw [← map_mul]; norm_num
    rw [h1, one_mul]
    congr 1
    rw [← map_mul]
    congr 1; ring
  unfold oppositeForcing
  linear_combination -annularQuadraticAtInverse * pInverse * he

end Zeta7Annulus.ClosedAnnulus

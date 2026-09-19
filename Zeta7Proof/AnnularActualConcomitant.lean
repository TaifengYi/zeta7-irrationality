import Zeta7Proof.AnnularOppositeEquation

/-! The actual concomitant and primitive cancellation on the y-annulus. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
namespace Zeta7Annulus.ClosedAnnulus
local instance AnnularActualConcomitant_prime : Fact (Nat.Prime 7) := ⟨by decide⟩
local instance AnnularActualConcomitant_radius : Fact (0 < (7 : ℝ)) := ⟨by norm_num⟩

def actualVStar : ClosedAnnulus 7 7 := correctedSolutionOn (by norm_num) le_rfl
def oppositeHPrime : ClosedAnnulus 7 7 :=
  constant annularQuadratic₁ + monomial (-1) (2 * annularQuadratic₂)
def oppositeHSecond : ClosedAnnulus 7 7 := constant (2 * annularQuadratic₂)
def oppositePrimitiveCombination : ClosedAnnulus 7 7 :=
  annularQuadraticAtInverse * oppositeGerm 3 -
    constant 49 * oppositeHPrime * oppositeGerm 4 +
    constant (49 ^ 2) * oppositeHSecond * oppositeGerm 5

def concomitant (v H : ClosedAnnulus 7 7) : ClosedAnnulus 7 7 :=
  v * euler (euler H) - euler v * euler H +
    (euler (euler v) - annularPotential * v) * H

theorem concomitant_derivative (v H : ClosedAnnulus 7 7) :
    euler (concomitant v H) = v * annularL H + H * annularL v := by
  have hh : constant (r := 7) (R := 7) (1 / 2 : ℚ_[7]) * 2 = 1 := by
    rw [← map_ofNat constant 2, ← map_mul]; norm_num
  simp only [concomitant, euler_add, euler_sub, euler_mul, annularL]
  linear_combination euler annularPotential * v * H * hh

theorem oppositeH_derivative : euler (annularQuadraticAtInverse (r := 7) (R := 7)) =
    -(monomial (-1) 1 * oppositeHPrime) := by
  simp only [annularQuadraticAtInverse, oppositeHPrime, euler_add, euler_constant,
    euler_monomial, zero_add, mul_add]
  change monomial (-1) ((-1 : ℚ_[7]) * annularQuadratic₁) +
    monomial (-2) ((-2 : ℚ_[7]) * annularQuadratic₂) =
      -(monomial (-1) 1 * monomial 0 annularQuadratic₁ + monomial (-1) 1 * monomial (-1) (2 * annularQuadratic₂))
  simp only [monomial_mul, one_mul]
  ext k
  simp only [coeffs_add, coeffs_neg, Pi.add_apply, Pi.neg_apply, monomial_coeffs, bilateralMonomial]
  norm_num
  split_ifs <;> ring

theorem oppositeHPrime_derivative : euler oppositeHPrime = -(monomial (-1) 1 * oppositeHSecond) := by
  simp only [oppositeHPrime, euler_add, euler_constant, zero_add, euler_monomial]
  change monomial (-1) ((-1 : ℚ_[7]) * (2 * annularQuadratic₂)) =
    -(monomial (-1) 1 * monomial 0 (2 * annularQuadratic₂))
  rw [monomial_mul]
  ext k
  simp only [coeffs_neg, monomial_coeffs, Pi.neg_apply, bilateralMonomial]
  norm_num
  split_ifs <;> ring

theorem oppositeHSecond_derivative : euler oppositeHSecond = 0 := euler_constant _

theorem oppositeX_scale : constant (r := 7) (R := 7) 49 * oppositeX = monomial (-1) 1 := by
  change monomial 0 49 * monomial (-1) (49 : ℚ_[7])⁻¹ = _
  rw [monomial_mul]
  norm_num

theorem oppositePrimitiveCombination_derivative :
    euler oppositePrimitiveCombination =
      -annularQuadraticAtInverse * oppositeForcing * oppositeGerm 0 := by
  have hc : constant (r := 7) (R := 7) (49 ^ 2 : ℚ_[7]) = constant 49 * constant 49 := by
    rw [← map_mul]; congr 1; ring
  simp only [oppositePrimitiveCombination, euler_add, euler_sub, euler_mul,
    euler_constant, zero_mul, zero_add, oppositeH_derivative,
    oppositeHPrime_derivative, oppositeHSecond_derivative,
    oppositeK_derivative, oppositeJ1_derivative, oppositeJ2_derivative, hc]
  linear_combination (oppositeHPrime * oppositeGerm 3 -
    constant 49 * oppositeHSecond * oppositeGerm 4) * oppositeX_scale

def actualConcomitantRemainder : ClosedAnnulus 7 7 :=
  oppositePrimitiveCombination - concomitant actualVStar (oppositeGerm 0)

theorem actualConcomitantRemainder_derivative : euler actualConcomitantRemainder =
    oppositeForcingNumerator * correctedPartOn (r := 7) (R := 7) (by norm_num) le_rfl := by
  have hv : annularL actualVStar = -annularQuadraticAtInverse * oppositeForcing :=
    correctedSolution_opposite_forcing
  rw [actualConcomitantRemainder, euler_sub, oppositePrimitiveCombination_derivative,
    concomitant_derivative, oppositeTarget_differential_equation, hv]
  have hp := annularP_mul_inverse (r := 7) (R := 7) (by norm_num) (by norm_num) le_rfl
  unfold actualVStar correctedSolutionOn oppositeForcing
  linear_combination oppositeForcingNumerator * correctedPartOn (r := 7) (R := 7)
    (by norm_num) le_rfl * hp

theorem actualConcomitantRemainder_below {k : ℤ} (hk : k < -2) :
    actualConcomitantRemainder.coeffs k = 0 := by
  have he := congrArg (fun a : ClosedAnnulus 7 7 => a.coeffs k) actualConcomitantRemainder_derivative
  have hc : (correctedPartOn (r := 7) (R := 7) (by norm_num) le_rfl).coeffs = annularCorrectedPart := by
    simp only [correctedPartOn, coeffs_sub, monomial_coeffs, annularCorrectedPart]
    rfl
  simp only [oppositeForcingNumerator, add_mul, coeffs_add, Pi.add_apply] at he
  rw [coeffs_constant_mul] at he
  simp only [coeffs_mul, monomial_coeffs, bilateralMonomial_convolution, hc, Pi.add_apply,
    annularCorrectedPart_below hk, annularCorrectedPart_below (by omega : k - 1 < -2),
    mul_zero, add_zero] at he
  change (k : ℚ_[7]) * actualConcomitantRemainder.coeffs k = 0 at he
  exact (mul_eq_zero.mp he).resolve_left (by exact_mod_cast (by omega : k ≠ 0))

end Zeta7Annulus.ClosedAnnulus

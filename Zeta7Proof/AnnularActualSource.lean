import Zeta7Proof.AnnularPolynomialCoefficients

/-! Actual integral source polynomial and fixed completion cost, using the
constructed six coefficients, with no unproved integrality or nonvanishing premise. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
namespace Zeta7Annulus
local instance AnnularActualSource_prime : Fact (Nat.Prime 7) := ⟨by decide⟩
local instance AnnularActualSource_radius : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
open Polynomial

theorem seven_four_integral {z : ℚ_[7]} (hz : ‖z‖ ≤ (2401 : ℝ)) :
    ‖(7 : ℚ_[7]) ^ 4 * z‖ ≤ 1 := by
  have h7 : ‖(7 : ℚ_[7])‖ = (1 / 7 : ℝ) := by simpa using Padic.norm_p (p := 7)
  have hn : ‖(7 : ℚ_[7]) ^ 4‖ ≤ (1 / 2401 : ℝ) := by rw [norm_pow, h7]; norm_num
  exact (padic_mul_bound hn hz).trans (by norm_num)

def integralAnnularQuadratic₀ : ℤ_[7] :=
  ⟨7 ^ 4 * annularQuadratic₀, seven_four_integral (annularQuadratic_bounds.1.trans (by norm_num))⟩
def integralAnnularQuadratic₁ : ℤ_[7] :=
  ⟨7 ^ 4 * annularQuadratic₁, seven_four_integral annularQuadratic_bounds.2.1⟩
def integralAnnularQuadratic₂ : ℤ_[7] :=
  ⟨7 ^ 4 * annularQuadratic₂, seven_four_integral (annularQuadratic_bounds.2.2.trans (by norm_num))⟩

def integralAnnularQuadratic : Polynomial ℤ_[7] :=
  C integralAnnularQuadratic₀ + C integralAnnularQuadratic₁ * X + C integralAnnularQuadratic₂ * X ^ 2

def actualIntegralSourcePolynomial : Polynomial ℤ_[7] :=
  (49 + 13 * X + X ^ 2) ^ 2 * integralAnnularQuadratic

theorem integralAnnularQuadratic_map :
    integralAnnularQuadratic.map (algebraMap ℤ_[7] ℚ_[7]) = C (7 ^ 4) * annularForcingQuadratic := by
  simp only [integralAnnularQuadratic, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X]
  change C ((7 : ℚ_[7]) ^ 4 * annularQuadratic₀) +
    C (7 ^ 4 * annularQuadratic₁) * X + C (7 ^ 4 * annularQuadratic₂) * X ^ 2 = _
  unfold annularForcingQuadratic
  polynomial

theorem actualIntegralSourcePolynomial_map :
    actualIntegralSourcePolynomial.map (algebraMap ℤ_[7] ℚ_[7]) =
      C (7 ^ 4) * (ClosedAnnulus.reflectedQPolynomial ^ 2 * annularForcingQuadratic) := by
  simp only [actualIntegralSourcePolynomial, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_add, Polynomial.map_ofNat, Polynomial.map_X, integralAnnularQuadratic_map,
    ClosedAnnulus.reflectedQPolynomial]
  ring

theorem actualIntegralSourcePolynomial_ne_zero : actualIntegralSourcePolynomial ≠ 0 := by
  intro hz
  have hm := actualIntegralSourcePolynomial_map
  rw [hz, Polynomial.map_zero] at hm
  have hq : ClosedAnnulus.reflectedQPolynomial ≠ 0 := by
    intro h
    have h0 := congrArg (fun f : Polynomial ℚ_[7] => f.coeff 0) h
    norm_num [ClosedAnnulus.reflectedQPolynomial] at h0
  exact (mul_ne_zero (by norm_num) (mul_ne_zero (pow_ne_zero 2 hq)
    annularForcingQuadratic_ne_zero)) hm.symm

theorem actualIntegralSourcePolynomial_degree : actualIntegralSourcePolynomial.natDegree ≤ 6 := by
  unfold actualIntegralSourcePolynomial integralAnnularQuadratic
  compute_degree!

theorem actualAnnularCoefficients_K (k : ℤ) : actualAnnularCoefficients 3 k =
    Zeta7AnnularSource.coeffInt
      (ClosedAnnulus.reflectedQPolynomial ^ 2 * annularForcingQuadratic) k := by
  change (ClosedAnnulus.reflectedQ ^ 2 * ClosedAnnulus.padicPolynomialMap annularForcingQuadratic).coeffs k = _
  rw [ClosedAnnulus.reflectedQ, ← map_pow, ← map_mul, ClosedAnnulus.padicPolynomialMap_coefficients]

theorem actualIntegralAnnularCoefficients_K : actualIntegralAnnularCoefficients 3 =
    Zeta7AnnularSource.coeffInt actualIntegralSourcePolynomial := by
  funext k
  apply Subtype.ext
  rw [actualIntegralAnnularCoefficients_cast, actualAnnularCoefficients_K]
  unfold Zeta7AnnularSource.coeffInt
  split_ifs with hk
  · have hm := congrArg (fun f : Polynomial ℚ_[7] => f.coeff k.toNat) actualIntegralSourcePolynomial_map
    simpa only [Polynomial.coeff_map, Polynomial.coeff_C_mul, PadicInt.algebraMap_apply] using hm.symm
  · simp

/-- Fixed witnesses are chosen before the universal degree binder. This is
the exact original-column completion and its actual valuation cost. -/
theorem actualAnnularSourceCompletion_cost :
    ∃ (a ell : ℕ) (hell : ell ≤ 6), ∀ d : ℕ,
      (Zeta7AnnularSource.sourceCompletion actualIntegralAnnularCoefficients d ell hell).det ≠ 0 ∧
      (Zeta7AnnularSource.sourceCompletion actualIntegralAnnularCoefficients d ell hell).det.valuation =
        a * (d - 6) :=
  Zeta7AnnularSource.exists_sourceCompletion_cost actualIntegralAnnularCoefficients
    actualIntegralSourcePolynomial actualIntegralAnnularCoefficients_K
    actualIntegralSourcePolynomial_degree actualIntegralSourcePolynomial_ne_zero

end Zeta7Annulus

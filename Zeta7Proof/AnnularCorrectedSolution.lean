import Zeta7Proof.AnnularForcingCorrection

/-! The correction is applied to the actual split solution. Its forcing is
identified in the annulus algebra, including its sign and factor 49. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
namespace Zeta7Annulus
local instance AnnularCorrectedSolution_local1 : Fact (Nat.Prime 7) := ⟨by decide⟩

theorem bilateralBand_monomial_neg_two (z : ℚ_[7]) :
    bilateralBand (bilateralMonomial (-2) z) =
      bilateralMonomial (-2) (-8 * z) + bilateralMonomial (-1) (-105 * z) +
      bilateralMonomial 0 (-433 * z) + bilateralMonomial 1 (-441 * z) := by
  funext k
  by_cases h0 : k = -2
  · subst k; norm_num [bilateralBand, bilateralMonomial, bandWeight₀, bandWeight₁,
      bandWeight₂, bandWeight₃, bandWeight₄]
  by_cases h1 : k = -1
  · subst k; norm_num [bilateralBand, bilateralMonomial, bandWeight₀, bandWeight₁,
      bandWeight₂, bandWeight₃, bandWeight₄]
  by_cases h2 : k = 0
  · subst k; norm_num [bilateralBand, bilateralMonomial, bandWeight₀, bandWeight₁,
      bandWeight₂, bandWeight₃, bandWeight₄]
  by_cases h3 : k = 1
  · subst k; norm_num [bilateralBand, bilateralMonomial, bandWeight₀, bandWeight₁,
      bandWeight₂, bandWeight₃, bandWeight₄]
  by_cases h4 : k = 2
  · subst k; norm_num [bilateralBand, bilateralMonomial, bandWeight₀, bandWeight₁,
      bandWeight₂, bandWeight₃, bandWeight₄]
  simp only [bilateralBand, bilateralMonomial, Pi.add_apply, if_neg h0, if_neg h1,
    if_neg h2, if_neg h3, if_neg (by omega : k - 1 ≠ -2),
    if_neg (by omega : k - 2 ≠ -2), if_neg (by omega : k - 3 ≠ -2),
    if_neg (by omega : k - 4 ≠ -2), mul_zero, add_zero]

namespace ClosedAnnulus
variable {r R : ℝ} [Fact (0 < r)] [Fact (0 < R)]

def positivePartOn (hR : R < 49) (hrR : r ≤ R) : ClosedAnnulus r R :=
  ⟨annularPositivePart, annularPositivePart_decays r Fact.out (hrR.trans_lt hR),
    annularPositivePart_decays R Fact.out hR⟩

def correctedPartOn (hR : R < 49) (hrR : r ≤ R) : ClosedAnnulus r R :=
  positivePartOn hR hrR - monomial (-2) annularCorrectionConstant

def correctedSolutionOn (hR : R < 49) (hrR : r ≤ R) : ClosedAnnulus r R :=
  annularP * correctedPartOn hR hrR

theorem correctedSolutionOn_cleared (hr : 1 < r) (hR : R < 49) (hrR : r ≤ R) :
    annularP * annularL (correctedSolutionOn (r := r) hR hrR) =
      monomial (-2) correctedForcing₀ + monomial (-1) correctedForcing₁ +
      monomial 0 correctedForcing₂ + monomial 1 correctedForcing₃ := by
  change annularS (correctedPartOn hR hrR) = _
  ext k
  rw [coeff_annularS hr hR hrR]
  simp only [correctedPartOn, coeffs_sub, monomial_coeffs]
  change bilateralBand (annularPositivePart - bilateralMonomial (-2) annularCorrectionConstant) k = _
  rw [bilateralBand_sub, bilateralBand_monomial_neg_two]
  change annularFiniteForcing k - _ = _
  rw [annularFiniteForcing_four_terms]
  simp only [Pi.sub_apply, Pi.add_apply, coeffs_add, monomial_coeffs,
    correctedForcing₀, correctedForcing₁, correctedForcing₂, correctedForcing₃,
    bilateralMonomial]
  split_ifs <;> ring

def padicPolynomialMap : Polynomial ℚ_[7] →+* ClosedAnnulus r R :=
  Polynomial.eval₂RingHom constant (monomial 1 1)

theorem padicPolynomialMap_C (z : ℚ_[7]) :
    padicPolynomialMap (r := r) (R := R) (Polynomial.C z) = constant z := Polynomial.eval₂_C _ _

theorem padicPolynomialMap_X : padicPolynomialMap (r := r) (R := R) Polynomial.X = monomial 1 1 :=
  Polynomial.eval₂_X _ _

theorem padicPolynomialMap_C_mul_X_pow (z : ℚ_[7]) (n : ℕ) :
    padicPolynomialMap (r := r) (R := R) (Polynomial.C z * Polynomial.X ^ n) = monomial n z := by
  rw [map_mul, map_pow, padicPolynomialMap_C, padicPolynomialMap_X]
  exact constant_mul_Y_pow z n

theorem correctedSolutionOn_polynomial (hr : 1 < r) (hR : R < 49) (hrR : r ≤ R) :
    monomial 2 1 * (annularP * annularL (correctedSolutionOn (r := r) hR hrR)) =
      padicPolynomialMap annularCorrectedForcingPolynomial := by
  rw [correctedSolutionOn_cleared hr hR hrR, annularCorrectedForcing_coefficients]
  simp only [mul_add, monomial_mul, one_mul, map_add, padicPolynomialMap_C,
    padicPolynomialMap_C_mul_X_pow]
  rw [map_mul, padicPolynomialMap_C, padicPolynomialMap_X]
  have hm : constant (r := r) (R := R) correctedForcing₁ * monomial 1 1 = monomial 1 correctedForcing₁ := by
    simpa only [pow_one, Nat.cast_one] using constant_mul_Y_pow (r := r) (R := R) correctedForcing₁ 1
  rw [hm]
  rfl

def annularQuadraticAtInverse : ClosedAnnulus r R :=
  constant annularQuadratic₀ + monomial (-1) annularQuadratic₁ + monomial (-2) annularQuadratic₂

theorem annularQuadraticAtInverse_clear :
    monomial (r := r) (R := R) 2 1 * annularQuadraticAtInverse =
      padicPolynomialMap annularForcingReversed := by
  simp only [annularQuadraticAtInverse, annularForcingReversed, mul_add, map_add,
    padicPolynomialMap_C_mul_X_pow, padicPolynomialMap_C, map_mul, map_pow,
    padicPolynomialMap_X, monomial_Y_pow]
  change monomial (r := r) (R := R) 2 1 * monomial 0 annularQuadratic₀ +
    monomial 2 1 * monomial (-1) annularQuadratic₁ + monomial 2 1 * monomial (-2) annularQuadratic₂ =
    monomial 0 annularQuadratic₀ * monomial 2 1 +
      monomial 0 annularQuadratic₁ * monomial 1 1 + monomial 0 annularQuadratic₂
  simp only [monomial_mul, one_mul, mul_one]
  rfl

theorem correctedSolutionOn_forcing (hr : 1 < r) (hR : R < 49) (hrR : r ≤ R) :
    annularL (correctedSolutionOn (r := r) hR hrR) =
      -(constant (1 / 49 : ℚ_[7]) * annularQuadraticAtInverse *
        (10 + 49 * monomial 1 1) * pInverse) := by
  have h := correctedSolutionOn_polynomial hr hR hrR
  rw [annularCorrectedForcing_factorization] at h
  simp only [map_mul, map_add, map_ofNat, padicPolynomialMap_C, padicPolynomialMap_X,
    neg_div, map_neg, ← annularQuadraticAtInverse_clear] at h
  apply ((monomial_isUnit (r := r) (R := R) 2 (by norm_num : (1 : ℚ_[7]) ≠ 0)).mul
    (annularP_isUnit hr hR hrR)).mul_left_cancel
  have hp := annularP_mul_inverse hr hR hrR
  linear_combination h + (monomial 2 1 * constant (1 / 49 : ℚ_[7]) * annularQuadraticAtInverse *
    (10 + 49 * monomial 1 1)) * hp

end ClosedAnnulus
end Zeta7Annulus

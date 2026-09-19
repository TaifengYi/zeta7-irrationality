import Zeta7Proof.AnnularRowTransport
import Zeta7Proof.AnnularGlobalCandidates

/-! The homogeneous differential equation for the original convergent candidate. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
namespace Zeta7Annulus.ClosedAnnulus
local instance AnnularHomogeneousSolution_local1 : Fact (Nat.Prime 7) := ⟨by decide⟩
variable {r R : ℝ} [Fact (0 < r)] [Fact (0 < R)]

theorem actualAnnularRow_residual (hr : 1 < r) (hR : R < 49) (hrR : r ≤ R) (i : Fin 4) :
    actualAnnularRow (r := r) (R := R) 3 i - annularPotential * actualAnnularRow 1 i -
      constant (1 / 2 : ℚ_[7]) * euler annularPotential * actualAnnularRow 0 i = 0 := by
  have h := congrArg (rationalPolynomialMap (r := r) (R := R))
    (Zeta7AnnularRows.indexed_residual i)
  simp only [map_sub, map_mul, map_pow, map_zero, rationalPolynomialMap_C,
    Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, ← annularP_polynomial] at h
  simp only [← actualAnnularRow_clear hr hR hrR, ← annularPotential_clear hr hR hrR,
    ← annularPotential_euler_clear hr hR hrR] at h
  apply ((pnDenominator_isUnit hr hR hrR 4 10).mul ((annularP_isUnit hr hR hrR).pow 3)).mul_left_cancel
  rw [mul_zero]
  linear_combination h

theorem actualAnnularRow_initial (hr : 1 < r) (hR : R < 49) (hrR : r ≤ R) :
    actualAnnularRow (r := r) (R := R) 0 0 = annularT * nInverse ^ 2 := by
  apply (pnDenominator_isUnit hr hR hrR 4 10).mul_left_cancel
  rw [actualAnnularRow_clear hr hR hrR, Zeta7AnnularRows.initial_numerator]
  simp only [map_mul, map_pow, ← annularT_polynomial, ← annularP_polynomial,
    ← annularN_polynomial, pnDenominator]
  calc
    _ = annularT * annularP ^ 4 * annularN ^ 8 * (annularN * nInverse) ^ 2 := by
      rw [annularN_mul_inverse hr hR hrR]; simp
    _ = _ := by ring

theorem actualAnnularRow_initial_succ (i : Fin 3) :
    actualAnnularRow (r := r) (R := R) 0 i.succ = 0 := by
  simp only [actualAnnularRow, Zeta7AnnularRows.initial_numerator_succ, pnFraction,
    map_zero, zero_mul]

theorem fourComponentValue_initial (hr : 1 < r) (hR : R < 49) (hrR : r ≤ R) :
    fourComponentValue (actualAnnularRow (r := r) (R := R) 0) = candidateB := by
  have h1 : actualAnnularRow (r := r) (R := R) 0 1 = 0 := actualAnnularRow_initial_succ 0
  have h2 : actualAnnularRow (r := r) (R := R) 0 2 = 0 := actualAnnularRow_initial_succ 1
  have h3 : actualAnnularRow (r := r) (R := R) 0 3 = 0 := actualAnnularRow_initial_succ 2
  simp only [fourComponentValue, actualAnnularRow_initial hr hR hrR, h1, h2, h3,
    zero_mul, add_zero, actualHypergeometricJet_zero, candidateB]
  ring

theorem candidateB_homogeneous (hr : 1 < r) (hR : R < 49) (hrR : r ≤ R) :
    euler (euler (euler (candidateB (r := r) (R := R)))) -
      annularPotential * euler candidateB -
      constant (1 / 2 : ℚ_[7]) * euler annularPotential * candidateB = 0 := by
  have h0 : euler (fourComponentValue (actualAnnularRow (r := r) (R := R) 0)) =
      fourComponentValue (actualAnnularRow 1) := actualAnnularRow_value_derivative hr hR hrR 0
  have h1 : euler (fourComponentValue (actualAnnularRow (r := r) (R := R) 1)) =
      fourComponentValue (actualAnnularRow 2) := actualAnnularRow_value_derivative hr hR hrR 1
  have h2 : euler (fourComponentValue (actualAnnularRow (r := r) (R := R) 2)) =
      fourComponentValue (actualAnnularRow 3) := actualAnnularRow_value_derivative hr hR hrR 2
  rw [fourComponentValue_initial hr hR hrR] at h0
  rw [h0, h1, h2, ← fourComponentValue_initial hr hR hrR]
  simp only [fourComponentValue]
  linear_combination
    (actualHypergeometricJet 0 0 * actualHypergeometricJet 1 0) * actualAnnularRow_residual hr hR hrR 0 +
    (actualHypergeometricJet 0 1 * actualHypergeometricJet 1 0) * actualAnnularRow_residual hr hR hrR 1 +
    (actualHypergeometricJet 0 0 * actualHypergeometricJet 1 1) * actualAnnularRow_residual hr hR hrR 2 +
    (actualHypergeometricJet 0 1 * actualHypergeometricJet 1 1) * actualAnnularRow_residual hr hR hrR 3

end Zeta7Annulus.ClosedAnnulus

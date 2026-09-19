import Zeta7Proof.AnnularPNFractions
import Zeta7Proof.AnnularFourComponent
import Zeta7Proof.AnnularRowBaseIdentities

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
namespace Zeta7Annulus.ClosedAnnulus
local instance AnnularClearedSubstitution_local1 : Fact (Nat.Prime 7) := ⟨by decide⟩
variable {r R : ℝ} [Fact (0 < r)] [Fact (0 < R)]

theorem annularSubstitution_fraction : annularSubstitution (r := r) (R := R) =
    pnFraction Zeta7AnnularRows.raw_s 1 3 := by
  rw [Zeta7AnnularRows.s_numerator]
  simp only [pnFraction, map_pow, ← annularT_polynomial, pow_one, annularSubstitution]

theorem annularSubstitution_clear (hr : 1 < r) (hR : R < 49) (hrR : r ≤ R) :
    annularP * annularN ^ 3 * annularSubstitution (r := r) (R := R) =
      rationalPolynomialMap Zeta7AnnularRows.raw_s := by
  rw [annularSubstitution_fraction]
  simpa only [pnDenominator, pow_one] using pnFraction_clear hr hR hrR Zeta7AnnularRows.raw_s 1 3

theorem annularSubstitution_euler_clear (hr : 1 < r) (hR : R < 49) (hrR : r ≤ R) :
    annularP ^ 2 * annularN ^ 4 * euler (annularSubstitution (r := r) (R := R)) =
      rationalPolynomialMap Zeta7AnnularRows.raw_ds := by
  have h := pnFraction_euler_clear hr hR hrR Zeta7AnnularRows.raw_s 1 3
  rw [← annularSubstitution_fraction] at h
  simp only [Nat.cast_one, Nat.cast_ofNat, one_mul, pnDenominator, pow_one] at h
  rw [Zeta7AnnularRows.ds_numerator]
  convert h using 1 <;> ring

theorem hypergeometricDiscriminant_clear (hr : 1 < r) (hR : R < 49) (hrR : r ≤ R) :
    annularP ^ 2 * annularN ^ 6 * hypergeometricDiscriminant (r := r) (R := R) =
      rationalPolynomialMap Zeta7AnnularRows.raw_q := by
  have h := annularSubstitution_clear hr hR hrR
  rw [Zeta7AnnularRows.q_numerator]
  simp only [map_mul, map_sub, map_pow, ← annularT_polynomial,
    ← annularP_polynomial, ← annularN_polynomial]
  have hs : rationalPolynomialMap (r := r) (R := R) Zeta7AnnularRows.raw_s = annularT ^ 2 := by
    rw [Zeta7AnnularRows.s_numerator, map_pow, ← annularT_polynomial]
  rw [hs] at h
  unfold hypergeometricDiscriminant
  linear_combination
    (annularP * annularN ^ 3 - annularP * annularN ^ 3 * annularSubstitution - annularT ^ 2) * h

def annularPotential : ClosedAnnulus r R := pnFraction Zeta7AnnularRows.raw_V 2 0

theorem annularPotential_formula : annularPotential (r := r) (R := R) =
    8 * monomial 1 1 * (1 + 16 * monomial 1 1 + 49 * (monomial 1 1) ^ 2) * pInverse ^ 2 := by
  simp only [annularPotential, pnFraction, Zeta7AnnularRows.V_numerator, map_mul,
    map_add, map_pow, map_one, map_ofNat, rationalPolynomialMap_X, pow_zero, mul_one]

theorem annularPotential_clear (hr : 1 < r) (hR : R < 49) (hrR : r ≤ R) :
    annularP ^ 2 * annularPotential (r := r) (R := R) =
      rationalPolynomialMap Zeta7AnnularRows.raw_V := by
  simpa only [annularPotential, pnDenominator, pow_zero, mul_one] using
    pnFraction_clear hr hR hrR Zeta7AnnularRows.raw_V 2 0

theorem annularPotential_euler_clear (hr : 1 < r) (hR : R < 49) (hrR : r ≤ R) :
    annularP ^ 3 * euler (annularPotential (r := r) (R := R)) =
      rationalPolynomialMap Zeta7AnnularRows.raw_dV := by
  have h := pnFraction_euler_clear hr hR hrR Zeta7AnnularRows.raw_V 2 0
  simp only [pnDenominator, pow_zero, mul_one, Nat.cast_zero, Nat.cast_ofNat,
    zero_mul, add_zero] at h
  apply (annularN_isUnit hr hR hrR).mul_left_cancel
  rw [Zeta7AnnularRows.dV_numerator]
  simp only [map_mul, map_sub, map_ofNat, ← annularP_polynomial,
    ← annularN_polynomial] at h ⊢
  change annularN * (annularP ^ 3 * euler (pnFraction Zeta7AnnularRows.raw_V 2 0)) = _
  linear_combination h

end Zeta7Annulus.ClosedAnnulus

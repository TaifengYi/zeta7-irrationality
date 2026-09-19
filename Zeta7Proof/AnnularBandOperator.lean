import Zeta7Proof.AnnularGlobalHomogeneous
import Zeta7Proof.AnnularBandPolynomials

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
namespace Zeta7Annulus.ClosedAnnulus
local instance AnnularBandOperator_local1 : Fact (Nat.Prime 7) := ⟨by decide⟩
variable {r R : ℝ} [Fact (0 < r)] [Fact (0 < R)]

def annularL (f : ClosedAnnulus r R) : ClosedAnnulus r R :=
  euler (euler (euler f)) - annularPotential * euler f -
    constant (1 / 2 : ℚ_[7]) * euler annularPotential * f

def annularS (f : ClosedAnnulus r R) : ClosedAnnulus r R :=
  annularP * annularL (annularP * f)

def annularBand (f : ClosedAnnulus r R) : ClosedAnnulus r R :=
  rationalPolynomialMap Zeta7AnnularBand.b₃ * euler (euler (euler f)) +
  rationalPolynomialMap Zeta7AnnularBand.b₂ * euler (euler f) +
  rationalPolynomialMap Zeta7AnnularBand.b₁ * euler f +
  rationalPolynomialMap Zeta7AnnularBand.b₀ * f

theorem annularS_eq_band (hr : 1 < r) (hR : R < 49) (hrR : r ≤ R) (f : ClosedAnnulus r R) :
    annularS f = annularBand f := by
  have h0 := congrArg (rationalPolynomialMap (r := r) (R := R)) Zeta7AnnularBand.band_polynomial_0
  have h1 := congrArg (rationalPolynomialMap (r := r) (R := R)) Zeta7AnnularBand.band_polynomial_1
  have h2 := congrArg (rationalPolynomialMap (r := r) (R := R)) Zeta7AnnularBand.band_polynomial_2
  have h3 := congrArg (rationalPolynomialMap (r := r) (R := R)) Zeta7AnnularBand.band_polynomial_3
  simp only [map_mul, map_sub, map_pow, map_ofNat, rationalPolynomialMap_C,
    Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, ← euler_polynomial, ← annularP_polynomial] at h0 h1 h2 h3
  have hV := annularPotential_clear hr hR hrR
  have hDV := annularPotential_euler_clear hr hR hrR
  apply (annularP_isUnit hr hR hrR).mul_left_cancel
  simp only [annularS, annularL, annularBand, euler_mul, euler_add]
  linear_combination f * h0 + (annularP * euler f) * h1 +
    (annularP * euler (euler f)) * h2 + (annularP * euler (euler (euler f))) * h3 -
    (euler annularP * f + annularP * euler f) * hV - (constant (1 / 2 : ℚ_[7]) * f) * hDV

theorem candidateA_band_zero (hr : 1 < r) (hR : R < 49) (hrR : r ≤ R) :
    annularBand (candidateA (r := r) (R := R)) = 0 := by
  rw [← annularS_eq_band hr hR hrR]
  have he : annularP * candidateA (r := r) (R := R) = candidateB := by
    unfold candidateA
    calc
      _ = (annularP * pInverse) * candidateB := by ring
      _ = _ := by rw [annularP_mul_inverse hr hR hrR, one_mul]
  rw [annularS, he]
  have h : annularL (candidateB (r := r) (R := R)) = 0 := candidateB_homogeneous hr hR hrR
  rw [h, mul_zero]

end Zeta7Annulus.ClosedAnnulus

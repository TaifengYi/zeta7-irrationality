import Zeta7Proof.AnnularBandOperator

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
namespace Zeta7Annulus
local instance AnnularBilateralBand_local1 : Fact (Nat.Prime 7) := ⟨by decide⟩

def bandWeight₀ (n : ℤ) : ℚ_[7] := (n : ℚ_[7]) ^ 3
def bandWeight₁ (n : ℤ) : ℚ_[7] := (2 * n + 1) * (13 * (n : ℚ_[7]) ^ 2 + 13 * n + 9)
def bandWeight₂ (n : ℤ) : ℚ_[7] := (n + 1) * (267 * (n : ℚ_[7]) ^ 2 + 534 * n + 433)
def bandWeight₃ (n : ℤ) : ℚ_[7] := 49 * (2 * n + 3) * (13 * (n : ℚ_[7]) ^ 2 + 39 * n + 35)
def bandWeight₄ (n : ℤ) : ℚ_[7] := 2401 * ((n : ℚ_[7]) + 2) ^ 3

def bilateralBand (a : LaurentCoefficients) (k : ℤ) : ℚ_[7] :=
  bandWeight₀ k * a k + bandWeight₁ (k - 1) * a (k - 1) +
  bandWeight₂ (k - 2) * a (k - 2) + bandWeight₃ (k - 3) * a (k - 3) +
  bandWeight₄ (k - 4) * a (k - 4)

namespace ClosedAnnulus
variable {r R : ℝ} [Fact (0 < r)] [Fact (0 < R)]

set_option maxHeartbeats 800000 in
-- Expands the five finite bands, including all negative integer exponents.
theorem coeff_annularBand (a : ClosedAnnulus r R) (k : ℤ) :
    (annularBand a).coeffs k = bilateralBand a.coeffs k := by
  simp only [annularBand, Zeta7AnnularBand.b₃, Zeta7AnnularBand.b₂,
    Zeta7AnnularBand.b₁, Zeta7AnnularBand.b₀, map_add, map_one,
    ← Nat.cast_ofNat (R := Polynomial ℚ), rationalPolynomialMap_nat_mul_X,
    rationalPolynomialMap_nat_mul_X_pow, add_mul, one_mul, coeffs_add, Pi.add_apply,
    coeffs_mul, monomial_coeffs, bilateralMonomial_convolution, coeffs_euler,
    bilateralEuler, bilateralBand, bandWeight₀, bandWeight₁, bandWeight₂, bandWeight₃, bandWeight₄]
  push_cast
  ring

theorem coeff_annularS (hr : 1 < r) (hR : R < 49) (hrR : r ≤ R)
    (a : ClosedAnnulus r R) (k : ℤ) : (annularS a).coeffs k = bilateralBand a.coeffs k := by
  rw [annularS_eq_band hr hR hrR, coeff_annularBand]

end ClosedAnnulus

theorem bilateralBand_sub (a b : LaurentCoefficients) : bilateralBand (a - b) = bilateralBand a - bilateralBand b := by
  funext k
  simp only [bilateralBand, Pi.sub_apply]
  ring

theorem annularCandidateA_band_zero : bilateralBand annularCandidateA = 0 := by
  letI : Fact (0 < (2 : ℝ)) := ⟨by norm_num⟩
  letI : Fact (0 < (3 : ℝ)) := ⟨by norm_num⟩
  funext k
  have h := congrArg (fun f : ClosedAnnulus 2 3 => f.coeffs k)
    (ClosedAnnulus.candidateA_band_zero (r := 2) (R := 3) (by norm_num) (by norm_num) (by norm_num))
  rw [ClosedAnnulus.coeff_annularBand] at h
  exact h

end Zeta7Annulus

import Zeta7Proof.AnnularClearedSubstitution
import Zeta7Proof.AnnularIndexedRows

/-! The certified P/N rows evaluated in the actual annular algebra. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
namespace Zeta7Annulus.ClosedAnnulus
local instance AnnularActualRows_local1 : Fact (Nat.Prime 7) := ⟨by decide⟩
variable {r R : ℝ} [Fact (0 < r)] [Fact (0 < R)]

def actualAnnularRow (k : Fin 4) (i : Fin 4) : ClosedAnnulus r R :=
  pnFraction (Zeta7AnnularRows.rowNumerator k i) 4 10

def actualAnnularMultiplier (k i : Fin 3) : ClosedAnnulus r R :=
  pnFraction (Zeta7AnnularRows.multiplierNumerator k i) 4 10

theorem actualAnnularRow_clear (hr : 1 < r) (hR : R < 49) (hrR : r ≤ R) (k i : Fin 4) :
    pnDenominator 4 10 * actualAnnularRow (r := r) (R := R) k i =
      rationalPolynomialMap (Zeta7AnnularRows.rowNumerator k i) :=
  pnFraction_clear hr hR hrR _ 4 10

theorem actualAnnularMultiplier_clear (hr : 1 < r) (hR : R < 49) (hrR : r ≤ R) (k i : Fin 3) :
    pnDenominator 4 10 * actualAnnularMultiplier (r := r) (R := R) k i =
      rationalPolynomialMap (Zeta7AnnularRows.multiplierNumerator k i) :=
  pnFraction_clear hr hR hrR _ 4 10

theorem actualAnnularRow_euler_clear (hr : 1 < r) (hR : R < 49) (hrR : r ≤ R) (k i : Fin 4) :
    pnDenominator 4 10 * annularP * annularN * euler (actualAnnularRow (r := r) (R := R) k i) =
      rationalPolynomialMap (Zeta7AnnularRows.derivativeNumerator (Zeta7AnnularRows.rowNumerator k i)) := by
  exact pnFraction_euler_clear hr hR hrR _ 4 10

theorem actualAnnularRow_reduction (hr : 1 < r) (hR : R < 49) (hrR : r ≤ R) (k i : Fin 3) :
    actualAnnularRow (r := r) (R := R) k.castSucc i.succ * euler annularSubstitution =
      hypergeometricDiscriminant * actualAnnularMultiplier k i := by
  have h := congrArg (rationalPolynomialMap (r := r) (R := R))
    (Zeta7AnnularRows.indexed_reduction k i)
  simp only [map_mul, map_pow, ← annularN_polynomial] at h
  rw [← actualAnnularRow_clear hr hR hrR, ← actualAnnularMultiplier_clear hr hR hrR,
    ← hypergeometricDiscriminant_clear hr hR hrR, ← annularSubstitution_euler_clear hr hR hrR] at h
  apply ((pnDenominator_isUnit hr hR hrR 4 10).mul (pnDenominator_isUnit hr hR hrR 2 6)).mul_left_cancel
  unfold pnDenominator at h ⊢
  linear_combination -h

theorem hypergeometricAlpha_factored : hypergeometricAlpha (r := r) (R := R) =
    constant (1 / 2 : ℚ_[7]) * (3 * annularSubstitution - 1) := by
  have h : constant (r := r) (R := R) (3 / 2 : ℚ_[7]) = 3 * constant (1 / 2 : ℚ_[7]) := by
    calc
      _ = constant (3 : ℚ_[7]) * constant (1 / 2 : ℚ_[7]) := by rw [← map_mul]; congr 1; ring
      _ = _ := by rw [map_ofNat]
  rw [hypergeometricAlpha, h]
  ring

theorem hypergeometricGamma_factored : hypergeometricGamma (r := r) (R := R) =
    constant (1 / 2 : ℚ_[7]) * (5 * annularSubstitution - 3) := by
  have h3 : constant (r := r) (R := R) (3 / 2 : ℚ_[7]) = 3 * constant (1 / 2 : ℚ_[7]) := by
    calc
      _ = constant (3 : ℚ_[7]) * constant (1 / 2 : ℚ_[7]) := by rw [← map_mul]; congr 1; ring
      _ = _ := by rw [map_ofNat]
  have h5 : constant (r := r) (R := R) (5 / 2 : ℚ_[7]) = 5 * constant (1 / 2 : ℚ_[7]) := by
    calc
      _ = constant (5 : ℚ_[7]) * constant (1 / 2 : ℚ_[7]) := by rw [← map_mul]; congr 1; ring
      _ = _ := by rw [map_ofNat]
  rw [hypergeometricGamma, h3, h5]
  ring

theorem hypergeometricAlpha_add_Gamma :
    hypergeometricAlpha (r := r) (R := R) + hypergeometricGamma = 4 * annularSubstitution - 2 := by
  unfold hypergeometricAlpha hypergeometricGamma
  calc
    _ = (constant (3 / 2 : ℚ_[7]) + constant (5 / 2 : ℚ_[7])) * annularSubstitution -
      (constant (1 / 2 : ℚ_[7]) + constant (3 / 2 : ℚ_[7])) := by ring
    _ = _ := by rw [← map_add, ← map_add]; norm_num [map_ofNat]

end Zeta7Annulus.ClosedAnnulus

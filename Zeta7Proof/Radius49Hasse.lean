import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.Tactic

/-! The characteristic-seven calculation in paper Section 5.1.
The coefficient is identified with the actual Weierstrass j invariant.
No equivalence with geometric supersingularity is assumed. -/

set_option autoImplicit false
namespace Zeta7Radius49
open Polynomial

def shortCurve {K : Type*} (a b : K) [Zero K] : WeierstrassCurve K := ⟨0, 0, 0, a, b⟩

theorem cubic_cube_coeff_six {K : Type*} [CommRing K] (a b : K) :
    ((X ^ 3 + C a * X + C b : K[X]) ^ 3).coeff 6 = 3 * b := by
  have h : (X ^ 3 + C a * X + C b : K[X]) ^ 3 =
      X^9 + C (3*a)*X^7 + C (3*b)*X^6 + C (3*a^2)*X^5 +
      C (6*a*b)*X^4 + C (a^3+3*b^2)*X^3 + C (3*a^2*b)*X^2 +
      C (3*a*b^2)*X + C (b^3) := by
    simp only [map_mul, map_add, map_pow, map_ofNat]
    ring
  rw [h]
  simp only [coeff_add, coeff_X_pow, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C]
  norm_num

theorem cubic_cube_coeff_six_eq_zero {K : Type*} [Field K] [CharP K 7] (a b : K) :
    ((X ^ 3 + C a * X + C b : K[X]) ^ 3).coeff 6 = 0 ↔ b = 0 := by
  rw [cubic_cube_coeff_six, mul_eq_zero]
  have h3 : (3 : K) ≠ 0 := (CharP.cast_eq_zero_iff K 7 3).not.mpr (by decide)
  simp only [h3, false_or]

theorem shortCurve_discriminant {K : Type*} [CommRing K] (a b : K) :
    (shortCurve a b).Δ = -16 * (4*a^3 + 27*b^2) := by
  simp only [shortCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

theorem shortCurve_c_four {K : Type*} [CommRing K] (a b : K) :
    (shortCurve a b).c₄ = -48*a := by
  simp only [shortCurve, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
  ring

theorem shortCurve_j_eq_1728_iff {K : Type*} [Field K] [CharP K 7]
    (a b : K) [(shortCurve a b).IsElliptic] :
    (shortCurve a b).j = 1728 ↔ b = 0 := by
  have hd : (shortCurve a b).Δ ≠ 0 := (shortCurve a b).isUnit_Δ.ne_zero
  rw [WeierstrassCurve.j_eq, ← div_eq_inv_mul, div_eq_iff hd,
    shortCurve_discriminant, shortCurve_c_four]
  have hnum : (-48*a)^3 - 1728 * (-16*(4*a^3+27*b^2)) = 746496*b^2 := by ring
  rw [← sub_eq_zero, hnum, mul_eq_zero]
  have hc : (746496 : K) ≠ 0 := (CharP.cast_eq_zero_iff K 7 746496).not.mpr (by decide)
  simp only [hc, false_or, pow_eq_zero_iff (by decide : 2 ≠ 0)]

theorem cubic_cube_coeff_zero_iff_j {K : Type*} [Field K] [CharP K 7]
    (a b : K) [(shortCurve a b).IsElliptic] :
    ((X ^ 3 + C a * X + C b : K[X]) ^ 3).coeff 6 = 0 ↔
      (shortCurve a b).j = 1728 := by
  rw [cubic_cube_coeff_six_eq_zero, shortCurve_j_eq_1728_iff]

end Zeta7Radius49

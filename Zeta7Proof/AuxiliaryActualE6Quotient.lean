import Zeta7Proof.ActualRiccati
import Zeta7Proof.RamanujanFour
import Zeta7Proof.AuxiliaryQuotientPolynomials

/-! The actual E6 quotient, derived from the established E4 quotient and Ramanujan equation. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
namespace Zeta7Common
open PowerSeries Zeta7Main

def pulledE6 : PowerSeries ℚ := qTransport eisensteinSixQ
def shortT : PowerSeries ℚ := (Zeta7Riccati.T : Polynomial ℚ)

theorem E4_ramanujan_transported :
    3 * BSeries * euler pulledE4 = pulledE2 * pulledE4 - pulledE6 := by
  have h := Zeta7Classical.eisensteinFourQ_ramanujan
  simp only [map_ofNat] at h
  have ht := congrArg qTransport h
  simpa only [map_mul, map_sub, map_ofNat, qTransport_euler,
    pulledE2, pulledE4, pulledE6, mul_assoc] using ht

theorem pulledE6_eq_short :
    pulledE6 = BSeries ^ 3 * (shortS * shortA - 3 * euler shortA) := by
  have hd : euler pulledE4 = BSeries ^ 2 *
      (2 * logarithmicB * shortA + euler shortA) := by
    rw [pulledE4_eq, pow_two, euler_mul, euler_mul, euler_B]
    ring
  have h := E4_ramanujan_transported
  rw [hd, pulledE4_eq, ← B_mul_actualW, actualW_eq] at h
  linear_combination h

theorem shortP_sq_euler_shortA :
    shortP ^ 2 * euler shortA = euler shortN * shortP - shortN * euler shortP := by
  have h := congrArg euler shortP_mul_shortA
  rw [euler_mul] at h
  linear_combination shortP * h - euler shortP * shortP_mul_shortA

theorem shortT_identity :
    shortQ * shortN - 3 * (euler shortN * shortP - shortN * euler shortP) = shortT := by
  have h := congrArg Polynomial.coeToPowerSeries.ringHom Zeta7Riccati.sNumerator_eq_NQ
  simp only [Zeta7Riccati.sNumerator, map_add, map_sub, map_mul, map_ofNat,
    Polynomial.coeToPowerSeries.ringHom_apply] at h
  simp only [shortQ, shortN, shortP, shortT, polynomial_euler]
  linear_combination -h

/-- Complete denominator-cleared E6 identity for the original inverse coordinate. -/
theorem pulledE6_cleared : shortP ^ 2 * pulledE6 = BSeries ^ 3 * shortT := by
  have hsa : shortP ^ 2 * (shortS * shortA) = shortQ * shortN := by
    calc
      _ = (shortP * shortS) * (shortP * shortA) := by ring
      _ = _ := by rw [shortP_mul_shortS, shortP_mul_shortA]
  rw [pulledE6_eq_short]
  linear_combination BSeries ^ 3 * hsa - 3 * BSeries ^ 3 * shortP_sq_euler_shortA +
    BSeries ^ 3 * shortT_identity

theorem pulled_monomial_cleared (s a b : ℕ) (h : a + 2*b ≤ s) :
    shortP ^ s * (pulledE4 ^ a * pulledE6 ^ b) =
      BSeries ^ (2*a+3*b) * (Zeta7Auxiliary.quotientMonomial s a b : Polynomial ℚ) := by
  have hs : s = (s-a-2*b) + a + 2*b := by omega
  calc
    _ = shortP^(s-a-2*b) * (shortP*pulledE4)^a * (shortP^2*pulledE6)^b := by
      conv_lhs => rw [hs]
      simp only [pow_add, mul_pow, pow_mul]
      ring
    _ = _ := by
      rw [pulledE4_cleared, pulledE6_cleared]
      simp only [Zeta7Auxiliary.quotientMonomial, map_mul, map_pow,
        Polynomial.coe_mul, Polynomial.coe_pow, shortP, shortN, shortT,
        mul_pow, pow_add, pow_mul]
      ring

end Zeta7Common

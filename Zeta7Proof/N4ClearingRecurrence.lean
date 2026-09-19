import Zeta7Proof.N4CyclicSpan
import Zeta7Proof.N4ClearedCoefficients

/-! Exact clearing recurrence for the original seven-coordinate connection,
including the derivative of the clearing factor. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
open scoped RatFunc
namespace Zeta7Germ

theorem rationalD_pow_cleared (f : RatFunc ℂ) (n : ℕ) :
    f * rationalD (f ^ n) = (n : RatFunc ℂ) * f ^ n * rationalD f := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, Derivation.leibniz]
      simp only [smul_eq_mul, Nat.cast_add, Nat.cast_one]
      linear_combination f * ih

theorem clearingCorrection_cast (k : ℕ) :
    (clearingCorrection k : RatFunc ℂ) = (3 * (k : RatFunc ℂ)) * P ^ 2 * rationalD P := by
  have hd : (polynomialD polynomialP : RatFunc ℂ) = rationalD P := by
    rw [← polynomialP_cast, rationalD_polynomial]
    rfl
  simp only [clearingCorrection, RatFunc.coePolynomial_eq_algebraMap, map_mul,
    map_pow, RatFunc.algebraMap_C, map_ofNat, map_natCast]
  simp only [← RatFunc.coePolynomial_eq_algebraMap, polynomialP_cast, hd]

theorem clearingFactor_derivative (k : ℕ) :
    P ^ 3 * rationalD (P ^ (3 * k)) = (clearingCorrection k : RatFunc ℂ) * P ^ (3 * k) := by
  have h := rationalD_pow_cleared P (3 * k)
  simp only [Nat.cast_mul, Nat.cast_ofNat] at h
  rw [clearingCorrection_cast]
  linear_combination P ^ 2 * h

def clearedIterate (z : SevenCoordinates) (k : ℕ) : SevenCoordinates :=
  P ^ (3 * k) • connection7^[k] z

theorem clearedIterate_zero (z : SevenCoordinates) : clearedIterate z 0 = z := by
  simp [clearedIterate]

theorem clearedIterate_recurrence (z : SevenCoordinates) (k : ℕ) :
    clearedIterate z (k + 1) = P ^ 3 • connection7 (clearedIterate z k) -
      (clearingCorrection k : RatFunc ℂ) • clearedIterate z k := by
  simp only [clearedIterate, connection7_leibniz, smul_add, smul_smul]
  rw [clearingFactor_derivative]
  simp only [add_sub_cancel_left]
  rw [Function.iterate_succ_apply']
  congr 1
  rw [Nat.mul_add, Nat.mul_one, pow_add]
  ring

theorem clearedIterates_independent (z : SevenCoordinates) (n : ℕ)
    (hn : n ≤ Module.finrank (RatFunc ℂ) (cyclicSpan z)) :
    LinearIndependent (RatFunc ℂ) (fun i : Fin n => clearedIterate z i.val) := by
  exact (cyclic_derivatives_independent z n hn).units_smul
    (fun i => Units.mk0 (P ^ (3 * i.val)) (pow_ne_zero _ P_ne_zero))

end Zeta7Germ

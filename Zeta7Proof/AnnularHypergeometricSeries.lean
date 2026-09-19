import Zeta7Proof.ActualTargetDifferential
import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric

/-! The two specified hypergeometric Taylor series in A1, using Mathlib's
Pochhammer coefficients. These identities concern complete series. Their
seven-adic convergence after annular substitution is a separate obligation. -/
noncomputable section
set_option autoImplicit false
open PowerSeries
namespace Zeta7Annulus

theorem pochhammer_eval_pos (c : ℚ) (hc : 0 < c) (n : ℕ) :
    0 < (ascPochhammer ℚ n).eval c := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [ascPochhammer_succ_eval]
      positivity

def hypergeometricTaylor (a b c : ℚ) : ℚ⟦X⟧ :=
  mk (ordinaryHypergeometricCoefficient a b c)

theorem hypergeometric_coefficient_recurrence (a b c : ℚ) (hc : 0 < c) (n : ℕ) :
    ((n : ℚ) + 1) * ((n : ℚ) + c) *
        ordinaryHypergeometricCoefficient a b c (n + 1) =
      ((n : ℚ) + a) * ((n : ℚ) + b) * ordinaryHypergeometricCoefficient a b c n := by
  have hpc := ne_of_gt (pochhammer_eval_pos c hc n)
  have hnc : c + (n : ℚ) ≠ 0 := ne_of_gt (by positivity)
  have hn : (n : ℚ) + 1 ≠ 0 := ne_of_gt (by positivity)
  have hfac : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  simp only [ordinaryHypergeometricCoefficient, Nat.factorial_succ,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one, ascPochhammer_succ_eval]
  field_simp
  <;> ring

theorem hypergeometricTaylor_constant (a b c : ℚ) :
    constantCoeff (hypergeometricTaylor a b c) = 1 := by
  simp [hypergeometricTaylor, ordinaryHypergeometricCoefficient]

theorem hypergeometricTaylor_equation (a b c : ℚ) (hc : 0 < c) :
    Zeta7Common.euler (Zeta7Common.euler (hypergeometricTaylor a b c)) +
        C (c - 1) * Zeta7Common.euler (hypergeometricTaylor a b c) =
      X * (Zeta7Common.euler (Zeta7Common.euler (hypergeometricTaylor a b c)) +
        C (a + b) * Zeta7Common.euler (hypergeometricTaylor a b c) +
        C (a * b) * hypergeometricTaylor a b c) := by
  ext n
  cases n with
  | zero => simp [Zeta7Common.euler]
  | succ n =>
      simp only [map_add (coeff _), coeff_C_mul, coeff_succ_X_mul, Zeta7Common.euler_coeff,
        hypergeometricTaylor, coeff_mk, Nat.cast_succ]
      linear_combination hypergeometric_coefficient_recurrence a b c hc n

def annularHypergeometricA : ℚ⟦X⟧ := hypergeometricTaylor (1/12) (5/12) (1/2)
def annularHypergeometricC : ℚ⟦X⟧ := hypergeometricTaylor (7/12) (11/12) (3/2)

theorem annularHypergeometricA_constant : constantCoeff annularHypergeometricA = 1 :=
  hypergeometricTaylor_constant _ _ _

theorem annularHypergeometricC_constant : constantCoeff annularHypergeometricC = 1 :=
  hypergeometricTaylor_constant _ _ _

theorem annularHypergeometricA_equation :
    Zeta7Common.euler (Zeta7Common.euler annularHypergeometricA) -
        C (1/2 : ℚ) * Zeta7Common.euler annularHypergeometricA =
      X * (Zeta7Common.euler (Zeta7Common.euler annularHypergeometricA) +
        C (1/2 : ℚ) * Zeta7Common.euler annularHypergeometricA +
        C (5/144 : ℚ) * annularHypergeometricA) := by
  have h := hypergeometricTaylor_equation (1/12) (5/12) (1/2) (by norm_num)
  norm_num at h
  simpa only [annularHypergeometricA, map_neg, neg_mul, sub_eq_add_neg] using h

theorem annularHypergeometricC_equation :
    Zeta7Common.euler (Zeta7Common.euler annularHypergeometricC) +
        C (1/2 : ℚ) * Zeta7Common.euler annularHypergeometricC =
      X * (Zeta7Common.euler (Zeta7Common.euler annularHypergeometricC) +
        C (3/2 : ℚ) * Zeta7Common.euler annularHypergeometricC +
        C (77/144 : ℚ) * annularHypergeometricC) := by
  have h := hypergeometricTaylor_equation (7/12) (11/12) (3/2) (by norm_num)
  norm_num at h
  exact h

end Zeta7Annulus

import Zeta7Proof.AnnularHypergeometricSeries
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-! Integer product formulas for the two actual A1 hypergeometric families. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
open PowerSeries
namespace Zeta7Annulus
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

def hypergeometricNumerator (i : Fin 2) (n : ℕ) : ℕ :=
  ∏ k ∈ Finset.range n, (12 * k + 1 + 6 * i.val) * (12 * k + 5 + 6 * i.val)

def annularHypergeometricCoefficient (i : Fin 2) (n : ℕ) : ℚ :=
  ordinaryHypergeometricCoefficient ((1 + 6 * i.val) / 12 : ℚ)
    ((5 + 6 * i.val) / 12) ((1 + 2 * i.val) / 2) n

theorem hypergeometricNumerator_pos (i : Fin 2) (n : ℕ) :
    0 < hypergeometricNumerator i n := by
  apply Finset.prod_pos
  intro k hk
  positivity

theorem annularHypergeometricCoefficient_factorial (i : Fin 2) (n : ℕ) :
    annularHypergeometricCoefficient i n =
      (hypergeometricNumerator i n : ℚ) / (36 ^ n * ((2 * n + i.val).factorial : ℚ)) := by
  induction n with
  | zero => fin_cases i <;> norm_num [annularHypergeometricCoefficient,
      ordinaryHypergeometricCoefficient, hypergeometricNumerator]
  | succ n ih =>
      have hc : (0 : ℚ) < (1 + 2 * i.val) / 2 := by positivity
      have hrec := hypergeometric_coefficient_recurrence
        ((1 + 6 * i.val) / 12 : ℚ) ((5 + 6 * i.val) / 12) ((1 + 2 * i.val) / 2) hc n
      change ((n : ℚ) + 1) * ((n : ℚ) + (1 + 2 * i.val) / 2) *
        annularHypergeometricCoefficient i (n + 1) = _ at hrec
      have hm : ((n : ℚ) + 1) * ((n : ℚ) + (1 + 2 * i.val) / 2) ≠ 0 := by positivity
      apply mul_left_cancel₀ hm
      rw [hrec, ← annularHypergeometricCoefficient, ih]
      have hnum : hypergeometricNumerator i (n + 1) = hypergeometricNumerator i n *
          ((12 * n + 1 + 6 * i.val) * (12 * n + 5 + 6 * i.val)) := by
        exact Finset.prod_range_succ _ n
      rw [hnum]
      have he : 2 * (n + 1) + i.val = (2 * n + i.val + 1) + 1 := by omega
      rw [he, Nat.factorial_succ, Nat.factorial_succ, pow_succ]
      push_cast
      fin_cases i <;> norm_num only [Fin.val_zero, Fin.val_one] at *
      all_goals field_simp <;> ring

theorem annularHypergeometricA_coeff_factorial (n : ℕ) :
    coeff n annularHypergeometricA =
      (hypergeometricNumerator 0 n : ℚ) / (36 ^ n * ((2 * n).factorial : ℚ)) := by
  simpa [annularHypergeometricA, hypergeometricTaylor, annularHypergeometricCoefficient]
    using annularHypergeometricCoefficient_factorial 0 n

theorem annularHypergeometricC_coeff_factorial (n : ℕ) :
    coeff n annularHypergeometricC =
      (hypergeometricNumerator 1 n : ℚ) / (36 ^ n * ((2 * n + 1).factorial : ℚ)) := by
  have h := annularHypergeometricCoefficient_factorial 1 n
  norm_num [annularHypergeometricCoefficient] at h
  simpa only [annularHypergeometricC, hypergeometricTaylor, coeff_mk] using h

theorem annularHypergeometricCoefficient_valuation (i : Fin 2) (n : ℕ) :
    -(n : ℚ) / 3 ≤ (padicValRat 7 (annularHypergeometricCoefficient i n) : ℚ) := by
  rw [annularHypergeometricCoefficient_factorial]
  have hn : (hypergeometricNumerator i n : ℚ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (hypergeometricNumerator_pos i n))
  have hf : (((2 * n + i.val).factorial : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero _
  rw [padicValRat.div hn (mul_ne_zero (pow_ne_zero _ (by norm_num)) hf),
    padicValRat.mul (pow_ne_zero _ (by norm_num)) hf, padicValRat.pow]
  have h36 : padicValRat 7 (36 : ℚ) = 0 := by
    have hh := padicValRat.of_nat (p := 7) (n := 36)
    norm_num only [Nat.cast_ofNat, padicValNat.eq_zero_of_not_dvd (by decide : ¬ 7 ∣ 36)] at hh
    exact hh
  simp only [h36, padicValRat.of_nat,
    Int.natCast_zero, mul_zero, zero_add]
  have hb : 3 * padicValNat 7 (2 * n + i.val).factorial ≤ n := by
    by_cases hz : 2 * n + i.val = 0
    · simp [hz]
    · have hh := sub_one_mul_padicValNat_factorial_lt_of_ne_zero 7 hz
      have hi := i.isLt
      omega
  have hq : (3 : ℚ) * (padicValNat 7 (2 * n + i.val).factorial : ℚ) ≤ n := by
    exact_mod_cast hb
  simp only [Int.cast_sub, Int.cast_natCast]
  have hp : (0 : ℚ) ≤ padicValNat 7 (hypergeometricNumerator i n) := by positivity
  linarith

theorem annularHypergeometricA_valuation (n : ℕ) :
    -(n : ℚ) / 3 ≤ (padicValRat 7 (coeff n annularHypergeometricA) : ℚ) := by
  simpa [annularHypergeometricA, hypergeometricTaylor, annularHypergeometricCoefficient]
    using annularHypergeometricCoefficient_valuation 0 n

theorem annularHypergeometricC_valuation (n : ℕ) :
    -(n : ℚ) / 3 ≤ (padicValRat 7 (coeff n annularHypergeometricC) : ℚ) := by
  have h := annularHypergeometricCoefficient_valuation 1 n
  norm_num [annularHypergeometricCoefficient] at h
  simpa only [annularHypergeometricC, hypergeometricTaylor, coeff_mk] using h

theorem annularHypergeometricCoefficient_nonzero (i : Fin 2) (n : ℕ) :
    annularHypergeometricCoefficient i n ≠ 0 := by
  rw [annularHypergeometricCoefficient_factorial]
  apply div_ne_zero
  · exact_mod_cast ne_of_gt (hypergeometricNumerator_pos i n)
  · exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (by exact_mod_cast Nat.factorial_ne_zero _)

theorem annularHypergeometricCoefficient_gauss_one (i : Fin 2) (n : ℕ) (hn : 0 < n) :
    0 < (padicValRat 7 (annularHypergeometricCoefficient i n) : ℚ) + n := by
  have h := annularHypergeometricCoefficient_valuation i n
  have hn' : (0 : ℚ) < n := by exact_mod_cast hn
  linarith

end Zeta7Annulus

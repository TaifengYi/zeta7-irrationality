import Zeta7Proof.GermRationalOperator
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! Exact algebra at the singular points, and the terminal N1 obstruction. -/
noncomputable section
set_option autoImplicit false
open scoped RatFunc Polynomial
namespace Zeta7Germ

def indicial (m : ℂ) : ℂ := m * (m - 1) * (m - 2) + 8 * m / 9 - 8 / 9

theorem indicial_factor (m : ℂ) :
    indicial m = (m - 1) * (m - 2 / 3) * (m - 4 / 3) := by
  dsimp [indicial]
  ring

theorem indicial_roots (m : ℂ) :
    indicial m = 0 ↔ m = 1 ∨ m = 2 / 3 ∨ m = 4 / 3 := by
  rw [indicial_factor]
  simp only [mul_eq_zero, sub_eq_zero]
  tauto

theorem indicial_negative_integer (n : ℤ) (hn : n < 0) : indicial (n : ℂ) ≠ 0 := by
  intro h
  rw [indicial_roots] at h
  rcases h with h | h | h
  · have := congrArg Complex.re h
    norm_num at this
    have hn' : (n : ℝ) < 0 := by exact_mod_cast hn
    linarith
  · have := congrArg Complex.re h
    norm_num at this
    have hn' : (n : ℝ) < 0 := by exact_mod_cast hn
    linarith
  · have := congrArg Complex.re h
    norm_num at this
    have hn' : (n : ℝ) < 0 := by exact_mod_cast hn
    linarith

theorem singular_root_algebra (a : ℂ) (ha : 1 + 13 * a + 49 * a ^ 2 = 0) :
    a ≠ 0 ∧ 1 + 16 * a + 49 * a ^ 2 = 3 * a ∧
      (13 + 98 * a) ^ 2 = -27 := by
  refine ⟨?_, ?_, ?_⟩
  · intro hz
    norm_num [hz] at ha
  · linear_combination ha
  · linear_combination 196 * ha

def obstructionPolynomial : Polynomial ℂ :=
  9 + 433 * Polynomial.X + 5145 * Polynomial.X ^ 2 + 19208 * Polynomial.X ^ 3

theorem obstructionPolynomial_eval :
    obstructionPolynomial.eval (-1 / 10) = -1029 / 500 := by
  norm_num [obstructionPolynomial]

theorem obstructionPolynomial_not_dvd :
    ¬(1 + 10 * Polynomial.X : Polynomial ℂ) ∣ obstructionPolynomial := by
  rintro ⟨p, hp⟩
  have he := congrArg (Polynomial.eval (-1 / 10)) hp
  rw [obstructionPolynomial_eval] at he
  norm_num at he

theorem obstruction_cleared_implies_zero (h : Polynomial ℂ) (a : ℂ)
    (he : (1 + 10 * Polynomial.X) * h = Polynomial.C a * obstructionPolynomial) : a = 0 := by
  have hh := congrArg (Polynomial.eval (-1 / 10)) he
  simp only [Polynomial.eval_mul, Polynomial.eval_C, obstructionPolynomial_eval] at hh
  norm_num at hh
  exact hh

/-- The no-finite-poles conclusion expressed using the actual reduced denominator. -/
theorem polynomial_of_denom_no_roots (f : RatFunc ℂ)
    (h : ∀ a : ℂ, f.denom.eval a ≠ 0) : ∃ p : Polynomial ℂ, f = p := by
  have hd : f.denom.degree = 0 := by
    by_contra hn
    obtain ⟨a, ha⟩ := IsAlgClosed.exists_root f.denom hn
    exact h a ha
  have hc : f.denom = Polynomial.C (f.denom.coeff 0) :=
    Polynomial.eq_C_of_degree_le_zero (le_of_eq hd)
  refine ⟨Polynomial.C ((f.denom.coeff 0)⁻¹) * f.num, ?_⟩
  conv_lhs => rw [← RatFunc.num_div_denom f]
  rw [hc]
  simp [RatFunc.coePolynomial_eq_algebraMap, RatFunc.algebraMap_C, mul_comm,
    div_eq_mul_inv]

end Zeta7Germ

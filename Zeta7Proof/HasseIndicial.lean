import Mathlib

/-! Polynomial indicial equations at arbitrary roots, in arbitrary characteristic. -/
noncomputable section
set_option autoImplicit false
namespace Zeta7Auxiliary
open Polynomial
variable {K : Type*} [Field K]

def centeredEuler (a : K) (f : Polynomial K) : Polynomial K := (X - C a) * f.derivative

theorem centeredEuler_mul (a : K) (f g : Polynomial K) :
    centeredEuler a (f*g) = centeredEuler a f*g + f*centeredEuler a g := by
  simp only [centeredEuler, derivative_mul]; ring

theorem centeredEuler_power (a : K) (m : ℕ) :
    centeredEuler a ((X-C a)^m) = C (m:K)*(X-C a)^m := by
  cases m with
  | zero => simp [centeredEuler]
  | succ m =>
    simp only [centeredEuler, derivative_pow, derivative_sub, derivative_X,
      derivative_C, sub_zero, mul_one, Nat.succ_sub_one]
    simp only [pow_succ]
    ring

theorem centeredEuler_factor (a : K) (m : ℕ) (g : Polynomial K) :
    centeredEuler a ((X-C a)^m*g) =
      (X-C a)^m*(C (m:K)*g + centeredEuler a g) := by
  rw [centeredEuler_mul, centeredEuler_power]; ring

theorem centeredEuler_eval (a : K) (g : Polynomial K) : (centeredEuler a g).eval a = 0 := by
  simp [centeredEuler]

/-- The exact indicial equation; the root need not lie in the base prime field. -/
theorem polynomial_indicial (a : K) (f A B C₀ : Polynomial K) (hf : f ≠ 0)
    (he : A * (centeredEuler a (centeredEuler a f) - centeredEuler a f) +
      B * centeredEuler a f + C₀ * f = 0) :
    A.eval a * ((f.rootMultiplicity a : K)^2 - (f.rootMultiplicity a : K)) +
      B.eval a * (f.rootMultiplicity a : K) + C₀.eval a = 0 := by
  obtain ⟨g,hg,hg0⟩ := f.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hf a
  have hgv : g.eval a ≠ 0 := by
    intro h; exact hg0 (dvd_iff_isRoot.mpr h)
  have ht : (X-C a)^f.rootMultiplicity a ≠ 0 :=
    pow_ne_zero _ (X_sub_C_ne_zero a)
  rw [hg, centeredEuler_factor, centeredEuler_factor] at he
  have hex : (X-C a)^f.rootMultiplicity a *
      (A*(C (f.rootMultiplicity a : K)*(C (f.rootMultiplicity a : K)*g + centeredEuler a g) +
        centeredEuler a (C (f.rootMultiplicity a : K)*g + centeredEuler a g) -
          (C (f.rootMultiplicity a : K)*g + centeredEuler a g)) +
       B*(C (f.rootMultiplicity a : K)*g + centeredEuler a g) + C₀*g) = 0 := by
    linear_combination he
  have hz := (mul_eq_zero.mp hex).resolve_left ht
  have hev := congrArg (Polynomial.eval a) hz
  simp only [eval_add, eval_sub, eval_mul, eval_C, centeredEuler_eval, add_zero,
    eval_zero] at hev
  apply (mul_eq_zero.mp (show
    (A.eval a*((f.rootMultiplicity a:K)^2-(f.rootMultiplicity a:K)) +
      B.eval a*(f.rootMultiplicity a:K)+C₀.eval a) * g.eval a = 0 by
        linear_combination hev)).resolve_right hgv

theorem centeredEuler_second (a : K) (f : Polynomial K) :
    centeredEuler a (centeredEuler a f) - centeredEuler a f =
      (X-C a)^2*f.derivative.derivative := by
  simp only [centeredEuler, derivative_mul, derivative_sub, derivative_X, derivative_C,
    sub_zero, one_mul]
  ring

theorem ordinary_indicial (a : K) (f A B C₀ : Polynomial K) (hf : f ≠ 0)
    (he : A*f.derivative.derivative+B*f.derivative+C₀*f=0) :
    A.eval a * ((f.rootMultiplicity a : K)^2-(f.rootMultiplicity a : K)) = 0 := by
  have h := polynomial_indicial a f A ((X-C a)*B) ((X-C a)^2*C₀) hf (by
    rw [centeredEuler_second]
    unfold centeredEuler
    linear_combination (X-C a)^2 * he)
  simpa using h

end Zeta7Auxiliary

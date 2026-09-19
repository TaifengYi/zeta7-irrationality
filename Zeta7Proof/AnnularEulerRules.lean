import Zeta7Proof.AnnularHypergeometricComposition
import Zeta7Proof.AnnularPolynomialIdentification

/-! Exact finite differentiation rules for the existing annulus Euler map. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
namespace Zeta7Annulus.ClosedAnnulus
local instance AnnularEulerRules_local1 : Fact (Nat.Prime 7) := ⟨by decide⟩
variable {r R : ℝ} [Fact (0 < r)] [Fact (0 < R)]

@[simp] theorem euler_zero : euler (0 : ClosedAnnulus r R) = 0 := eulerAddHom.map_zero
theorem euler_add (a b : ClosedAnnulus r R) : euler (a + b) = euler a + euler b :=
  eulerAddHom.map_add a b
theorem euler_sub (a b : ClosedAnnulus r R) : euler (a - b) = euler a - euler b :=
  eulerAddHom.map_sub a b

theorem euler_monomial (n : ℤ) (z : ℚ_[7]) :
    euler (monomial (r := r) (R := R) n z) = monomial n ((n : ℚ_[7]) * z) := by
  ext k
  change (k : ℚ_[7]) * (if k = n then z else 0) = if k = n then (n : ℚ_[7]) * z else 0
  split_ifs with h
  · subst k; rfl
  · exact mul_zero _

@[simp] theorem euler_constant (z : ℚ_[7]) : euler (constant (r := r) (R := R) z) = 0 := by
  change euler (monomial (r := r) (R := R) 0 z) = 0
  rw [euler_monomial]
  simp only [Int.cast_zero, zero_mul, monomial_zero]

@[simp] theorem euler_one : euler (1 : ClosedAnnulus r R) = 0 := by
  simpa only [map_one] using euler_constant (r := r) (R := R) 1

theorem euler_constant_mul (z : ℚ_[7]) (a : ClosedAnnulus r R) :
    euler (constant z * a) = constant z * euler a := by
  rw [euler_mul, euler_constant, zero_mul, zero_add]

theorem euler_pow_succ (a : ClosedAnnulus r R) (n : ℕ) :
    euler (a ^ (n + 1)) = (n + 1 : ClosedAnnulus r R) * a ^ n * euler a := by
  induction n with
  | zero => simp only [zero_add, pow_one, Nat.cast_zero, pow_zero, one_mul, mul_one]
  | succ n ih =>
      rw [pow_succ, euler_mul, ih]
      push_cast
      rw [pow_succ]
      ring

theorem euler_inverse (a b : ClosedAnnulus r R) (hab : a * b = 1) :
    euler b = -(b ^ 2 * euler a) := by
  have hd := congrArg euler hab
  rw [euler_mul, euler_one] at hd
  have ht := congrArg (fun z => b * z) hd
  calc
    euler b = b * (euler a * b + a * euler b) - b ^ 2 * euler a := by
      calc
        _ = (a * b) * euler b := by rw [hab, one_mul]
        _ = _ := by ring
    _ = _ := by rw [ht, mul_zero, zero_sub]

end Zeta7Annulus.ClosedAnnulus

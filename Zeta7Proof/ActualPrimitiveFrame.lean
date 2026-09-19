import Zeta7Proof.ActualLH

/-! The ordinary-primitive frame of N3, for the original modular germs. -/
noncomputable section
set_option autoImplicit false
open PowerSeries
namespace Zeta7Common

theorem derivative_primitive_actual (f : ℚ⟦X⟧) : derivative ℚ (primitive f) = f :=
  Zeta7Stage2B.derivative_primitive f

theorem euler_primitive_actual (f : ℚ⟦X⟧) : euler (primitive f) = X * f := by
  rw [euler, derivative_primitive_actual]

def primitiveFrame (c : ℚ) : Fin 3 → ℚ⟦X⟧ :=
  let K := quadratic rationalPotential (rationalH c)
  ![K, primitive K - X * K,
    primitive (primitive K) - X * primitive K + C (1 / 2 : ℚ) * X ^ 2 * K]

@[simp] theorem euler_X_actual : euler (X : ℚ⟦X⟧) = X := by simp [euler]

theorem primitiveFrame_euler_zero (c : ℚ) :
    euler (primitiveFrame c 0) = rationalForcing * rationalH c :=
  rationalH_quadratic_derivative c

theorem primitiveFrame_euler_one (c : ℚ) :
    euler (primitiveFrame c 1) = -X * rationalForcing * rationalH c := by
  change euler (primitive _ - X * _) = _
  rw [euler_sub, euler_primitive_actual, euler_mul,
    euler_X_actual, rationalH_quadratic_derivative]
  ring

theorem primitiveFrame_euler_two (c : ℚ) :
    euler (primitiveFrame c 2) =
      C (1 / 2 : ℚ) * X ^ 2 * rationalForcing * rationalH c := by
  change euler (primitive (primitive _) - X * primitive _ + C _ * X ^ 2 * _) = _
  simp only [euler_add, euler_sub, euler_primitive_actual, euler_mul, euler_C,
    pow_two, euler_X_actual, rationalH_quadratic_derivative, zero_mul, zero_add]
  have hh : (C (1 / 2 : ℚ) : ℚ⟦X⟧) * 2 = 1 := by
    have h := congrArg (C (R := ℚ)) (show (1 / 2 : ℚ) * 2 = 1 by norm_num)
    simpa only [map_mul, map_ofNat, map_one] using h
  linear_combination hh * X ^ 2 * quadratic rationalPotential (rationalH c)

theorem primitiveFrame_inverse_one (c : ℚ) :
    rationalGerms c 4 = primitiveFrame c 1 + X * primitiveFrame c 0 := by
  simp [rationalGerms, germs, primitiveFrame]

theorem primitiveFrame_inverse_two (c : ℚ) :
    rationalGerms c 5 = primitiveFrame c 2 + X * primitiveFrame c 1 +
      C (1 / 2 : ℚ) * X ^ 2 * primitiveFrame c 0 := by
  simp only [rationalGerms, germs, primitiveFrame, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons, Matrix.tail_cons]
  have hh : (C (1 / 2 : ℚ) : ℚ⟦X⟧) * 2 = 1 := by
    have h := congrArg (C (R := ℚ)) (show (1 / 2 : ℚ) * 2 = 1 by norm_num)
    simpa only [map_mul, map_ofNat, map_one] using h
  linear_combination -hh * X ^ 2 * quadratic rationalPotential (rationalH c)

end Zeta7Common

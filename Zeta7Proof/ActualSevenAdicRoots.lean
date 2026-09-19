import Zeta7Proof.ActualTargetPrimitiveBounds
import Mathlib.NumberTheory.Padics.Hensel

/-! The two actual roots of 1+13x+49x² over the seven-adic field. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
open Polynomial
namespace Zeta7Common
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

def integralPotentialDenominator : Polynomial ℤ := 1 + 13 * X + 49 * X ^ 2

theorem exists_inner_potential_root :
    ∃ a : ℚ_[7], 1 + 13 * a + 49 * a ^ 2 = 0 ∧ ‖a‖ = 1 := by
  have he : integralPotentialDenominator.aeval (1 : ℤ_[7]) = 63 := by
    norm_num [integralPotentialDenominator, map_ofNat]
  have hd : integralPotentialDenominator.derivative.aeval (1 : ℤ_[7]) = 111 := by
    norm_num [integralPotentialDenominator, Polynomial.derivative_mul, map_ofNat]
  have hd1 : ‖(111 : ℤ_[7])‖ = 1 := by
    exact PadicInt.norm_natCast_eq_one_iff.mpr (by norm_num : Nat.Coprime 7 111)
  have he1 : ‖(63 : ℤ_[7])‖ < 1 := by
    exact PadicInt.norm_natCast_lt_one_iff.mpr (by norm_num : 7 ∣ 63)
  obtain ⟨a, ha, hdist, _, _⟩ := hensels_lemma (F := integralPotentialDenominator)
    (a := (1 : ℤ_[7])) (by rw [he, hd, hd1]; simpa using he1)
  refine ⟨a, ?_, ?_⟩
  · have h : 1 + 13 * a + 49 * a ^ 2 = 0 := by
      simpa [integralPotentialDenominator, map_ofNat] using ha
    have h13 : ((13 : ℤ_[7]) : ℚ_[7]) = 13 := PadicInt.coe_natCast 13
    have h49 : ((49 : ℤ_[7]) : ℚ_[7]) = 49 := PadicInt.coe_natCast 49
    have hh := congrArg (fun z : ℤ_[7] => (z : ℚ_[7])) h
    simpa only [PadicInt.coe_add, PadicInt.coe_mul, PadicInt.coe_pow,
      PadicInt.coe_one, PadicInt.coe_zero, h13, h49] using hh
  · rw [hd, hd1] at hdist
    have h : ‖(a : ℚ_[7]) - 1‖ < 1 := by
      simpa only [PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_one] using hdist
    simpa only [norm_one] using Padic.norm_eq_of_norm_sub_lt_right
      (by simpa only [norm_one] using h : ‖(a : ℚ_[7]) - 1‖ < ‖(1 : ℚ_[7])‖)

def innerPotentialRoot : ℚ_[7] := Classical.choose exists_inner_potential_root

theorem innerPotentialRoot_equation :
    1 + 13 * innerPotentialRoot + 49 * innerPotentialRoot ^ 2 = 0 :=
  (Classical.choose_spec exists_inner_potential_root).1

theorem innerPotentialRoot_norm : ‖innerPotentialRoot‖ = 1 :=
  (Classical.choose_spec exists_inner_potential_root).2

theorem innerPotentialRoot_ne_zero : innerPotentialRoot ≠ 0 := by
  intro h
  simpa [h] using innerPotentialRoot_norm

theorem potential_root_derivative_square (a : ℚ_[7])
    (ha : 1 + 13 * a + 49 * a ^ 2 = 0) : (13 + 98 * a) ^ 2 = -27 := by
  linear_combination 196 * ha

theorem potential_root_simple (a : ℚ_[7])
    (ha : 1 + 13 * a + 49 * a ^ 2 = 0) : 13 + 98 * a ≠ 0 := by
  intro h
  have hs := potential_root_derivative_square a ha
  rw [h] at hs
  norm_num at hs

def outerPotentialRoot : ℚ_[7] := (49 * innerPotentialRoot)⁻¹

theorem potential_root_factorization (x : ℚ_[7]) :
    1 + 13 * x + 49 * x ^ 2 =
      49 * (x - innerPotentialRoot) * (x - outerPotentialRoot) := by
  have ha := innerPotentialRoot_equation
  have hn := innerPotentialRoot_ne_zero
  unfold outerPotentialRoot
  field_simp [hn]
  linear_combination x * ha

theorem outerPotentialRoot_norm : ‖outerPotentialRoot‖ = 49 := by
  unfold outerPotentialRoot
  simp only [mul_inv, norm_mul, norm_inv, innerPotentialRoot_norm,
    inv_one, mul_one]
  simpa only [norm_inv] using norm_inverse_49

theorem outerPotentialRoot_equation :
    1 + 13 * outerPotentialRoot + 49 * outerPotentialRoot ^ 2 = 0 := by
  rw [potential_root_factorization]
  simp

end Zeta7Common

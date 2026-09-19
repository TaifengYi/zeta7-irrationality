import Zeta7Proof.ActualTargetDifferential

/-! Exact normalization and polynomial division costs for the actual ordinary primitives.
These inequalities do not assert the still missing radius estimate for K. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
open PowerSeries
namespace Zeta7Common
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

theorem padic_inverse_nat_norm_le (n : ℕ) : ‖(n : ℚ_[7])⁻¹‖ ≤ (n : ℝ) := by
  by_cases hn : n = 0
  · subst n; simp
  have hp : 7 ^ padicValNat 7 n ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) pow_padicValNat_dvd
  have he : ‖(n : ℚ_[7])⁻¹‖ = (7 : ℝ) ^ padicValNat 7 n := by
    rw [norm_inv, show (n : ℚ_[7]) = ((n : ℚ) : ℚ_[7]) by norm_cast,
      Padic.eq_padicNorm, padicNorm.eq_zpow_of_nonzero (by exact_mod_cast hn)]
    simp [padicValRat.of_nat, zpow_neg, zpow_natCast]
  rw [he]
  exact_mod_cast hp

theorem normalized_primitive_coeff (f : ℚ_[7]⟦X⟧) (n : ℕ) :
    coeff (n + 1) (rescale (49 : ℚ_[7])⁻¹ (primitive f)) =
      (49 : ℚ_[7])⁻¹ * coeff n (rescale (49 : ℚ_[7])⁻¹ f) / (n + 1 : ℚ_[7]) := by
  simp only [coeff_rescale, primitive, coeff_mk, Nat.add_eq_zero_iff, Nat.one_ne_zero,
    and_false, ↓reduceIte, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, pow_succ]
  ring

theorem norm_inverse_49 : ‖(49 : ℚ_[7])⁻¹‖ = (49 : ℝ) := by
  have hp : ‖(7 : ℚ_[7])‖ = (7 : ℝ)⁻¹ := Padic.norm_p
  rw [norm_inv, show (49 : ℚ_[7]) = (7 : ℚ_[7]) ^ 2 by norm_num, norm_pow, hp]
  norm_num

theorem normalized_primitive_norm_le (f : ℚ_[7]⟦X⟧) (n : ℕ) :
    ‖coeff (n + 1) (rescale (49 : ℚ_[7])⁻¹ (primitive f))‖ ≤
      49 * (n + 1 : ℝ) * ‖coeff n (rescale (49 : ℚ_[7])⁻¹ f)‖ := by
  rw [normalized_primitive_coeff, div_eq_mul_inv, norm_mul, norm_mul, norm_inverse_49]
  have h := mul_le_mul_of_nonneg_left (padic_inverse_nat_norm_le (n + 1))
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 49) (norm_nonneg (coeff n (rescale (49 : ℚ_[7])⁻¹ f))))
  simpa only [Nat.cast_add, Nat.cast_one, mul_assoc, mul_left_comm, mul_comm] using h

theorem targetJ1_normalized_norm_le (n : ℕ) :
    ‖coeff (n + 1) (rescale (49 : ℚ_[7])⁻¹ (targetGerms 4))‖ ≤
      49 * (n + 1 : ℝ) * ‖coeff n (rescale (49 : ℚ_[7])⁻¹ (targetGerms 3))‖ :=
  normalized_primitive_norm_le (targetGerms 3) n

theorem targetJ2_normalized_norm_le (n : ℕ) :
    ‖coeff (n + 2) (rescale (49 : ℚ_[7])⁻¹ (targetGerms 5))‖ ≤
      2401 * (n + 2 : ℝ) * (n + 1 : ℝ) *
        ‖coeff n (rescale (49 : ℚ_[7])⁻¹ (targetGerms 3))‖ := by
  have h := normalized_primitive_norm_le (targetGerms 4) (n + 1)
  have he : primitive (targetGerms 4) = targetGerms 5 := rfl
  rw [he] at h
  have h' := mul_le_mul_of_nonneg_left (targetJ1_normalized_norm_le n)
    (by positivity : (0 : ℝ) ≤ 49 * ((n + 1 : ℕ) + 1 : ℝ))
  calc
    _ ≤ 49 * (n + 2 : ℝ) * (49 * (n + 1 : ℝ) *
        ‖coeff n (rescale (49 : ℚ_[7])⁻¹ (targetGerms 3))‖) := by
      simpa only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using h.trans h'
    _ = _ := by ring

theorem target_primitives_initial_coefficients :
    coeff 0 (targetGerms 4) = 0 ∧ coeff 1 (targetGerms 4) = 0 ∧
    coeff 0 (targetGerms 5) = 0 ∧ coeff 1 (targetGerms 5) = 0 ∧ coeff 2 (targetGerms 5) = 0 := by
  have h := targetK_constant
  rw [← coeff_zero_eq_constantCoeff] at h
  change coeff 0 (primitive (targetGerms 3)) = 0 ∧
    coeff 1 (primitive (targetGerms 3)) = 0 ∧
    coeff 0 (primitive (primitive (targetGerms 3))) = 0 ∧
    coeff 1 (primitive (primitive (targetGerms 3))) = 0 ∧
    coeff 2 (primitive (primitive (targetGerms 3))) = 0
  simp [primitive, h]

end Zeta7Common

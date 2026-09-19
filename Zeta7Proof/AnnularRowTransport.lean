import Zeta7Proof.AnnularActualRows

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
namespace Zeta7Annulus.ClosedAnnulus
local instance AnnularRowTransport_local1 : Fact (Nat.Prime 7) := ⟨by decide⟩
variable {r R : ℝ} [Fact (0 < r)] [Fact (0 < R)]

set_option maxHeartbeats 800000 in
theorem actualAnnularRow_next_0 (hr : 1 < r) (hR : R < 49) (hrR : r ≤ R) (k : Fin 3) :
    fourComponentNext (actualAnnularRow (r := r) (R := R) k.castSucc)
      (actualAnnularMultiplier k) 0 = actualAnnularRow k.succ 0 := by
  have h := congrArg (rationalPolynomialMap (r := r) (R := R))
    (Zeta7AnnularRows.indexed_recurrence_0 k)
  simp only [map_mul, map_add, map_sub, map_pow, map_ofNat, rationalPolynomialMap_C,
    Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, ← annularP_polynomial, ← annularN_polynomial] at h
  simp only [← actualAnnularRow_clear hr hR hrR, ← actualAnnularMultiplier_clear hr hR hrR,
    ← actualAnnularRow_euler_clear hr hR hrR, ← annularSubstitution_euler_clear hr hR hrR,
    ← annularSubstitution_clear hr hR hrR] at h
  simp only [fourComponentNext, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  apply ((pnDenominator_isUnit hr hR hrR 4 10).mul (pnDenominator_isUnit hr hR hrR 2 4)).mul_left_cancel
  unfold pnDenominator at h ⊢
  linear_combination -h


set_option maxHeartbeats 800000 in
theorem actualAnnularRow_next_1 (hr : 1 < r) (hR : R < 49) (hrR : r ≤ R) (k : Fin 3) :
    fourComponentNext (actualAnnularRow (r := r) (R := R) k.castSucc)
      (actualAnnularMultiplier k) 1 = actualAnnularRow k.succ 1 := by
  have h := congrArg (rationalPolynomialMap (r := r) (R := R))
    (Zeta7AnnularRows.indexed_recurrence_1 k)
  simp only [map_mul, map_add, map_sub, map_pow, map_ofNat, rationalPolynomialMap_C,
    Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, ← annularP_polynomial, ← annularN_polynomial] at h
  simp only [← actualAnnularRow_clear hr hR hrR, ← actualAnnularMultiplier_clear hr hR hrR,
    ← actualAnnularRow_euler_clear hr hR hrR, ← annularSubstitution_euler_clear hr hR hrR,
    ← annularSubstitution_clear hr hR hrR] at h
  simp only [fourComponentNext, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, hypergeometricAlpha_factored]
  apply ((pnDenominator_isUnit hr hR hrR 4 10).mul (pnDenominator_isUnit hr hR hrR 2 4)).mul_left_cancel
  unfold pnDenominator at h ⊢
  linear_combination -h


set_option maxHeartbeats 800000 in
theorem actualAnnularRow_next_2 (hr : 1 < r) (hR : R < 49) (hrR : r ≤ R) (k : Fin 3) :
    fourComponentNext (actualAnnularRow (r := r) (R := R) k.castSucc)
      (actualAnnularMultiplier k) 2 = actualAnnularRow k.succ 2 := by
  have h := congrArg (rationalPolynomialMap (r := r) (R := R))
    (Zeta7AnnularRows.indexed_recurrence_2 k)
  simp only [map_mul, map_add, map_sub, map_pow, map_ofNat, rationalPolynomialMap_C,
    Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, ← annularP_polynomial, ← annularN_polynomial] at h
  simp only [← actualAnnularRow_clear hr hR hrR, ← actualAnnularMultiplier_clear hr hR hrR,
    ← actualAnnularRow_euler_clear hr hR hrR, ← annularSubstitution_euler_clear hr hR hrR,
    ← annularSubstitution_clear hr hR hrR] at h
  simp only [fourComponentNext, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, hypergeometricGamma_factored]
  apply ((pnDenominator_isUnit hr hR hrR 4 10).mul (pnDenominator_isUnit hr hR hrR 2 4)).mul_left_cancel
  unfold pnDenominator at h ⊢
  linear_combination -h


set_option maxHeartbeats 800000 in
theorem actualAnnularRow_next_3 (hr : 1 < r) (hR : R < 49) (hrR : r ≤ R) (k : Fin 3) :
    fourComponentNext (actualAnnularRow (r := r) (R := R) k.castSucc)
      (actualAnnularMultiplier k) 3 = actualAnnularRow k.succ 3 := by
  have h := congrArg (rationalPolynomialMap (r := r) (R := R))
    (Zeta7AnnularRows.indexed_recurrence_3 k)
  simp only [map_mul, map_add, map_sub, map_pow, map_ofNat, rationalPolynomialMap_C,
    Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, ← annularP_polynomial, ← annularN_polynomial] at h
  simp only [← actualAnnularRow_clear hr hR hrR, ← actualAnnularMultiplier_clear hr hR hrR,
    ← actualAnnularRow_euler_clear hr hR hrR, ← annularSubstitution_euler_clear hr hR hrR,
    ← annularSubstitution_clear hr hR hrR] at h
  simp only [fourComponentNext, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, hypergeometricAlpha_add_Gamma]
  apply ((pnDenominator_isUnit hr hR hrR 4 10).mul (pnDenominator_isUnit hr hR hrR 2 4)).mul_left_cancel
  unfold pnDenominator at h ⊢
  linear_combination -h


theorem actualAnnularRow_next (hr : 1 < r) (hR : R < 49) (hrR : r ≤ R) (k : Fin 3) :
    fourComponentNext (actualAnnularRow (r := r) (R := R) k.castSucc)
      (actualAnnularMultiplier k) = actualAnnularRow k.succ := by
  funext i
  fin_cases i
  · exact actualAnnularRow_next_0 hr hR hrR k
  · exact actualAnnularRow_next_1 hr hR hrR k
  · exact actualAnnularRow_next_2 hr hR hrR k
  · exact actualAnnularRow_next_3 hr hR hrR k

theorem actualAnnularRow_value_derivative (hr : 1 < r) (hR : R < 49) (hrR : r ≤ R) (k : Fin 3) :
    euler (fourComponentValue (actualAnnularRow (r := r) (R := R) k.castSucc)) =
      fourComponentValue (actualAnnularRow k.succ) := by
  rw [fourComponent_derivative hr hR hrR _ _ (actualAnnularRow_reduction hr hR hrR k 0)
    (actualAnnularRow_reduction hr hR hrR k 1) (actualAnnularRow_reduction hr hR hrR k 2),
    actualAnnularRow_next hr hR hrR]

end Zeta7Annulus.ClosedAnnulus

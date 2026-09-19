import Zeta7Proof.AnnularActualColumnIdentity

/-! Bounds on the actual completed matrix, retaining its original source columns. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
namespace Zeta7Annulus
local instance AnnularCompletedMatrix_prime : Fact (Nat.Prime 7) := ⟨by decide⟩
open Zeta7Common Zeta7AnnularSource

def actualCompletedMatrix (d : ℕ) (c : ℚ) (ell : ℕ) (hell : ell ≤ 6) :=
  (actualNormalizedTargetMatrix d c).submatrix (sourceOrder d ell hell) (sourceOrder d ell hell) *
    (sourceCompletion actualIntegralAnnularCoefficients d ell hell).map (algebraMap ℤ_[7] ℚ_[7])

theorem actualCompletedMatrix_original (d : ℕ) (c : ℚ) (ell : ℕ) (hell : ell ≤ 6)
    (i : Fin (d - 6) ⊕ Remaining d ell hell) (m : Fin (d - 6)) :
    actualCompletedMatrix d c ell hell i (.inl m) =
      -actualAnnularTail m.val (actualTailRow d c (sourceOrder d ell hell i)) := by
  rw [← actualSourceColumn_image d c m (sourceOrder d ell hell i)]
  simp only [actualCompletedMatrix, Matrix.mul_apply, Matrix.submatrix_apply,
    Matrix.map_apply, sourceCompletion_original]
  exact Fintype.sum_equiv (sourceOrder d ell hell) _ _ (fun _ => rfl)

theorem actualCompletedMatrix_coordinate (d : ℕ) (c : ℚ) (ell : ℕ) (hell : ell ≤ 6)
    (i : Fin (d - 6) ⊕ Remaining d ell hell) (j : Remaining d ell hell) :
    actualCompletedMatrix d c ell hell i (.inr j) =
      actualNormalizedTargetMatrix d c (sourceOrder d ell hell i)
        (sourceOrder d ell hell (.inr j)) := by
  classical
  simp only [actualCompletedMatrix, Matrix.mul_apply, Matrix.submatrix_apply,
    Matrix.map_apply, sourceCompletion, completion_coordinate, apply_ite,
    map_one, map_zero, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true]

theorem actualNormalizedTargetMatrix_bound {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (d : ℕ) (c : ℚ) (i j : TailIndex d),
      ‖actualNormalizedTargetMatrix d c i j‖ ≤ C * (σ⁻¹) ^ (7 * d + 175) := by
  obtain ⟨C, hC, hCb⟩ := actualNormalizedTargetCoefficients_bound hσ hσ1
  refine ⟨C, hC, fun d c i j => ?_⟩
  have hr := actualTailRow_position_lower d c i
  have hu := actualTailRow_lt d c i
  have hj := j.2.isLt
  have hle : j.2.val ≤ actualTailRow d c i := by omega
  have hb := hCb j.1 (actualTailRow d c i - j.2.val)
  change ‖PowerSeries.coeff (actualTailRow d c i - j.2.val)
    (PowerSeries.rescale (49 : ℚ_[7])⁻¹ (targetGerms j.1))‖ ≤ _ at hb
  simp only [actualNormalizedTargetMatrix, tailMatrix, PowerSeries.coeff_X_pow_mul', if_pos hle]
  exact hb.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ (by rw [one_le_inv₀ hσ]; exact hσ1.le) (by omega)) hC)

theorem actualCompletedMatrix_bounds {ρ σ : ℝ}
    (hρ : (1 / 49 : ℝ) < ρ) (hρσ : ρ < σ) (hσ1 : σ < 1) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (d : ℕ) (c : ℚ) (ell : ℕ) (hell : ell ≤ 6)
      (i : Fin (d - 6) ⊕ Remaining d ell hell),
      (∀ m : Fin (d - 6), ‖actualCompletedMatrix d c ell hell i (.inl m)‖ ≤
        (C * (σ⁻¹) ^ (7 * d + 175)) * ρ ^ m.val) ∧
      (∀ j : Remaining d ell hell, ‖actualCompletedMatrix d c ell hell i (.inr j)‖ ≤
        C * (σ⁻¹) ^ (7 * d + 175)) := by
  have hσ : 0 < σ := lt_trans (lt_trans (by norm_num) hρ) hρσ
  have hρ0 : 0 < ρ := lt_trans (by norm_num) hρ
  obtain ⟨A, hA, hAb⟩ := actualAnnularTail_bound hρ hρσ hσ1
  obtain ⟨B, hB, hBb⟩ := actualNormalizedTargetMatrix_bound hσ hσ1
  refine ⟨max 1 (max A B), le_max_left _ _, fun d c ell hell i => ⟨?_, ?_⟩⟩
  · intro m
    rw [actualCompletedMatrix_original, norm_neg]
    have hrow := actualTailRow_lt d c (sourceOrder d ell hell i)
    have hb := (hAb m.val (actualTailRow d c (sourceOrder d ell hell i))).2
    have hA' : A ≤ max 1 (max A B) := (le_max_left A B).trans (le_max_right _ _)
    calc
      _ ≤ A * ρ ^ m.val * (σ⁻¹) ^ (actualTailRow d c (sourceOrder d ell hell i)) := hb
      _ ≤ max 1 (max A B) * ρ ^ m.val * (σ⁻¹) ^ (7 * d + 175) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hA' (by positivity))
          (pow_le_pow_right₀ (by rw [one_le_inv₀ hσ]; exact hσ1.le) (by omega))
          (by positivity) (by positivity)
      _ = _ := by ring
  · intro j
    rw [actualCompletedMatrix_coordinate]
    exact (hBb d c _ _).trans (mul_le_mul_of_nonneg_right
      ((le_max_right A B).trans (le_max_right _ _)) (by positivity))

theorem padic_det_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℚ_[7]) (B : ι → ℝ) (hB : ∀ j, 0 ≤ B j)
    (hM : ∀ i j, ‖M i j‖ ≤ B j) : ‖M.det‖ ≤ ∏ j, B j := by
  rw [Matrix.det_apply]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
    (Finset.prod_nonneg (fun j _ => hB j))
  intro s _
  rw [norm_units_zsmul, norm_prod]
  exact Finset.prod_le_prod (fun j _ => norm_nonneg _) (fun j _ => hM (s j) j)

theorem actualCompletedMatrix_det_bound {ρ σ : ℝ}
    (hρ : (1 / 49 : ℝ) < ρ) (hρσ : ρ < σ) (hσ1 : σ < 1) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (d : ℕ) (c : ℚ) (ell : ℕ) (hell : ell ≤ 6),
      ‖(actualCompletedMatrix d c ell hell).det‖ ≤
        (C * (σ⁻¹) ^ (7 * d + 175)) ^ (6 * d) *
          ρ ^ (∑ m : Fin (d - 6), m.val) := by
  classical
  obtain ⟨C, hC, hCb⟩ := actualCompletedMatrix_bounds hρ hρσ hσ1
  have hρ0 : 0 < ρ := lt_trans (by norm_num) hρ
  have hσ0 : 0 < σ := hρ0.trans hρσ
  refine ⟨C, hC, fun d c ell hell => ?_⟩
  let T := C * (σ⁻¹) ^ (7 * d + 175)
  let w : Fin (d - 6) ⊕ Remaining d ell hell → ℝ := Sum.elim (fun m => ρ ^ m.val) (fun _ => 1)
  have hb := padic_det_bound (actualCompletedMatrix d c ell hell) (fun j => T * w j)
    (by intro j; cases j <;> dsimp [w, T] <;> positivity)
    (by intro i j; cases j with
        | inl m => exact (hCb d c ell hell i).1 m
        | inr j => simpa only [w, Sum.elim_inr, mul_one] using (hCb d c ell hell i).2 j)
  have hcard : Fintype.card (Fin (d - 6) ⊕ Remaining d ell hell) = 6 * d := by
    rw [Fintype.card_congr (sourceOrder d ell hell)]
    simp [TailIndex]
  simpa only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, hcard,
    Fintype.prod_sum_type, w, Sum.elim_inl, Sum.elim_inr, Finset.prod_const_one, mul_one,
    Finset.prod_pow_eq_pow_sum, T, one_pow, mul_one, mul_pow] using hb

end Zeta7Annulus

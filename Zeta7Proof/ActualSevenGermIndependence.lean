import Zeta7Proof.ActualSevenFrameIndependence

/-! Return from the ordinary-primitive frame to the original germs and instantiate
the existing block and common-determinant bridges. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
open scoped RatFunc LaurentSeries
open PowerSeries
local instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩
namespace Zeta7Germ

def originalSixFrame (c : ℚ) : Fin 6 → ℂ⸨X⸩ :=
  let U := fun j => complexSeries (Zeta7Common.primitiveFrame c j)
  ![actualH c, laurentD (actualH c), laurentD (laurentD (actualH c)),
    U 0, U 1 + embed RatFunc.X * U 0,
    U 2 + embed RatFunc.X * U 1 + embed RatFunc.X ^ 2 * U 0 / 2]

theorem complexSeries_X : complexSeries (X : ℚ⟦X⟧) = embed RatFunc.X := by
  simp [complexSeries, embed_X]

theorem actual_original_six_frame (c : ℚ) (j : Fin 6) :
    Zeta7Common.complexLaurentGerms c (.inr j) = originalSixFrame c j := by
  change complexSeries (Zeta7Common.rationalGerms c j) = _
  fin_cases j
  · rfl
  · exact complexSeries_euler _
  · change complexSeries (Zeta7Common.euler (Zeta7Common.euler (Zeta7Common.rationalH c))) =
      laurentD (laurentD (actualH c))
    rw [complexSeries_euler, complexSeries_euler]
  · rfl
  · change complexSeries (Zeta7Common.rationalGerms c 4) = originalSixFrame c 4
    rw [Zeta7Common.primitiveFrame_inverse_one, complexSeries_add, complexSeries_mul, complexSeries_X]
    rfl
  · change complexSeries (Zeta7Common.rationalGerms c 5) = originalSixFrame c 5
    rw [Zeta7Common.primitiveFrame_inverse_two]
    simp only [complexSeries_add, complexSeries_mul, complexSeries_half]
    have hx : complexSeries (X ^ 2 : ℚ⟦X⟧) = embed RatFunc.X ^ 2 := by
      simp [complexSeries, embed_X]
    rw [complexSeries_X, hx]
    simp only [originalSixFrame, Matrix.cons_val]
    ring

end Zeta7Germ
namespace Zeta7Common
open Zeta7Germ

theorem complexLaurentGerms_independent (c : ℚ) :
    LinearIndependent (RatFunc ℂ) (complexLaurentGerms c) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro a ha j
  have hunit : complexLaurentGerms c (.inl ()) = (1 : ℂ⸨X⸩) := by
    simp [complexLaurentGerms, sevenGerms]
  simp [Fintype.sum_sum_type, Fintype.sum_unique, hunit,
    actual_original_six_frame, originalSixFrame, Fin.sum_univ_succ,
    rational_smul] at ha
  have hrel : embed (a (.inl ())) + jetEval c ![a (.inr 0), a (.inr 1), a (.inr 2)] +
      primitiveEval c ![a (.inr 3) + RatFunc.X * a (.inr 4) + RatFunc.X ^ 2 * a (.inr 5) / 2,
        a (.inr 4) + RatFunc.X * a (.inr 5), a (.inr 5)] = 0 := by
    simp only [jetEval, primitiveEval, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, map_add, map_mul, map_div₀, map_pow, map_ofNat]
    simp only [Matrix.head_cons, Matrix.tail_cons]
    have hx1 : embed RatFunc.X = HahnSeries.single (1 : ℤ) 1 := by
      rw [embed_X, HahnSeries.ofPowerSeries_X]
    have hx2 : embed RatFunc.X ^ 2 = HahnSeries.single (2 : ℤ) 1 := by
      simp [hx1, HahnSeries.single_pow]
    rw [hx2, hx1]
    linear_combination ha
  obtain ⟨hr, hv, hw⟩ := actual_seven_frame_relation c _ _ _ hrel
  have hv0 := congrFun hv 0
  have hv1 := congrFun hv 1
  have hv2 := congrFun hv 2
  have hw0 := congrFun hw 0
  have hw1 := congrFun hw 1
  have hw2 := congrFun hw 2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Pi.zero_apply] at *
  cases j with
  | inl u => cases u; exact hr
  | inr j => fin_cases j <;> simp_all

theorem rationalGerms_block_independent (c : ℚ) (d : ℕ) :
    LinearIndependent ℚ (blockSeries d (rationalGerms c)) :=
  actual_block_independent_of_ratFunc c (complexLaurentGerms_independent c) d

theorem rationalGerms_fullRank (c : ℚ) (d : ℕ) :
    Zeta7Jump.FullRank (coefficientRow d (rationalGerms c)) :=
  actual_fullRank_of_ratFunc c (complexLaurentGerms_independent c) d

def actualCommonDeterminant (d : ℕ) (c : ℚ) : ℚ :=
  commonDeterminant d c (rationalGerms_fullRank c d)

theorem actualCommonDeterminant_ne_zero (d : ℕ) (c : ℚ) : actualCommonDeterminant d c ≠ 0 :=
  commonDeterminant_ne_zero d c (rationalGerms_fullRank c d)

theorem actualCommonDeterminant_productFormula (d : ℕ) (c : ℚ) :
    Zeta7ProductFormula.arch (actualCommonDeterminant d c) +
      Zeta7ProductFormula.target (actualCommonDeterminant d c) +
      Zeta7ProductFormula.auxiliary (actualCommonDeterminant d c) = 0 :=
  commonDeterminant_productFormula d c (rationalGerms_fullRank c d)

theorem actualCommonDeterminant_target (d : ℕ) (c : ℚ)
    (hc : (c : ℚ_[7]) = Zeta7Main.eta) :
    (tailMatrix d targetGerms (selectedTailRow d c (rationalGerms_fullRank c d))).det =
      (actualCommonDeterminant d c : ℚ_[7]) :=
  commonDeterminant_target d c hc (rationalGerms_fullRank c d)

end Zeta7Common

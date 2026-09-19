import Zeta7Proof.ActualAnnularSaving
import Zeta7Proof.ActualRationalTargetBridge

/-! The annular bound on the same nonzero rational family in the product formula. -/
noncomputable section
set_option autoImplicit false
namespace Zeta7Common
local instance ActualAnnularTargetBridge_prime : Fact (Nat.Prime 7) := ⟨by decide⟩

theorem actual_annular_family_of_rationality
    (hq : Zeta7Partial.IsRationalSeven Zeta7Main.zeta7Three) :
    ∃ c : ℚ, (c : ℚ_[7]) = Zeta7Main.eta ∧
      (∀ d : ℕ, actualCommonDeterminant d c ≠ 0 ∧
        (tailMatrix d targetGerms
          (selectedTailRow d c (rationalGerms_fullRank c d))).det =
            (actualCommonDeterminant d c : ℚ_[7]) ∧
        Real.log |(actualCommonDeterminant d c : ℝ)| +
          Real.log ‖(tailMatrix d targetGerms
            (selectedTailRow d c (rationalGerms_fullRank c d))).det‖ +
          Zeta7ProductFormula.auxiliary (actualCommonDeterminant d c) = 0) ∧
      ∀ δ : ℝ, 0 < δ → δ < 2 → ∃ K : ℝ, 0 ≤ K ∧
        ∀ d : ℕ, 7 ≤ d → (43 - δ) * (d : ℝ) ^ 2 - K * d ≤
          (padicValRat 7 (actualCommonDeterminant d c) : ℝ) := by
  obtain ⟨c, hc, hf⟩ := actual_determinant_family_of_rationality hq
  refine ⟨c, hc, hf, fun δ hδ hδ2 => ?_⟩
  obtain ⟨K, hK, hb⟩ := Zeta7Annulus.actualCommonDeterminant_annular_saving δ hδ hδ2
  exact ⟨K, hK, fun d hd => hb d hd c hc⟩

end Zeta7Common

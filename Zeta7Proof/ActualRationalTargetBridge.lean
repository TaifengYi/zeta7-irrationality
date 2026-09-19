import Zeta7Proof.ActualSevenGermIndependence
import Zeta7Proof.Zeta7_Lean_Partial

/-! Rationality of the actual Kubota--Leopoldt value supplies the same
parameter for every canonical determinant. This is a rationality reduction,
not an irrationality theorem or an estimate. -/
noncomputable section
set_option autoImplicit false
open PowerSeries
namespace Zeta7Common
local instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

theorem rational_parameter_of_zeta7Three
    (hq : Zeta7Partial.IsRationalSeven Zeta7Main.zeta7Three) :
    ∃ c : ℚ, (c : ℚ_[7]) = Zeta7Main.eta := by
  obtain ⟨q, hq⟩ := hq
  refine ⟨q / 2, ?_⟩
  simpa only [Rat.cast_div, Rat.cast_ofNat, hq, Zeta7Main.eta]

theorem zeta7Three_rational_iff_eta_rational :
    Zeta7Partial.IsRationalSeven Zeta7Main.zeta7Three ↔
      Zeta7Partial.IsRationalSeven Zeta7Main.eta := by
  constructor
  · exact rational_parameter_of_zeta7Three
  · rintro ⟨c, hc⟩
    refine ⟨2 * c, ?_⟩
    rw [Rat.cast_mul, Rat.cast_ofNat, hc, Zeta7Main.eta]
    ring

theorem actualCommonDeterminant_target_productFormula (d : ℕ) (c : ℚ)
    (hc : (c : ℚ_[7]) = Zeta7Main.eta) :
    Real.log |(actualCommonDeterminant d c : ℝ)| +
      Real.log ‖(tailMatrix d targetGerms
        (selectedTailRow d c (rationalGerms_fullRank c d))).det‖ +
      Zeta7ProductFormula.auxiliary (actualCommonDeterminant d c) = 0 :=
  commonDeterminant_productFormula_target d c hc (rationalGerms_fullRank c d)

/-- One rational parameter works simultaneously in all degrees, including zero. -/
theorem actual_determinant_family_of_rationality
    (hq : Zeta7Partial.IsRationalSeven Zeta7Main.zeta7Three) :
    ∃ c : ℚ, (c : ℚ_[7]) = Zeta7Main.eta ∧ ∀ d : ℕ,
      actualCommonDeterminant d c ≠ 0 ∧
      (tailMatrix d targetGerms
        (selectedTailRow d c (rationalGerms_fullRank c d))).det =
          (actualCommonDeterminant d c : ℚ_[7]) ∧
      Real.log |(actualCommonDeterminant d c : ℝ)| +
        Real.log ‖(tailMatrix d targetGerms
          (selectedTailRow d c (rationalGerms_fullRank c d))).det‖ +
        Zeta7ProductFormula.auxiliary (actualCommonDeterminant d c) = 0 := by
  obtain ⟨c, hc⟩ := rational_parameter_of_zeta7Three hq
  exact ⟨c, hc, fun d => ⟨actualCommonDeterminant_ne_zero d c,
    actualCommonDeterminant_target d c hc,
    actualCommonDeterminant_target_productFormula d c hc⟩⟩

end Zeta7Common

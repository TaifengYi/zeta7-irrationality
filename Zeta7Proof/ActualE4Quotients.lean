import Zeta7Proof.LevelSevenE4Forms
import Zeta7Proof.PhiQExpansion
import Zeta7Proof.QuotientCoefficientChecks

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open UpperHalfPlane PowerSeries Zeta7Main
open scoped ModularForm
namespace Zeta7LevelSeven

theorem GammaSeven_period_one : (1 : ℝ) ∈ GammaSeven.strictPeriods := by
  simp [GammaSeven, CongruenceSubgroup.strictPeriods_Gamma0]

def phiCombination (a b : ℚ) : ModularForm GammaSeven 6 :=
  phiModularForm 0 + (a : ℂ) • phiModularForm 1 + (b : ℂ) • phiModularForm 2

theorem qExpansion_add_forms {k : ℤ} (f g : ModularForm GammaSeven k) :
    qExpansion 1 (f + g) = qExpansion 1 f + qExpansion 1 g := by
  change qExpansion 1 ((f : ℍ → ℂ) + (g : ℍ → ℂ)) = _
  exact UpperHalfPlane.qExpansion_add
    (ModularFormClass.analyticAt_cuspFunction_zero f (by norm_num) GammaSeven_period_one)
    (ModularFormClass.analyticAt_cuspFunction_zero g (by norm_num) GammaSeven_period_one)

theorem qExpansion_smul_forms {k : ℤ} (a : ℂ) (f : ModularForm GammaSeven k) :
    qExpansion 1 (a • f) = a • qExpansion 1 f := by
  change qExpansion 1 (a • (f : ℍ → ℂ)) = _
  exact UpperHalfPlane.qExpansion_smul
    (ModularFormClass.analyticAt_cuspFunction_zero f (by norm_num) GammaSeven_period_one) a

theorem phiCombination_qExpansion (a b : ℚ) :
    qExpansion 1 (phiCombination a b) =
      (phiZeroSeries * (1 + C a * xSeries + C b * xSeries ^ 2)).map (algebraMap ℚ ℂ) := by
  have hp (i : Fin 3) : qExpansion 1 (phiModularForm i) =
      (phiZeroSeries * xSeries ^ i.val).map (algebraMap ℚ ℂ) := phi_qExpansion i
  have hrat (q : ℚ) : (algebraMap ℚ ℂ) q = (q : ℂ) := rfl
  have hs := (qExpansion_add_forms (phiModularForm 0) ((a : ℂ) • phiModularForm 1)).trans
    (congrArg (fun s : ℂ⟦X⟧ => qExpansion 1 (phiModularForm 0) + s)
      (qExpansion_smul_forms (a : ℂ) (phiModularForm 1)))
  have ht := (qExpansion_add_forms (phiModularForm 0 + (a : ℂ) • phiModularForm 1)
    ((b : ℂ) • phiModularForm 2)).trans
      (congrArg₂ (fun s t : ℂ⟦X⟧ => s + t) hs
        (qExpansion_smul_forms (b : ℂ) (phiModularForm 2)))
  change qExpansion 1 (phiCombination a b) = _ at ht
  rw [ht]
  simp only [
    hp, map_mul, map_add, map_one, map_pow, map_C, smul_eq_C_mul]
  norm_num only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, mul_one,
    hrat]
  ring

def actualASquare : ModularForm GammaSeven 4 := actualAModularForm.mul actualAModularForm

theorem actualASquare_qExpansion : qExpansion 1 actualASquare =
    (ASeries.map (algebraMap ℚ ℂ)) ^ 2 := by
  change qExpansion 1 (actualAModularForm.mul actualAModularForm) = _
  rw [ModularForm.qExpansion_mul (by norm_num : (0 : ℝ) < 1) GammaSeven_period_one]
  change qExpansion 1 actualA * qExpansion 1 actualA = _
  rw [actualA_qExpansion, pow_two]

def firstWeightTen : ModularForm GammaSeven 10 :=
  (phiCombination 13 49).mul E4ModularForm -
    (phiCombination 245 2401).mul actualASquare

def secondWeightTen : ModularForm GammaSeven 10 :=
  (phiCombination 13 49).mul E4SevenModularForm -
    (phiCombination 5 1).mul actualASquare

theorem firstWeightTen_qExpansion : qExpansion 1 firstWeightTen =
    (phiZeroSeries * Zeta7Common.firstQuotientDifference).map (algebraMap ℚ ℂ) := by
  have ha : qExpansion 1 actualAModularForm = ASeries.map (algebraMap ℚ ℂ) := actualA_qExpansion
  have he : qExpansion 1 E4ModularForm =
      Zeta7Common.eisensteinFourQ.map (algebraMap ℚ ℂ) :=
    Zeta7Common.eisensteinFourQ_classical.symm
  simp only [firstWeightTen, FunLike.coe_sub,
    ModularForm.qExpansion_sub (by norm_num : (0 : ℝ) < 1) GammaSeven_period_one,
    ModularForm.qExpansion_mul (by norm_num : (0 : ℝ) < 1) GammaSeven_period_one,
    phiCombination_qExpansion, actualASquare_qExpansion, ha, he, Zeta7Common.firstQuotientDifference,
    map_mul, map_sub, map_add, map_pow, map_one, map_ofNat, map_C]
  norm_num only [map_ofNat]
  ring

theorem secondWeightTen_qExpansion : qExpansion 1 secondWeightTen =
    (phiZeroSeries * Zeta7Common.secondQuotientDifference).map (algebraMap ℚ ℂ) := by
  have ha : qExpansion 1 actualAModularForm = ASeries.map (algebraMap ℚ ℂ) := actualA_qExpansion
  simp only [secondWeightTen, FunLike.coe_sub,
    ModularForm.qExpansion_sub (by norm_num : (0 : ℝ) < 1) GammaSeven_period_one,
    ModularForm.qExpansion_mul (by norm_num : (0 : ℝ) < 1) GammaSeven_period_one,
    phiCombination_qExpansion, actualASquare_qExpansion, ha, E4_seven_qExpansion,
    Zeta7Common.secondQuotientDifference,
    map_mul, map_sub, map_add, map_pow, map_one, map_ofNat, map_C]
  norm_num only [map_ofNat, map_one]
  ring

theorem phiZero_mul_order_seven {f : ℚ⟦X⟧} (hf : ∀ n ≤ 4, coeff n f = 0) :
    (7 : ℕ∞) ≤ ((phiZeroSeries * f).map (algebraMap ℚ ℂ)).order := by
  have ho : (5 : ℕ∞) ≤ f.order := nat_le_order f 5 (fun n hn => hf n (by omega))
  apply le_trans _ (le_order_map (φ := phiZeroSeries * f) (algebraMap ℚ ℂ))
  rw [order_mul, phiZeroSeries_order]
  change (2 : ℕ∞) + 5 ≤ 2 + f.order
  exact add_le_add_right ho (2 : ℕ∞)

theorem firstWeightTen_zero : firstWeightTen = 0 := by
  apply weightTen_eq_zero_of_order
  rw [firstWeightTen_qExpansion]
  exact phiZero_mul_order_seven Zeta7Common.firstQuotientDifference_coeff_small

theorem secondWeightTen_zero : secondWeightTen = 0 := by
  apply weightTen_eq_zero_of_order
  rw [secondWeightTen_qExpansion]
  exact phiZero_mul_order_seven Zeta7Common.secondQuotientDifference_coeff_small

theorem phiZeroSeries_ne_zero : phiZeroSeries ≠ 0 := by
  intro h
  have ho := phiZeroSeries_order
  rw [h, order_zero] at ho
  exact (by decide : (⊤ : ℕ∞) ≠ 2) ho

theorem phiZero_map_mul_eq_zero {f : ℚ⟦X⟧}
    (h : (phiZeroSeries * f).map (algebraMap ℚ ℂ) = 0) : f = 0 := by
  have hi := PowerSeries.map_injective (algebraMap ℚ ℂ) (algebraMap ℚ ℂ).injective
  have hz : phiZeroSeries * f = 0 := hi (h.trans (map_zero _).symm)
  exact (mul_eq_zero.mp hz).resolve_left phiZeroSeries_ne_zero

theorem firstQuotientDifference_zero : Zeta7Common.firstQuotientDifference = 0 := by
  apply phiZero_map_mul_eq_zero
  rw [← firstWeightTen_qExpansion, firstWeightTen_zero]
  exact qExpansion_zero 1

theorem secondQuotientDifference_zero : Zeta7Common.secondQuotientDifference = 0 := by
  apply phiZero_map_mul_eq_zero
  rw [← secondWeightTen_qExpansion, secondWeightTen_zero]
  exact qExpansion_zero 1

theorem actual_E4_quotient :
    (1 + 13 * xSeries + 49 * xSeries ^ 2) * Zeta7Common.eisensteinFourQ =
      ASeries ^ 2 * (1 + 245 * xSeries + 2401 * xSeries ^ 2) := by
  simpa only [Zeta7Common.firstQuotientDifference, map_ofNat] using
    sub_eq_zero.mp firstQuotientDifference_zero

theorem actual_E4_seven_quotient :
    (1 + 13 * xSeries + 49 * xSeries ^ 2) *
        expand 7 (by decide) Zeta7Common.eisensteinFourQ =
      ASeries ^ 2 * (1 + 5 * xSeries + xSeries ^ 2) := by
  simpa only [Zeta7Common.secondQuotientDifference, map_ofNat] using
    sub_eq_zero.mp secondQuotientDifference_zero

end Zeta7LevelSeven

import Zeta7Proof.ActualE4Quotients
import Zeta7Proof.ActualEisensteinClassical

/-! The weight-six companion of `actual_E4_quotient`:

`E₆ · P(x)² = A³ · T(x)` with `P = 1 + 13x + 49x²`, `T = 1 - 490x - 21609x² - 235298x³ - 823543x⁴`,

as an identity of q-expansions of the actual coordinate `x`, the actual weight-two form `A` and the
classical Eisenstein series `E₆`. The proof clears denominators with the weight-six eta quotients
`φ_i = φ₀ xⁱ`, obtains a weight-eighteen form on `Γ₀(7)` whose expansion begins at `q¹³`, and
applies the level-one Sturm bound to its norm (weight 144, bound 12). The nine needed coefficients
are checked by the kernel. -/
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open UpperHalfPlane PowerSeries Zeta7Main Matrix.SpecialLinearGroup HeckeRing.GL2 ModularForm Function
open scoped MatrixGroups ModularForm Manifold
namespace Zeta7LevelSeven

abbrev classicalE6 := ModularForm.E (k := 6) (by decide)

theorem classicalE6_slash (γ : SL(2, ℤ)) :
    (classicalE6 : ℍ → ℂ) ∣[(6 : ℤ)] γ = classicalE6 := by
  rw [SL_slash]
  exact SlashInvariantForm.slash_action_eqn classicalE6 _ ⟨γ, rfl⟩

def E6SlashInvariant : SlashInvariantForm GammaSeven 6 where
  toFun := classicalE6
  slash_action_eq' γ hγ := by
    obtain ⟨δ, _, rfl⟩ := hγ
    simpa [SL_slash, mapGL] using classicalE6_slash δ

def E6ModularForm : ModularForm GammaSeven 6 :=
  levelSevenFormOfTwoCusps E6SlashInvariant (ModularFormClass.holo classicalE6)
    (ModularFormClass.bdd_at_infty classicalE6)
    (ModularFormClass.bdd_at_infty_slash classicalE6 ModularGroup.S)

theorem E6ModularForm_coe : (E6ModularForm : ℍ → ℂ) = classicalE6 := rfl

theorem E6_qExpansion : qExpansion 1 E6ModularForm =
    Zeta7Common.eisensteinSixQ.map (algebraMap ℚ ℂ) :=
  Zeta7Common.eisensteinSixQ_classical.symm

def actualACube : ModularForm GammaSeven 6 := actualAModularForm.mul actualASquare

theorem actualACube_qExpansion : qExpansion 1 actualACube =
    (ASeries.map (algebraMap ℚ ℂ)) ^ 3 := by
  change qExpansion 1 (actualAModularForm.mul actualASquare) = _
  rw [ModularForm.qExpansion_mul (by norm_num : (0 : ℝ) < 1) GammaSeven_period_one,
    actualASquare_qExpansion]
  change qExpansion 1 actualA * _ = _
  rw [actualA_qExpansion]
  ring

/-- `φ₀² P(x)²`. -/
def phiPSquare : ModularForm GammaSeven 12 := (phiCombination 13 49).mul (phiCombination 13 49)

/-- `φ₀² T(x)`. -/
def phiT : ModularForm GammaSeven 12 :=
  (phiModularForm 0).mul (phiCombination (-490) (-21609)) -
    (phiModularForm 2).mul (phiCombination 235298 823543 - phiModularForm 0)

/-- The difference series `P(x)² E₆ - A³ T(x)`. -/
def sixQuotientDifference : ℚ⟦X⟧ :=
  (1 + C 13 * xSeries + C 49 * xSeries ^ 2) ^ 2 * Zeta7Common.eisensteinSixQ -
    ASeries ^ 3 * (1 - C 490 * xSeries - C 21609 * xSeries ^ 2 - C 235298 * xSeries ^ 3 -
      C 823543 * xSeries ^ 4)

def weightEighteen : ModularForm GammaSeven 18 :=
  phiPSquare.mul E6ModularForm - phiT.mul actualACube

theorem qExpansion_mul_forms {k l : ℤ} (f : ModularForm GammaSeven k) (g : ModularForm GammaSeven l) :
    qExpansion 1 (f.mul g) = qExpansion 1 f * qExpansion 1 g :=
  ModularForm.qExpansion_mul (by norm_num : (0 : ℝ) < 1) GammaSeven_period_one f g

theorem qExpansion_sub_forms {k : ℤ} (f g : ModularForm GammaSeven k) :
    qExpansion 1 (f - g) = qExpansion 1 f - qExpansion 1 g := by
  simpa using ModularForm.qExpansion_sub (by norm_num : (0 : ℝ) < 1) GammaSeven_period_one f g

theorem weightEighteen_qExpansion : qExpansion 1 weightEighteen =
    (phiZeroSeries ^ 2 * sixQuotientDifference).map (algebraMap ℚ ℂ) := by
  have hp (i : Fin 3) : qExpansion 1 (phiModularForm i) =
      (phiZeroSeries * xSeries ^ i.val).map (algebraMap ℚ ℂ) := phi_qExpansion i
  have hrat (q : ℚ) : (algebraMap ℚ ℂ) q = (q : ℂ) := rfl
  simp only [weightEighteen, phiPSquare, phiT, FunLike.coe_sub,
    ModularForm.qExpansion_sub (by norm_num : (0 : ℝ) < 1) GammaSeven_period_one,
    ModularForm.qExpansion_mul (by norm_num : (0 : ℝ) < 1) GammaSeven_period_one,
    phiCombination_qExpansion, E6_qExpansion, actualACube_qExpansion, hp,
    sixQuotientDifference, map_mul, map_sub, map_add, map_pow, map_one, map_C, map_neg, map_ofNat]
  norm_num only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, mul_one, map_ofNat,
    map_neg, hrat]
  ring

/-- The weight-eighteen level-seven vanishing theorem, via the weight-144 norm. -/
theorem weightEighteen_eq_zero_of_order (f : ModularForm GammaSeven 18)
    (hf : (13 : ℕ∞) ≤ (qExpansion 1 f).order) : f = 0 := by
  apply (levelSevenNorm_eq_zero_iff f).mp
  apply ModularForm.sturm_bound_levelOne_nat (k := 144)
  exact lt_of_lt_of_le (by norm_num : ((144 / 12 : ℕ) : ℕ∞) < 13)
    (hf.trans (order_le_levelSevenNorm f))

/-! ### Kernel-checked coefficients -/

namespace Coeffs
open Zeta7Common

theorem x0 : constantCoeff xSeries = 0 := xSeries_constant
theorem x1 : coeff 1 xSeries = 1 := xSeries_linear
theorem x2 : coeff 2 xSeries = 4 := xSeries_coeff_two
theorem x3 : coeff 3 xSeries = 14 := xSeries_coeff_three
theorem x4 : coeff 4 xSeries = 40 := xSeries_coeff_four

theorem A_small (n : ℕ) (hn : n ≤ 8) :
    coeff n ASeries = ![1, 4, 12, 16, 28, 24, 48, 4, 60] ⟨n, by omega⟩ := by
  interval_cases n <;> rw [ASeries_coeff] <;> decide +kernel +revert

theorem A0 : constantCoeff ASeries = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply]; exact A_small 0 (by norm_num)

theorem x5 : coeff 5 xSeries = 105 := by
  have h := congrArg (coeff 5) ASeries_mul_xSeries
  change coeff 5 (ASeries * xSeries) = coeff 5 (euler xSeries) at h
  norm_num [coeff_mul, Finset.Nat.antidiagonal_succ, euler_coeff, A_small, A0,
    coeff_zero_eq_constantCoeff, x0, x1, x2, x3, x4] at h
  linear_combination (-1 / 4 : ℚ) * h

theorem x6 : coeff 6 xSeries = 252 := by
  have h := congrArg (coeff 6) ASeries_mul_xSeries
  change coeff 6 (ASeries * xSeries) = coeff 6 (euler xSeries) at h
  norm_num [coeff_mul, Finset.Nat.antidiagonal_succ, euler_coeff, A_small, A0,
    coeff_zero_eq_constantCoeff, x0, x1, x2, x3, x4, x5] at h
  linear_combination (-1 / 5 : ℚ) * h

theorem x7 : coeff 7 xSeries = 574 := by
  have h := congrArg (coeff 7) ASeries_mul_xSeries
  change coeff 7 (ASeries * xSeries) = coeff 7 (euler xSeries) at h
  norm_num [coeff_mul, Finset.Nat.antidiagonal_succ, euler_coeff, A_small, A0,
    coeff_zero_eq_constantCoeff, x0, x1, x2, x3, x4, x5, x6] at h
  linear_combination (-1 / 6 : ℚ) * h

theorem x8 : coeff 8 xSeries = 1236 := by
  have h := congrArg (coeff 8) ASeries_mul_xSeries
  change coeff 8 (ASeries * xSeries) = coeff 8 (euler xSeries) at h
  norm_num [coeff_mul, Finset.Nat.antidiagonal_succ, euler_coeff, A_small, A0,
    coeff_zero_eq_constantCoeff, x0, x1, x2, x3, x4, x5, x6, x7] at h
  linear_combination (-1 / 7 : ℚ) * h

theorem E6_small (n : ℕ) (hn : n ≤ 8) :
    coeff n eisensteinSixQ = ![1, -504, -16632, -122976, -532728, -1575504, -4058208, -8471232,
      -17047800] ⟨n, by omega⟩ := by
  rw [eisensteinSixQ]
  simp only [map_sub, coeff_one, coeff_C_mul, coeff_mk, sigmaFive]
  interval_cases n <;> decide +kernel +revert


theorem xp2 (n : ℕ) (hn : n ≤ 8) :
    coeff n (xSeries ^ 2) = ![0, 0, 1, 8, 44, 192, 726, 2464, 7704] ⟨n, by omega⟩ := by
  interval_cases n <;> norm_num [pow_two, coeff_mul, Finset.Nat.antidiagonal_succ,
    coeff_zero_eq_constantCoeff, x0, x1, x2, x3, x4, x5, x6, x7, x8]

theorem xp3 (n : ℕ) (hn : n ≤ 8) :
    coeff n (xSeries ^ 3) = ![0, 0, 0, 1, 12, 90, 520, 2535, 10908] ⟨n, by omega⟩ := by
  rw [pow_succ]
  interval_cases n <;> norm_num [coeff_mul, Finset.Nat.antidiagonal_succ,
    coeff_zero_eq_constantCoeff, x0, x1, x2, x3, x4, x5, x6, x7, x8, xp2]

theorem xp4 (n : ℕ) (hn : n ≤ 8) :
    coeff n (xSeries ^ 4) = ![0, 0, 0, 0, 1, 16, 152, 1088, 6460] ⟨n, by omega⟩ := by
  rw [pow_succ]
  interval_cases n <;> norm_num [coeff_mul, Finset.Nat.antidiagonal_succ,
    coeff_zero_eq_constantCoeff, x0, x1, x2, x3, x4, x5, x6, x7, x8, xp3]

theorem Ap2 (n : ℕ) (hn : n ≤ 8) :
    coeff n (ASeries ^ 2) = ![1, 8, 40, 128, 328, 656, 1216, 1864, 2856] ⟨n, by omega⟩ := by
  interval_cases n <;> norm_num [pow_two, coeff_mul, Finset.Nat.antidiagonal_succ,
    coeff_zero_eq_constantCoeff, A0, A_small]

theorem Ap3 (n : ℕ) (hn : n ≤ 8) :
    coeff n (ASeries ^ 3) = ![1, 12, 84, 400, 1476, 4392, 11184, 24780, 49668] ⟨n, by omega⟩ := by
  rw [pow_succ]
  interval_cases n <;> norm_num [coeff_mul, Finset.Nat.antidiagonal_succ,
    coeff_zero_eq_constantCoeff, A0, A_small, Ap2]

/-- `P(x)`. -/
def Pq : ℚ⟦X⟧ := 1 + C 13 * xSeries + C 49 * xSeries ^ 2

/-- `T(x)`. -/
def Tq : ℚ⟦X⟧ := 1 - C 490 * xSeries - C 21609 * xSeries ^ 2 - C 235298 * xSeries ^ 3 -
  C 823543 * xSeries ^ 4

theorem Pser (n : ℕ) (hn : n ≤ 8) :
    coeff n Pq =
      ![1, 13, 101, 574, 2676, 10773, 38850, 128198, 393564] ⟨n, by omega⟩ := by
  unfold Pq
  interval_cases n <;> norm_num [coeff_one, coeff_C_mul, coeff_zero_eq_constantCoeff,
    x0, x1, x2, x3, x4, x5, x6, x7, x8, xp2]

theorem Pc0 : constantCoeff Pq = 1 := by
  simp [Pq, x0]

theorem P2ser (n : ℕ) (hn : n ≤ 8) :
    coeff n (Pq ^ 2) =
      ![1, 26, 371, 3774, 30477, 207070, 1227826, 6514690, 31496356] ⟨n, by omega⟩ := by
  rw [pow_two]
  interval_cases n <;> norm_num [coeff_mul, Finset.Nat.antidiagonal_succ, Pser,
    coeff_zero_eq_constantCoeff, Pc0]

theorem Tser (n : ℕ) (hn : n ≤ 8) :
    coeff n Tq =
      ![1, -490, -23569, -415030, -4617515, -38553886, -263345110, -1546021050, -8053799740]
        ⟨n, by omega⟩ := by
  unfold Tq
  interval_cases n <;> norm_num [coeff_one, coeff_C_mul, coeff_zero_eq_constantCoeff,
    x0, x1, x2, x3, x4, x5, x6, x7, x8, xp2, xp3, xp4]

theorem P2c0 : constantCoeff (Pq ^ 2) = 1 := by
  simp [Pc0]

theorem Tc0 : constantCoeff Tq = 1 := by
  simp [Tq, x0]

theorem A3c0 : constantCoeff (ASeries ^ 3) = 1 := by simp [A0]

theorem E6c0 : constantCoeff eisensteinSixQ = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply]; exact E6_small 0 (by norm_num)

theorem diff_small (n : ℕ) (hn : n ≤ 8) : coeff n sixQuotientDifference = 0 := by
  have e : sixQuotientDifference = Pq ^ 2 * eisensteinSixQ - ASeries ^ 3 * Tq := rfl
  rw [e]
  rw [map_sub]
  interval_cases n <;> norm_num [coeff_mul, Finset.Nat.antidiagonal_succ, P2ser, Tser, Ap3,
    E6_small, coeff_zero_eq_constantCoeff, P2c0, Tc0, A3c0, E6c0]

end Coeffs

theorem phiZeroSq_mul_order {f : ℚ⟦X⟧} (hf : ∀ n ≤ 8, coeff n f = 0) :
    (13 : ℕ∞) ≤ ((phiZeroSeries ^ 2 * f).map (algebraMap ℚ ℂ)).order := by
  have ho : (9 : ℕ∞) ≤ f.order := nat_le_order f 9 (fun n hn => hf n (by omega))
  apply le_trans _ (le_order_map (φ := phiZeroSeries ^ 2 * f) (algebraMap ℚ ℂ))
  rw [order_mul, pow_two, order_mul, phiZeroSeries_order]
  change (2 : ℕ∞) + 2 + 9 ≤ 2 + 2 + f.order
  exact add_le_add_right ho _

theorem weightEighteen_zero : weightEighteen = 0 := by
  apply weightEighteen_eq_zero_of_order
  rw [weightEighteen_qExpansion]
  exact phiZeroSq_mul_order Coeffs.diff_small

theorem sixQuotientDifference_zero : sixQuotientDifference = 0 := by
  have hi := PowerSeries.map_injective (algebraMap ℚ ℂ) (algebraMap ℚ ℂ).injective
  have h : (phiZeroSeries ^ 2 * sixQuotientDifference).map (algebraMap ℚ ℂ) = 0 := by
    rw [← weightEighteen_qExpansion, weightEighteen_zero]; exact qExpansion_zero 1
  have hz : phiZeroSeries ^ 2 * sixQuotientDifference = 0 := hi (h.trans (map_zero _).symm)
  exact (mul_eq_zero.mp hz).resolve_left (pow_ne_zero 2 phiZeroSeries_ne_zero)

/-- **The E₆ quotient identity** `P(x)² E₆ = A³ T(x)` of q-expansions. -/
theorem actual_E6_quotient :
    (1 + C 13 * xSeries + C 49 * xSeries ^ 2) ^ 2 * Zeta7Common.eisensteinSixQ =
      ASeries ^ 3 * (1 - C 490 * xSeries - C 21609 * xSeries ^ 2 - C 235298 * xSeries ^ 3 -
        C 823543 * xSeries ^ 4) :=
  sub_eq_zero.mp sixQuotientDifference_zero

/-- **As weight-eighteen forms**: `φ₀²P(x)² E₆ = φ₀²T(x) A³` on the upper half-plane. -/
theorem weightEighteen_function (τ : ℍ) :
    phiPSquare τ * classicalE6 τ = phiT τ * actualACube τ := by
  have h := congrArg (fun f : ModularForm GammaSeven 18 => (f : ℍ → ℂ) τ) weightEighteen_zero
  simp only [weightEighteen] at h
  change phiPSquare τ * E6ModularForm τ - phiT τ * actualACube τ = 0 at h
  rw [E6ModularForm_coe] at h
  linear_combination h

end Zeta7LevelSeven

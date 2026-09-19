import Zeta7Proof.Radius49U7Psi
import Zeta7Proof.Radius49Coordinate
import Zeta7Proof.LevelSevenACusps
import Zeta7Proof.ActualModularEquation
import Zeta7Proof.ActualEisensteinClassical
import Zeta7Proof.ArchQPullback

/-! Radius internalization, HO: the Frobenius (`τ ↦ 7τ`) transforms of `E₄` and `E₆`.

Evaluating the proved level-seven identities `E₄ P(x) = A² N(x)` and `E₆ P(x)² = A³ T(x)` at the
Fricke point `-1/(7τ)`, where `x ↦ 1/(49x)`, `A ↦ -7τ² A` and `E_k ↦ (7τ)^k E_k(7τ)`, gives
* `VE4_function : E₄(7τ) P(x) = A² (1 + 5x + x²)`,
* `VE6_function : E₆(7τ) P(x)² = A³ T̃(x)` with `T̃ = polyTt`,
and hence the formal identities `VE4_formal`, `VE6_formal` over `ℚ`. In particular the Katz ratio
`E₆(q)/E₆(q⁷) = T(x)/T̃(x)` (`katz_ratio`). No published radius input is used. -/

noncomputable section
set_option autoImplicit false
open UpperHalfPlane Matrix.SpecialLinearGroup ModularForm Complex Filter Topology PowerSeries
open scoped MatrixGroups ModularForm Manifold
namespace Zeta7Radius49
open Zeta7LevelSeven Zeta7Valence Zeta7Main Zeta7Arch HeckeRing.GL2 EisensteinSeries

theorem coe_S_mulSeven (τ : ℍ) :
    ((ModularGroup.S • mulSeven τ : ℍ) : ℂ) = -1 / (7 * (τ : ℂ)) := by
  rw [modular_S_smul]
  simp [mulSeven, neg_div, div_eq_mul_inv]

theorem denom_S_coe (z : ℍ) : denom ModularGroup.S (z : ℂ) = (z : ℂ) :=
  ModularGroup.denom_S (z := z)

theorem denom_S_mulSeven (τ : ℍ) : denom ModularGroup.S (mulSeven τ : ℂ) = 7 * (τ : ℂ) := by
  rw [denom_S_coe]; rfl

theorem x_S_mulSeven (τ : ℍ) :
    etaCoordinate (ModularGroup.S • mulSeven τ) = (49 * etaCoordinate τ)⁻¹ := by
  rw [← Xf_eq, ← Xf_eq, coe_S_mulSeven]
  exact projectX_fricke τ.im_pos

theorem divSeven_mulSeven (τ : ℍ) : divSeven (mulSeven τ) = τ := by
  apply UpperHalfPlane.ext
  change (7 * (τ : ℂ)) / 7 = τ
  ring

theorem levelRaise_mulSeven (τ : ℍ) : levelRaiseMatrix 7 • τ = mulSeven τ := by
  apply UpperHalfPlane.ext
  rw [coe_levelRaiseMatrix_smul]
  rfl

theorem actualA_eq (τ : ℍ) : actualA τ = (1 / 6) * (7 * E2 (mulSeven τ) - E2 τ) := by
  simp only [actualA, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, levelRaiseFun_apply,
    levelRaise_mulSeven]

/-- `A(-1/(7τ)) = -7τ² A(τ)`. -/
theorem A_S_mulSeven (τ : ℍ) :
    actualA (ModularGroup.S • mulSeven τ) = -7 * (τ : ℂ) ^ 2 * actualA τ := by
  have h := actualA_S_value (mulSeven τ)
  rw [SL_slash_apply, denom_S_mulSeven, divSeven_mulSeven] at h
  have hτ : (τ : ℂ) ≠ 0 := τ.ne_zero
  rw [actualA_eq τ]
  rw [zpow_neg, zpow_ofNat] at h
  field_simp at h
  linear_combination h / 6

theorem E4_S_mulSeven (τ : ℍ) :
    classicalE4 (ModularGroup.S • mulSeven τ) = (7 * (τ : ℂ)) ^ 4 * classicalE4 (mulSeven τ) := by
  rw [E4_smul, denom_S_mulSeven]

theorem E6_S_mulSeven (τ : ℍ) :
    classicalE6 (ModularGroup.S • mulSeven τ) = (7 * (τ : ℂ)) ^ 6 * classicalE6 (mulSeven τ) := by
  rw [E6_smul, denom_S_mulSeven]

/-- The Fricke transform of `N`. -/
def polyNt (x : ℂ) : ℂ := 1 + 5 * x + x ^ 2

/-- **`E₄(7τ) P(x) = A² (1 + 5x + x²)`.** -/
theorem VE4_function (τ : ℍ) :
    classicalE4 (mulSeven τ) * polyP (etaCoordinate τ) = actualA τ ^ 2 * polyNt (etaCoordinate τ) := by
  have h := E4_function (ModularGroup.S • mulSeven τ)
  rw [E4_S_mulSeven, A_S_mulSeven, x_S_mulSeven] at h
  have hx : etaCoordinate τ ≠ 0 := by rw [← Xf_eq]; exact Xf_ne_zero τ.im_pos
  have hτ : (τ : ℂ) ≠ 0 := τ.ne_zero
  simp only [polyP, polyN, polyNt] at h ⊢
  field_simp at h
  linear_combination h / 2401

/-- **`E₆(7τ) P(x)² = A³ T̃(x)`.** -/
theorem VE6_function (τ : ℍ) :
    classicalE6 (mulSeven τ) * polyP (etaCoordinate τ) ^ 2 =
      actualA τ ^ 3 * polyTt (etaCoordinate τ) := by
  have h := E6_function (ModularGroup.S • mulSeven τ)
  rw [E6_S_mulSeven, A_S_mulSeven, x_S_mulSeven] at h
  have hx : etaCoordinate τ ≠ 0 := by rw [← Xf_eq]; exact Xf_ne_zero τ.im_pos
  have hτ : (τ : ℂ) ≠ 0 := τ.ne_zero
  simp only [polyP, polyT, polyTt] at h ⊢
  field_simp at h
  linear_combination h / 823543


/-! ### Formal versions -/

theorem sum_divisors_pow_le (n k : ℕ) : ∑ d ∈ n.divisors, (d : ℚ) ^ k ≤ (n : ℚ) ^ (k + 1) := by
  calc ∑ d ∈ n.divisors, (d : ℚ) ^ k ≤ ∑ _d ∈ n.divisors, (n : ℚ) ^ k := by
        apply Finset.sum_le_sum
        intro d hd
        exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast Nat.divisor_le hd) k
    _ = (n.divisors.card : ℚ) * (n : ℚ) ^ k := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (n : ℚ) * (n : ℚ) ^ k := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast Nat.card_divisors_le_self n
    _ = (n : ℚ) ^ (k + 1) := by ring

theorem E6Q_tempered : RTempered Zeta7Common.eisensteinSixQ := by
  apply RTempered.of_bound_succ 505 6
  intro n
  have hs := sum_divisors_pow_le n 5
  norm_num at hs
  have hs0 : 0 ≤ ∑ d ∈ n.divisors, (d : ℚ) ^ 5 := Finset.sum_nonneg (fun _ _ => by positivity)
  have hn : (0 : ℚ) ≤ n := Nat.cast_nonneg n
  simp only [Zeta7Common.eisensteinSixQ, map_sub, coeff_one, map_mul, coeff_C_mul, coeff_mk,
    Zeta7Common.sigmaFive]
  have hb : |(if n = 0 then (1 : ℚ) else 0) - 504 * ∑ d ∈ n.divisors, (d : ℚ) ^ 5| ≤
      505 * ((n : ℚ) + 1) ^ 6 := by
    have h1 : (n : ℚ) ^ 6 ≤ ((n : ℚ) + 1) ^ 6 := pow_le_pow_left₀ hn (by linarith) 6
    have h2 : (1 : ℚ) ≤ ((n : ℚ) + 1) ^ 6 := one_le_pow₀ (by linarith)
    split_ifs
    · rw [abs_le]; constructor <;> nlinarith
    · rw [abs_le]; constructor <;> nlinarith
  exact_mod_cast hb

theorem E4Q_tempered : RTempered Zeta7Common.eisensteinFourQ := by
  apply RTempered.of_bound_succ 241 4
  intro n
  have hs := sum_divisors_pow_le n 3
  norm_num at hs
  have hs0 : 0 ≤ ∑ d ∈ n.divisors, (d : ℚ) ^ 3 := Finset.sum_nonneg (fun _ _ => by positivity)
  have hn : (0 : ℚ) ≤ n := Nat.cast_nonneg n
  simp only [Zeta7Common.eisensteinFourQ, map_add, coeff_one, map_mul, coeff_C_mul, coeff_mk,
    Zeta7Common.sigmaThree]
  have hb : |(if n = 0 then (1 : ℚ) else 0) + 240 * ∑ d ∈ n.divisors, (d : ℚ) ^ 3| ≤
      241 * ((n : ℚ) + 1) ^ 4 := by
    have h1 : (n : ℚ) ^ 4 ≤ ((n : ℚ) + 1) ^ 4 := pow_le_pow_left₀ hn (by linarith) 4
    have h2 : (1 : ℚ) ≤ ((n : ℚ) + 1) ^ 4 := one_le_pow₀ (by linarith)
    split_ifs
    · rw [abs_le]; constructor <;> nlinarith
    · rw [abs_le]; constructor <;> nlinarith
  exact_mod_cast hb

theorem evalQ_E4 (z : ℍ) :
    evalQ (Zeta7Common.eisensteinFourQ.map (algebraMap ℚ ℂ)) (Function.Periodic.qParam 1 z) =
      classicalE4 z := by
  have h := ModularForm.hasSum_qExpansion (f := ModularForm.E (k := 4) (by decide)) one_pos
    one_mem_strictPeriods_SL z
  rw [← Zeta7Common.eisensteinFourQ_classical] at h
  exact h.tsum_eq

theorem evalQ_E6 (z : ℍ) :
    evalQ (Zeta7Common.eisensteinSixQ.map (algebraMap ℚ ℂ)) (Function.Periodic.qParam 1 z) =
      classicalE6 z := by
  have h := ModularForm.hasSum_qExpansion (f := ModularForm.E (k := 6) (by decide)) one_pos
    one_mem_strictPeriods_SL z
  rw [← Zeta7Common.eisensteinSixQ_classical] at h
  exact h.tsum_eq

theorem evalQ_A (z : ℍ) :
    evalQ (ASeries.map (algebraMap ℚ ℂ)) (Function.Periodic.qParam 1 z) = actualA z := by
  have h := ModularForm.hasSum_qExpansion (f := actualAModularForm) one_pos
    GammaSeven_period_one z
  have hq : qExpansion 1 actualAModularForm = ASeries.map (algebraMap ℚ ℂ) := actualA_qExpansion
  rw [hq] at h
  exact h.tsum_eq

theorem qParam_mulSeven (σ : ℍ) :
    Function.Periodic.qParam 1 (σ : ℂ) ^ 7 = Function.Periodic.qParam 1 (mulSeven σ : ℂ) := by
  simp only [Function.Periodic.qParam, mulSeven, ← Complex.exp_nat_mul]
  congr 1; push_cast; ring

theorem norm_qParam_one_lt (σ : ℍ) : ‖Function.Periodic.qParam 1 (σ : ℂ)‖ < 1 := by
  rw [← qParam_seven_pow, norm_pow]
  exact pow_lt_one₀ (norm_nonneg _) (norm_qParam_seven_lt_one σ) (by norm_num)

/-- **Formal `E₆(q⁷) P(x)² = A³ T̃(x)`.** -/
theorem VE6_formal :
    vSeven Zeta7Common.eisensteinSixQ * (1 + 13 * xSeries + 49 * xSeries ^ 2) ^ 2 =
      ASeries ^ 3 * (1 + 14 * xSeries + 63 * xSeries ^ 2 + 70 * xSeries ^ 3 - 7 * xSeries ^ 4) := by
  apply map_injective_rat
  simp only [map_mul, map_add, map_pow, map_ofNat, map_sub, map_one, vSeven_map]
  have hE : Tempered (Zeta7Common.eisensteinSixQ.map (algebraMap ℚ ℂ)) := E6Q_tempered
  have hA : Tempered (ASeries.map (algebraMap ℚ ℂ)) := ASeries_tempered
  have hx : Tempered (xSeries.map (algebraMap ℚ ℂ)) := xSeries_tempered
  let S := temperedSubring
  let ee : S := ⟨vSeven (Zeta7Common.eisensteinSixQ.map (algebraMap ℚ ℂ)), tempered_vSeven hE⟩
  let aa : S := ⟨ASeries.map (algebraMap ℚ ℂ), hA⟩
  let xx : S := ⟨xSeries.map (algebraMap ℚ ℂ), hx⟩
  have hL : vSeven (Zeta7Common.eisensteinSixQ.map (algebraMap ℚ ℂ)) *
      (1 + 13 * xSeries.map (algebraMap ℚ ℂ) + 49 * xSeries.map (algebraMap ℚ ℂ) ^ 2) ^ 2 =
      ((ee * (1 + 13 * xx + 49 * xx ^ 2) ^ 2 : S) : ℂ⟦X⟧) := rfl
  have hR : ASeries.map (algebraMap ℚ ℂ) ^ 3 * (1 + 14 * xSeries.map (algebraMap ℚ ℂ) +
      63 * xSeries.map (algebraMap ℚ ℂ) ^ 2 + 70 * xSeries.map (algebraMap ℚ ℂ) ^ 3 -
      7 * xSeries.map (algebraMap ℚ ℂ) ^ 4) =
      ((aa ^ 3 * (1 + 14 * xx + 63 * xx ^ 2 + 70 * xx ^ 3 - 7 * xx ^ 4) : S) : ℂ⟦X⟧) := rfl
  rw [hL, hR]
  apply eq_of_evalQ_eventually (Subtype.prop _) (Subtype.prop _)
  apply eventually_punctured_of_atImInfty
  filter_upwards [Filter.univ_mem] with σ _
  have hq := norm_qParam_one_lt σ
  have e : ∀ f : S, evalQ (f : ℂ⟦X⟧) (Function.Periodic.qParam 1 (σ : ℂ)) =
      evalHom _ hq f := fun _ => rfl
  rw [e, e]
  simp only [map_mul, map_add, map_pow, map_ofNat, map_sub, map_one]
  have h1 : evalHom _ hq ee = classicalE6 (mulSeven σ) := by
    change evalQ (vSeven _) _ = _
    rw [evalQ_vSeven hE, qParam_mulSeven, evalQ_E6]
  have h2 : evalHom _ hq aa = actualA σ := evalQ_A σ
  have h3 : evalHom _ hq xx = etaCoordinate σ := xFun_qParam σ
  rw [h1, h2, h3]
  have := VE6_function σ
  simp only [polyP, polyTt] at this
  linear_combination this

/-- **Formal `E₄(q⁷) P(x) = A² (1 + 5x + x²)`.** -/
theorem VE4_formal :
    vSeven Zeta7Common.eisensteinFourQ * (1 + 13 * xSeries + 49 * xSeries ^ 2) =
      ASeries ^ 2 * (1 + 5 * xSeries + xSeries ^ 2) := by
  apply map_injective_rat
  simp only [map_mul, map_add, map_pow, map_ofNat, map_one, vSeven_map]
  have hE : Tempered (Zeta7Common.eisensteinFourQ.map (algebraMap ℚ ℂ)) := E4Q_tempered
  have hA : Tempered (ASeries.map (algebraMap ℚ ℂ)) := ASeries_tempered
  have hx : Tempered (xSeries.map (algebraMap ℚ ℂ)) := xSeries_tempered
  let S := temperedSubring
  let ee : S := ⟨vSeven (Zeta7Common.eisensteinFourQ.map (algebraMap ℚ ℂ)), tempered_vSeven hE⟩
  let aa : S := ⟨ASeries.map (algebraMap ℚ ℂ), hA⟩
  let xx : S := ⟨xSeries.map (algebraMap ℚ ℂ), hx⟩
  have hL : vSeven (Zeta7Common.eisensteinFourQ.map (algebraMap ℚ ℂ)) *
      (1 + 13 * xSeries.map (algebraMap ℚ ℂ) + 49 * xSeries.map (algebraMap ℚ ℂ) ^ 2) =
      ((ee * (1 + 13 * xx + 49 * xx ^ 2) : S) : ℂ⟦X⟧) := rfl
  have hR : ASeries.map (algebraMap ℚ ℂ) ^ 2 * (1 + 5 * xSeries.map (algebraMap ℚ ℂ) +
      xSeries.map (algebraMap ℚ ℂ) ^ 2) = ((aa ^ 2 * (1 + 5 * xx + xx ^ 2) : S) : ℂ⟦X⟧) := rfl
  rw [hL, hR]
  apply eq_of_evalQ_eventually (Subtype.prop _) (Subtype.prop _)
  apply eventually_punctured_of_atImInfty
  filter_upwards [Filter.univ_mem] with σ _
  have hq := norm_qParam_one_lt σ
  have e : ∀ f : S, evalQ (f : ℂ⟦X⟧) (Function.Periodic.qParam 1 (σ : ℂ)) =
      evalHom _ hq f := fun _ => rfl
  rw [e, e]
  simp only [map_mul, map_add, map_pow, map_ofNat, map_one]
  have h1 : evalHom _ hq ee = classicalE4 (mulSeven σ) := by
    change evalQ (vSeven _) _ = _
    rw [evalQ_vSeven hE, qParam_mulSeven, evalQ_E4]
  have h2 : evalHom _ hq aa = actualA σ := evalQ_A σ
  have h3 : evalHom _ hq xx = etaCoordinate σ := xFun_qParam σ
  rw [h1, h2, h3]
  have := VE4_function σ
  simp only [polyP, polyNt] at this
  linear_combination this

end Zeta7Radius49

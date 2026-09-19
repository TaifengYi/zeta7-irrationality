import Zeta7Proof.ActualTargetRootCancellation
import Zeta7Proof.SevenAdicDiscDivision
import Zeta7Proof.SevenAdicIntegrationRadius
import Zeta7Proof.SevenAdicOuterInverse

/-! Radius and uniform coefficient bounds for all six original target germs. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
open PowerSeries Filter Topology
namespace Zeta7Common
open Zeta7Main
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

def HSeries_inner_quotient : ℚ_[7]⟦X⟧ := discQuotient HSeries innerPotentialRoot

theorem HSeries_inner_quotient_identity :
    (X - C innerPotentialRoot) * HSeries_inner_quotient = HSeries := by
  rw [HSeries_inner_quotient, discQuotient_mul HSeries
    (HSeries_isRestricted 1 (by norm_num) (by norm_num)) _ innerPotentialRoot_norm,
    HSeries_inner_root_zero, map_zero, sub_zero]

theorem HSeries_inner_quotient_restricted (r : ℝ) (hr : 0 < r) (hr49 : r < 49) :
    IsRestricted r HSeries_inner_quotient := by
  obtain ⟨s, hs, hs49⟩ := exists_between (max_lt (by norm_num : (1 : ℝ) < 49) hr49)
  exact discQuotient_restricted HSeries ((le_max_left 1 r).trans hs.le) hr.le
    ((le_max_right 1 r).trans_lt hs) (HSeries_isRestricted s
      (lt_of_lt_of_le zero_lt_one ((le_max_left 1 r).trans hs.le)) hs49)
    innerPotentialRoot innerPotentialRoot_norm

theorem targetRH_cancelled :
    rationalForcing.map (algebraMap ℚ ℚ_[7]) * HSeries =
      C (49 : ℚ_[7])⁻¹ * targetS * HSeries_inner_quotient * linearReciprocal outerPotentialRoot := by
  have hb : outerPotentialRoot ≠ 0 := by
    intro h; have hh := outerPotentialRoot_norm; rw [h, norm_zero] at hh; norm_num at hh
  have hi := linearReciprocal_mul outerPotentialRoot hb
  have h49 : (C (49 : ℚ_[7]) : ℚ_[7]⟦X⟧) * C (49 : ℚ_[7])⁻¹ = 1 := by
    rw [← map_mul]; norm_num
  apply mul_left_cancel₀ targetP_ne_zero
  calc
    _ = (targetP * rationalForcing.map (algebraMap ℚ ℚ_[7])) * HSeries := by ring
    _ = targetS * HSeries := by rw [targetForcing_cleared]
    _ = (C (49 : ℚ_[7]) * C (49 : ℚ_[7])⁻¹) * targetS *
      ((X - C innerPotentialRoot) * HSeries_inner_quotient) *
      ((X - C outerPotentialRoot) * linearReciprocal outerPotentialRoot) := by
        rw [h49, hi, HSeries_inner_quotient_identity]; ring
    _ = _ := by rw [targetP_factorization]; ring

theorem targetRH_restricted (r : ℝ) (hr : 0 < r) (hr49 : r < 49) :
    IsRestricted r (rationalForcing.map (algebraMap ℚ ℚ_[7]) * HSeries) := by
  rw [targetRH_cancelled]
  have hs : IsRestricted r targetS := by
    convert restricted_polynomial (Polynomial.X * (1 + 10 * Polynomial.X) : Polynomial ℚ_[7]) r using 1
    have hx : Polynomial.coeToPowerSeries.ringHom (Polynomial.X : Polynomial ℚ_[7]) = X :=
      Polynomial.coe_X
    simp [targetS, ← Polynomial.coeToPowerSeries.ringHom_apply, map_ofNat, hx]
  exact isRestricted.mul r (isRestricted.mul r
    (isRestricted.mul r (isRestricted_C r ((49 : ℚ_[7])⁻¹)) hs)
    (HSeries_inner_quotient_restricted r hr hr49))
    (outerReciprocal_restricted r hr.le hr49)

theorem targetK_restricted (r : ℝ) (hr : 0 < r) (hr49 : r < 49) :
    IsRestricted r (targetGerms 3) := by
  obtain ⟨s, hrs, hs49⟩ := exists_between hr49
  apply restricted_of_euler hr.le (hr.trans hrs) hrs
  rw [targetK_derivative]
  exact targetRH_restricted s (hr.trans hrs) hs49

theorem targetJ1_restricted (r : ℝ) (hr : 0 < r) (hr49 : r < 49) :
    IsRestricted r (targetGerms 4) := by
  obtain ⟨s, hrs, hs49⟩ := exists_between hr49
  apply restricted_of_euler hr.le (hr.trans hrs) hrs
  have he : euler (targetGerms 4) = X * targetGerms 3 := euler_primitive_seven _
  rw [he]
  have hx : IsRestricted s (X : ℚ_[7]⟦X⟧) := by
    simpa only [Polynomial.coe_X] using
      restricted_polynomial (Polynomial.X : Polynomial ℚ_[7]) s
  exact isRestricted.mul s hx (targetK_restricted s (hr.trans hrs) hs49)

theorem targetJ2_restricted (r : ℝ) (hr : 0 < r) (hr49 : r < 49) :
    IsRestricted r (targetGerms 5) := by
  obtain ⟨s, hrs, hs49⟩ := exists_between hr49
  apply restricted_of_euler hr.le (hr.trans hrs) hrs
  have he : euler (targetGerms 5) = X * targetGerms 4 := euler_primitive_seven _
  rw [he]
  have hx : IsRestricted s (X : ℚ_[7]⟦X⟧) := by
    simpa only [Polynomial.coe_X] using
      restricted_polynomial (Polynomial.X : Polynomial ℚ_[7]) s
  exact isRestricted.mul s hx (targetJ1_restricted s (hr.trans hrs) hs49)

theorem targetGerms_restricted (j : Fin 6) (r : ℝ) (hr : 0 < r) (hr49 : r < 49) :
    IsRestricted r (targetGerms j) := by
  have h := HSeries_isRestricted r hr hr49
  have h1 := restricted_euler hr.le h
  have h2 := restricted_euler hr.le h1
  fin_cases j
  · exact h
  · exact h1
  · exact h2
  · exact targetK_restricted r hr hr49
  · exact targetJ1_restricted r hr hr49
  · exact targetJ2_restricted r hr hr49

theorem normalized_targetGerms_restricted (j : Fin 6) (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    IsRestricted r (rescale (49 : ℚ_[7])⁻¹ (targetGerms j)) := by
  rw [isRestricted_iff']
  have h := (isRestricted_iff' _ _).mp
    (targetGerms_restricted j (49 * r) (by positivity) (by nlinarith))
  convert h using 1
  funext n
  have he := Zeta7Section3.weighted_rescale_identity (targetGerms j) (49 * r) n
  simpa only [mul_div_cancel_left₀ r (by norm_num : (49 : ℝ) ≠ 0)] using he

theorem targetGerm_epsilon_norm_bound (j : Fin 6) (ε : ℝ) (hε : 0 < ε) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ,
      ‖coeff n (rescale (49 : ℚ_[7])⁻¹ (targetGerms j))‖ ≤ (7 : ℝ) ^ (ε * n + B) := by
  obtain ⟨B, hB, hb⟩ := Zeta7Radius49.restricted_coeff_bound ε
    ⟨_, normalized_targetGerms_restricted j ((7 : ℝ) ^ (-ε))
      (Real.rpow_pos_of_pos (by norm_num) _)
      (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith))⟩
  refine ⟨B, hB, fun n => ?_⟩
  have h := Zeta7Section3.norm_bound_of_valuation
    (coeff n (rescale (49 : ℚ_[7])⁻¹ (targetGerms j))) (-ε * n - B) (hb n)
  convert h using 1
  congr 1
  ring

theorem targetK_epsilon_norm_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ,
      ‖coeff n (rescale (49 : ℚ_[7])⁻¹ (targetGerms 3))‖ ≤ (7 : ℝ) ^ (ε * n + B) :=
  targetGerm_epsilon_norm_bound 3 ε hε

theorem targetGerms_all_six_norm_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (j : Fin 6) (n : ℕ),
      ‖coeff n (rescale (49 : ℚ_[7])⁻¹ (targetGerms j))‖ ≤ (7 : ℝ) ^ (ε * n + B) := by
  choose B hB hb using fun j : Fin 6 => targetGerm_epsilon_norm_bound j ε hε
  refine ⟨∑ j, B j, Finset.sum_nonneg (fun j _ => hB j), fun j n => (hb j n).trans ?_⟩
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  exact add_le_add le_rfl (Finset.single_le_sum (fun i _ => hB i) (Finset.mem_univ j))

end Zeta7Common

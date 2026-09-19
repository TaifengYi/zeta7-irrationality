import Zeta7Proof.ArchCTheorem
import Zeta7Proof.CertSurplus
import Zeta7Proof.ActualAnnularTargetBridge
import Zeta7Proof.AuxiliaryEstimateProof
import Zeta7Proof.CertLogSeven

/-! Phase V: the final contradiction, reduced to the single remaining energy comparison.

The C theorem (`c_theorem`) is stated with the actual energies `W_i = ∫ U dμ_i` and
`I = ∫ U dμ` of the actual six-circle measure. With `J = 7 I + π B`
(`constJ_eq_actual`), the C exponent is `J - (7/2) I = (7/2) I + π B`, so only an upper bound
for the actual energy `I` is needed. The explicit energy (48) evaluates it:
`explicitI` is `Σ w_i w_j E(y_i, y_j)` and `surplusS_gt` kernel-checks `S > 223/6250`.

* `final_contradiction_of_energy_le`: if `energyI ≤ explicitI`, the actual `zeta7Three` is not in
  the image of `ℚ`. The rational value zero is included.
* `eta_not_rational_of_energy_le`: the same for `eta = zeta7Three / 2`.

The hypothesis `energyI ≤ explicitI` is the upper half of the energy formula (48) for the actual
measure. It is proved as `Zeta7Valence.energyI_le_explicitI` and discharged in `FinalTheorem`;
nothing here assumes it globally. -/
noncomputable section
set_option autoImplicit false
namespace Zeta7Final
open Real Zeta7Arch Zeta7Cert Zeta7Common Zeta7ProductFormula

local instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

theorem circleW_vals : circleW 0 = 1 / 25 ∧ circleW 1 = 2 / 25 ∧ circleW 2 = 7 / 50 ∧
    circleW 3 = 17 / 100 ∧ circleW 4 = 6 / 25 ∧ circleW 5 = 33 / 100 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem circleY_vals : circleY 0 = 1 / 2 ∧ circleY 1 = 1 / 5 ∧ circleY 2 = 19 / 200 ∧
    circleY 3 = 11 / 200 ∧ circleY 4 = 7 / 200 ∧ circleY 5 = 23 / 1000 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem bnd_vals : bnd 0 = 0 ∧ bnd 1 = 7 / 25 ∧ bnd 2 = 21 / 25 ∧ bnd 3 = 91 / 50 ∧
    bnd 4 = 301 / 100 ∧ bnd 5 = 469 / 100 ∧ bnd 6 = 7 := by
  obtain ⟨w0, w1, w2, w3, w4, w5⟩ := circleW_vals
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [bnd, Fin.sum_univ_six, w0, w1, w2, w3, w4, w5] <;>
    norm_num

/-- `J = 7 I + π B` for the actual energies. -/
theorem constJ_eq_actual : constJ = 7 * energyI + π * (281603 / 156250 : ℝ) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := bnd_vals
  obtain ⟨w0, w1, w2, w3, w4, w5⟩ := circleW_vals
  obtain ⟨y0, y1, y2, y3, y4, y5⟩ := circleY_vals
  rw [constJ_eq, energyI_eq_sum]
  simp only [Fin.sum_univ_six, Fin.val_zero, Fin.val_one, Fin.val_two]
  have e3 : ((3 : Fin 6) : ℕ) + 1 = 4 := rfl
  have e4 : ((4 : Fin 6) : ℕ) + 1 = 5 := rfl
  have e5 : ((5 : Fin 6) : ℕ) + 1 = 6 := rfl
  have f3 : ((3 : Fin 6) : ℕ) = 3 := rfl
  have f4 : ((4 : Fin 6) : ℕ) = 4 := rfl
  have f5 : ((5 : Fin 6) : ℕ) = 5 := rfl
  simp only [e3, e4, e5, f3, f4, f5, zero_add, h0, h1, h2, h3, h4, h5, h6, w0, w1, w2, w3, w4, w5,
    y0, y1, y2, y3, y4, y5]
  ring

/-- `S = 43 log 7 - (7/2) I_explicit - π B - 12325/168`. -/
theorem surplusS_eq : surplusS = 43 * Real.log 7 - 7 / 2 * explicitI -
    π * (281603 / 156250 : ℝ) - 12325 / 168 := by
  unfold surplusS
  rw [explicitJ_eq]
  ring

/-- `log |D| = v₇(D) log 7 - aux(D)` from the exact product formula of the bridge. -/
theorem log_abs_eq {d : ℕ} {c : ℚ} (hD : actualCommonDeterminant d c ≠ 0)
    (hT : (tailMatrix d targetGerms (selectedTailRow d c (rationalGerms_fullRank c d))).det =
      (actualCommonDeterminant d c : ℚ_[7]))
    (hP : Real.log |(actualCommonDeterminant d c : ℝ)| +
      Real.log ‖(tailMatrix d targetGerms (selectedTailRow d c (rationalGerms_fullRank c d))).det‖ +
      auxiliary (actualCommonDeterminant d c) = 0) :
    Real.log |(actualCommonDeterminant d c : ℝ)| =
      (padicValRat 7 (actualCommonDeterminant d c) : ℝ) * Real.log 7 -
        auxiliary (actualCommonDeterminant d c) := by
  rw [hT, ← localTerm_eq_log_norm 7 _ hD, localTerm] at hP
  push_cast at hP
  linarith

/-- **Final contradiction, relative to the energy comparison.** -/
theorem final_contradiction_of_energy_le (hE : energyI ≤ explicitI) :
    ¬ Zeta7Partial.IsRationalSeven Zeta7Main.zeta7Three := by
  intro hq
  obtain ⟨c, _, hfam, hA⟩ := actual_annular_family_of_rationality hq
  obtain ⟨K, hK0, hK⟩ := hA (1 / 1000) (by norm_num) (by norm_num)
  obtain ⟨dP, hPd⟩ := Zeta7Auxiliary.actualAuxiliaryEstimate c (1 / 200) (by norm_num)
  obtain ⟨dC, hCd⟩ := c_theorem c (by norm_num : (0 : ℝ) < 1 / 200)
  have hS := surplusS_gt
  rw [surplusS_eq] at hS
  have hJ := constJ_eq_actual
  have hl7 := Zeta7Cert.log_seven_lt_two
  have hl70 : 0 < Real.log 7 := Real.log_pos (by norm_num)
  -- choose the degree
  set d : ℕ := max (max dP dC) (max 7 (⌈K * 2 / (1 / 50)⌉₊ + 1)) with hd
  have hdP : dP ≤ d := le_trans (le_max_left _ _) (le_max_left _ _)
  have hdC : dC ≤ d := le_trans (le_max_right _ _) (le_max_left _ _)
  have hd7 : 7 ≤ d := le_trans (le_max_left _ _) (le_max_right _ _)
  have hdK : ⌈K * 2 / (1 / 50)⌉₊ + 1 ≤ d := le_trans (le_max_right _ _) (le_max_right _ _)
  obtain ⟨hD, hT, hP⟩ := hfam d
  have hlog := log_abs_eq hD hT hP
  have hv := hK d hd7
  have haux := hPd d hdP
  have hC := hCd d hdC
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hd7)
  have hKd : K * 2 / (1 / 50) < d := by
    have := Nat.le_ceil (K * 2 / (1 / 50))
    have h2 : ((⌈K * 2 / (1 / 50)⌉₊ + 1 : ℕ) : ℝ) ≤ d := by exact_mod_cast hdK
    push_cast at h2
    linarith
  -- lower bound: log|D| ≥ ((43 - δ) d² - K d) log 7 - (12325/168 + ε) d²
  have hlow : ((43 - 1 / 1000) * (d : ℝ) ^ 2 - K * d) * Real.log 7 -
      (12325 / 168 + 1 / 200) * (d : ℝ) ^ 2 ≤ Real.log |(actualCommonDeterminant d c : ℝ)| := by
    rw [hlog]
    have := mul_le_mul_of_nonneg_right hv hl70.le
    linarith
  -- upper bound from C with J = 7I + πB and I ≤ I_explicit
  have hup : Real.log |(actualCommonDeterminant d c : ℝ)| ≤
      (7 / 2 * explicitI + π * (281603 / 156250 : ℝ) + 1 / 200) * (d : ℝ) ^ 2 := by
    refine hC.trans (mul_le_mul_of_nonneg_right ?_ (sq_nonneg _))
    rw [hJ]; linarith
  -- combine
  have hsq : 0 < (d : ℝ) ^ 2 := by positivity
  have hKlog : K * d * Real.log 7 ≤ K * d * 2 :=
    mul_le_mul_of_nonneg_left hl7.le (by positivity)
  have hKd' : K * d * 2 < 1 / 50 * (d : ℝ) ^ 2 := by
    rw [div_lt_iff₀ (by norm_num)] at hKd
    nlinarith
  have hkey : (223 / 6250 - 1 / 1000 * Real.log 7 - 2 * (1 / 200)) * (d : ℝ) ^ 2 ≤
      K * d * Real.log 7 := by nlinarith
  have hmargin : (1 / 50 : ℝ) < 223 / 6250 - 1 / 1000 * Real.log 7 - 2 * (1 / 200) := by
    linarith
  nlinarith

/-- **The same for `eta`**: `eta` is not the image of a rational number (zero included). -/
theorem eta_not_rational_of_energy_le (hE : energyI ≤ explicitI) :
    ∀ q : ℚ, (q : ℚ_[7]) ≠ Zeta7Main.eta := by
  intro q hq
  apply final_contradiction_of_energy_le hE
  refine ⟨2 * q, ?_⟩
  rw [Zeta7Main.eta] at hq
  push_cast
  rw [hq]
  ring

end Zeta7Final

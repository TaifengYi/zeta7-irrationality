import Zeta7Proof.CertEnergyPairs

/-! **Kernel-checked numerical margin.** For the explicit six-circle energies (48),

`S = 43 log 7 + (7/2) I - J - 12325/168 > 223/6250 = 0.03568`.

* `energyE_comm`: `E(y,t) = E(t,y)`.
* `explicitJ_eq`: `J = 7 I + π B` with `B = Σ (b_{i+1}² - b_i²) y_i = 281603/156250`.
* `explicitI_le`: `I ≤ π C_I` from the 36 pair bounds (upper bounds for every arccos term).
* `log_seven_gt`: `log 7 = 3 log 2 - log(8/7)`, with Mathlib's `log 2 > 0.6931471803` and the
  alternating logarithm series for `log(8/7)` with its remainder bound.
* `surplusS_gt`: the certified sign, using `π < 3.14159265358979323847`. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Zeta7Cert
open Real Finset

theorem mSet_comm (y t : ℚ) : mSet y t = mSet t y := by
  have h : ∀ m : ℕ, ((m : ℚ) ^ 2 * y * t < 1) = ((m : ℚ) ^ 2 * t * y < 1) := fun m => by
    rw [mul_right_comm]
  unfold mSet
  simp only [h, mul_comm y t]

theorem eTerm_comm (y t : ℚ) (m : ℕ) : eTerm y t m = eTerm t y m := by
  unfold eTerm
  rw [mul_comm ((y : ℚ) : ℝ) (t : ℝ), mul_right_comm ((m : ℝ) ^ 2) ((y : ℚ) : ℝ) (t : ℝ)]

theorem energyE_comm (y t : ℚ) : energyE y t = energyE t y := by
  unfold energyE
  rw [min_comm, mSet_comm]
  simp only [eTerm_comm y t]

theorem cb_vals : cb 0 = 0 ∧ cb 1 = 7 / 25 ∧ cb 2 = 21 / 25 ∧ cb 3 = 91 / 50 ∧ cb 4 = 301 / 100 ∧
    cb 5 = 469 / 100 ∧ cb 6 = 7 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [cb, Fin.sum_univ_six] <;> norm_num

/-- `J = 7 I + π B`. -/
theorem explicitJ_eq : explicitJ = 7 * explicitI + π * (281603 / 156250 : ℝ) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := cb_vals
  simp only [explicitJ, explicitI, Fin.sum_univ_six, Fin.val_zero, Fin.val_one, Fin.val_two]
  have e3 : ((3 : Fin 6) : ℕ) + 1 = 4 := rfl
  have e4 : ((4 : Fin 6) : ℕ) + 1 = 5 := rfl
  have e5 : ((5 : Fin 6) : ℕ) + 1 = 6 := rfl
  have f3 : ((3 : Fin 6) : ℕ) = 3 := rfl
  have f4 : ((4 : Fin 6) : ℕ) = 4 := rfl
  have f5 : ((5 : Fin 6) : ℕ) = 5 := rfl
  simp only [e3, e4, e5, f3, f4, f5, zero_add, h0, h1, h2, h3, h4, h5, h6, cwq_0, cwq_1, cwq_2,
    cwq_3, cwq_4, cwq_5, cy_0, cy_1, cy_2, cy_3, cy_4, cy_5]
  push_cast
  ring

/-- `I ≤ π C_I`. -/
theorem explicitI_le : explicitI ≤ π * (734244747828764079262909 / 1750000000000000000000000 : ℝ) := by
  simp only [explicitI, explicitW, Fin.sum_univ_six, cwq_0, cwq_1, cwq_2, cwq_3, cwq_4, cwq_5]
  push_cast
  have hpi := Real.pi_pos
  linarith [energyE_0_0, energyE_0_1, energyE_0_2, energyE_0_3, energyE_0_4, energyE_0_5, (energyE_comm (cy 1) (cy 0) ▸ energyE_0_1), energyE_1_1, energyE_1_2, energyE_1_3, energyE_1_4, energyE_1_5, (energyE_comm (cy 2) (cy 0) ▸ energyE_0_2), (energyE_comm (cy 2) (cy 1) ▸ energyE_1_2), energyE_2_2, energyE_2_3, energyE_2_4, energyE_2_5, (energyE_comm (cy 3) (cy 0) ▸ energyE_0_3), (energyE_comm (cy 3) (cy 1) ▸ energyE_1_3), (energyE_comm (cy 3) (cy 2) ▸ energyE_2_3), energyE_3_3, energyE_3_4, energyE_3_5, (energyE_comm (cy 4) (cy 0) ▸ energyE_0_4), (energyE_comm (cy 4) (cy 1) ▸ energyE_1_4), (energyE_comm (cy 4) (cy 2) ▸ energyE_2_4), (energyE_comm (cy 4) (cy 3) ▸ energyE_3_4), energyE_4_4, energyE_4_5, (energyE_comm (cy 5) (cy 0) ▸ energyE_0_5), (energyE_comm (cy 5) (cy 1) ▸ energyE_1_5), (energyE_comm (cy 5) (cy 2) ▸ energyE_2_5), (energyE_comm (cy 5) (cy 3) ▸ energyE_3_5), (energyE_comm (cy 5) (cy 4) ▸ energyE_4_5), energyE_5_5]

/-- `log 7 > 3 · 0.6931471803 - log87hi`. -/
theorem log_seven_gt : 3 * (0.6931471803 : ℝ) - (91379872583033219 / 684332506289223792 : ℝ) < Real.log 7 := by
  have h2 := Real.log_two_gt_d9
  have h := Real.abs_log_sub_add_sum_range_le (x := (-1 / 7 : ℝ)) (by norm_num) 16
  have h87 : Real.log (1 - (-1 / 7 : ℝ)) = 3 * Real.log 2 - Real.log 7 := by
    rw [show (1 : ℝ) - (-1 / 7) = 2 ^ 3 / 7 by norm_num, Real.log_div (by norm_num) (by norm_num),
      Real.log_pow]
    push_cast; ring
  rw [h87] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  rw [abs_le] at h
  linarith [h.1, h.2]

/-- **The certified surplus**: `S > 223/6250 = 0.03568`. -/
theorem surplusS_gt : (223 / 6250 : ℝ) < surplusS := by
  have hJ := explicitJ_eq
  have hI := explicitI_le
  have hL := log_seven_gt
  have hpi := Real.pi_lt_d20
  have hpi0 := Real.pi_pos
  unfold surplusS
  rw [hJ]
  nlinarith [mul_le_mul_of_nonneg_left hpi.le (by norm_num : (0 : ℝ) ≤ 7 / 2 * (734244747828764079262909 / 1750000000000000000000000) + 281603 / 156250)]

end Zeta7Cert

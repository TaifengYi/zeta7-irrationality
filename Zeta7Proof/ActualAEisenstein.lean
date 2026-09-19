import Zeta7Proof.ActualALogarithmicDerivative

/-! All-degree identification of the original logarithmic derivative with the
weight-two Eisenstein combination. These are equalities of formal series;
they assert neither modularity nor a level-seven vanishing bound. -/
set_option autoImplicit false
noncomputable section
open PowerSeries
namespace Zeta7Common
open Zeta7Main

theorem euler_inv (f : ℚ⟦X⟧) : euler f⁻¹ = -f⁻¹ ^ 2 * euler f := by
  simp only [euler, derivative_inv']
  ring

theorem euler_pow (f : ℚ⟦X⟧) (n : ℕ) :
    euler (f ^ n) = n * f ^ (n - 1) * euler f := by
  simp only [euler, derivative_pow]
  ring

theorem sevenEulerProduct_inv_euler :
    euler sevenEulerProduct⁻¹ = sevenEulerProduct⁻¹ * sevenSigmaOneSeries := by
  rw [euler_inv, sevenEulerProduct_euler]
  have h : sevenEulerProduct * sevenEulerProduct⁻¹ = 1 :=
    PowerSeries.mul_inv_cancel _ (by rw [sevenEulerProduct_constant]; norm_num)
  linear_combination sevenEulerProduct⁻¹ * sevenSigmaOneSeries * h

theorem xUnit_euler : euler xUnit = 4 * xUnit * sevenSigmaOneSeries := by
  rw [xUnit, euler_pow, sevenEulerProduct_inv_euler]
  norm_num
  ring

/-- The actual product-defined A, as a complete Lambert series. -/
theorem ASeries_lambert : ASeries = 1 + C (4 : ℚ) * sevenSigmaOneSeries := by
  change 1 + euler xUnit * xUnit⁻¹ = _
  rw [xUnit_euler, map_ofNat]
  have h : xUnit * xUnit⁻¹ = 1 :=
    PowerSeries.mul_inv_cancel _ (by rw [xUnit_constant]; norm_num)
  linear_combination 4 * sevenSigmaOneSeries * h

theorem ASeries_coeff (n : ℕ) :
    coeff n ASeries = (if n = 0 then 1 else 0) +
      4 * ∑ a ∈ n.divisors.filter (fun a => ¬ 7 ∣ a), (a : ℚ) := by
  simp [ASeries_lambert, sevenSigmaOneSeries, sevenSigmaOne, coeff_one]

def sigmaOne (n : ℕ) : ℚ := ∑ d ∈ n.divisors, (d : ℚ)
def eisensteinTwoQ : ℚ⟦X⟧ := 1 - C (24 : ℚ) * mk sigmaOne

theorem seven_sigmaOne_multiples (n : ℕ) (h7 : 7 ∣ n) :
    ∑ d ∈ n.divisors.filter (fun d => 7 ∣ d), (d : ℚ) =
      7 * sigmaOne (n / 7) := by
  classical
  by_cases hn : n = 0
  · subst n; simp [sigmaOne]
  have hn7 : n / 7 ≠ 0 := Nat.ne_of_gt
    (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) h7) (by decide))
  rw [sigmaOne, Finset.mul_sum]
  symm
  apply Finset.sum_bij (fun d _ => 7 * d)
  · intro d hd
    apply Finset.mem_filter.mpr
    exact ⟨Nat.mem_divisors.mpr
      ⟨(Nat.dvd_div_iff_mul_dvd h7).mp (Nat.dvd_of_mem_divisors hd), hn⟩,
      dvd_mul_right 7 d⟩
  · intro a ha b hb hab
    omega
  · intro d hd
    obtain ⟨hd, h7d⟩ := Finset.mem_filter.mp hd
    refine ⟨d / 7, Nat.mem_divisors.mpr ⟨?_, hn7⟩, Nat.mul_div_cancel' h7d⟩
    exact (Nat.div_dvd_div_iff_right h7d h7).mpr (Nat.dvd_of_mem_divisors hd)
  · intro d hd
    simp

theorem sevenSigmaOne_eq (n : ℕ) :
    sevenSigmaOne n = sigmaOne n - if 7 ∣ n then 7 * sigmaOne (n / 7) else 0 := by
  classical
  have h := Finset.sum_filter_add_sum_filter_not n.divisors
    (fun d => 7 ∣ d) (fun d => (d : ℚ))
  by_cases h7 : 7 ∣ n
  · rw [if_pos h7, seven_sigmaOne_multiples n h7] at *
    unfold sigmaOne sevenSigmaOne at *
    linear_combination h
  · rw [if_neg h7, sub_zero]
    have he : n.divisors.filter (fun d => 7 ∣ d) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro d hd
      exact h7 ((Finset.mem_filter.mp hd).2.trans
        (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1))
    simpa [he, sigmaOne, sevenSigmaOne] using h

/-- The weight-two normalization, proved for every coefficient of the original
product-defined A. The factor 6 is cleared. -/
theorem ASeries_eisensteinTwo :
    C (6 : ℚ) * ASeries =
      C (7 : ℚ) * (expand 7 (by decide)) eisensteinTwoQ - eisensteinTwoQ := by
  ext n
  rw [coeff_C_mul, ASeries_lambert]
  simp only [eisensteinTwoQ, map_sub, map_add, coeff_C_mul, coeff_mk,
    sevenSigmaOneSeries, coeff_expand, sevenSigmaOne_eq]
  by_cases h7 : 7 ∣ n
  · rw [if_pos h7]
    have hz : n = 0 ↔ n / 7 = 0 := by
      constructor
      · intro h; simp [h]
      · intro h
        have := Nat.div_mul_cancel h7
        rw [h] at this
        omega
    simp only [coeff_one, hz, h7, ite_true]
    ring
  · rw [if_neg h7]
    have hn : n ≠ 0 := by intro h; subst n; exact h7 (dvd_zero 7)
    simp [coeff_one, hn, h7]
    ring

end Zeta7Common

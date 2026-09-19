import Zeta7Proof.CommonRationalGerms

/-! Exact divisor reindexing for the third Euler derivative of the actual G.
The Eisenstein series here is defined by its full rational q-expansion;
its modular quotient identity is a separate obligation. -/
set_option autoImplicit false
noncomputable section
open PowerSeries
namespace Zeta7Common
open Zeta7Main

def sigmaThree (n : ℕ) : ℚ := ∑ d ∈ n.divisors, (d : ℚ) ^ 3

def eisensteinFourQ : ℚ⟦X⟧ := 1 + C 240 * mk sigmaThree

theorem GSeries_euler_three_coeff (n : ℕ) :
    coeff n (euler (euler (euler GSeries))) =
      ∑ a ∈ n.divisors.filter (fun a => ¬ 7 ∣ a), ((n / a : ℕ) : ℚ) ^ 3 := by
  simp only [euler_coeff, GSeries_coeff, ← mul_assoc, ← pow_succ', ← pow_two]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  have hd := Nat.mem_divisors.mp (Finset.mem_filter.mp ha).1
  have ha0 : (a : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_zero_of_dvd_ne_zero hd.2 hd.1)
  rw [Nat.cast_div hd.1 ha0, div_pow, div_eq_mul_inv]

theorem GSeries_euler_three_coeff_reindex (n : ℕ) :
    coeff n (euler (euler (euler GSeries))) =
      ∑ d ∈ n.divisors.filter (fun d => ¬ 7 ∣ n / d), (d : ℚ) ^ 3 := by
  rw [GSeries_euler_three_coeff, Finset.sum_filter, Finset.sum_filter]
  calc
    _ = ∑ a ∈ n.divisors,
        (if ¬ 7 ∣ n / (n / a) then ((n / a : ℕ) : ℚ) ^ 3 else 0) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Nat.div_div_self (Nat.dvd_of_mem_divisors ha) (Nat.ne_zero_of_mem_divisors ha)]
    _ = _ := Nat.sum_div_divisors n (fun a => if ¬ 7 ∣ n / a then (a : ℚ) ^ 3 else 0)

theorem seven_divisor_filter (n : ℕ) (h7 : 7 ∣ n) :
    n.divisors.filter (fun d => 7 ∣ n / d) = (n / 7).divisors := by
  by_cases hn : n = 0
  · subst n; simp
  have hn7 : n / 7 ≠ 0 := Nat.ne_of_gt
    (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) h7) (by decide))
  ext d
  simp only [Finset.mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hd, _⟩, h⟩
    exact ⟨(Nat.dvd_div_iff_mul_dvd h7).mpr
      (by simpa [mul_comm] using (Nat.dvd_div_iff_mul_dvd hd).mp h), hn7⟩
  · rintro ⟨hd, _⟩
    have hd' : d ∣ n := hd.trans (Nat.div_dvd_of_dvd h7)
    exact ⟨⟨hd', hn⟩, (Nat.dvd_div_iff_mul_dvd hd').mpr
      (by simpa [mul_comm] using (Nat.dvd_div_iff_mul_dvd h7).mp hd)⟩

/-- All degrees, including zero and indices divisible by arbitrarily high powers of seven. -/
theorem GSeries_euler_three_sigma (n : ℕ) :
    coeff n (euler (euler (euler GSeries))) =
      sigmaThree n - if 7 ∣ n then sigmaThree (n / 7) else 0 := by
  rw [GSeries_euler_three_coeff_reindex]
  have hs := Finset.sum_filter_add_sum_filter_not n.divisors
    (fun d => 7 ∣ n / d) (fun d => (d : ℚ) ^ 3)
  by_cases h7 : 7 ∣ n
  · rw [if_pos h7, seven_divisor_filter n h7] at *
    unfold sigmaThree
    linear_combination hs
  · rw [if_neg h7, sub_zero]
    have hempty : n.divisors.filter (fun d => 7 ∣ n / d) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro d hd
      exact h7 ((Finset.mem_filter.mp hd).2.trans
        (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1)))
    simpa [hempty, sigmaThree] using hs

/-- The exact Lambert forcing identity θ³G=(E₄(q)−E₄(q⁷))/240. -/
theorem GSeries_euler_three_eisenstein :
    C (240 : ℚ) * euler (euler (euler GSeries)) =
      eisensteinFourQ - (expand 7 (by decide)) eisensteinFourQ := by
  ext n
  rw [coeff_C_mul, GSeries_euler_three_sigma]
  simp only [eisensteinFourQ, map_sub, map_add, coeff_C_mul, coeff_mk,
    coeff_expand]
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

end Zeta7Common

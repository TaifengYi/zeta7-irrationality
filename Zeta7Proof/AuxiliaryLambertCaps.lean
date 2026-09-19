import Zeta7Proof.AuxiliaryCaps

/-! Unconditional caps for the original Lambert series, before coordinate transport. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
namespace Zeta7Auxiliary
open PowerSeries Zeta7Main
variable {p : ℕ} [Fact p.Prime]

theorem integral_nat_inv {a : ℕ} (ha : ¬ p ∣ a) : Integral ((a : ℚ_[p])⁻¹) := by
  change ‖(a : ℚ_[p])⁻¹‖ ≤ 1
  rw [norm_inv, Padic.norm_natCast_eq_one_iff.mpr
    ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr ha)]
  norm_num

theorem integral_prime_div_nat {a : ℕ} (ha : a ≠ 0) (hap : a < p ^ 2) :
    Integral ((p : ℚ_[p]) / (a : ℚ_[p])) := by
  by_cases hpa : p ∣ a
  · obtain ⟨b, rfl⟩ := hpa
    have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
    have hb0 : b ≠ 0 := by aesop
    have hbp : b < p := by nlinarith [Nat.pos_of_ne_zero hp0]
    have hpnb : ¬ p ∣ b := Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hb0) hbp
    have hpQ : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp0
    have he : (p : ℚ_[p]) / (p * b) = (b : ℚ_[p])⁻¹ := by
      simp [div_mul_eq_div_div, hpQ]
    simpa only [Nat.cast_mul, he] using (integral_nat_inv (p := p) hpnb)
  · exact (integral_nat p).mul (integral_nat_inv hpa)

theorem lambert_integral_below_prime (n : ℕ) (hn : n < p) :
    Integral ((coeff n GSeries : ℚ) : ℚ_[p]) := by
  rw [GSeries_coeff]
  push_cast
  apply integral_sum
  intro a ha
  have hd := Nat.mem_divisors.mp (Finset.mem_filter.mp ha).1
  have ha0 := ne_zero_of_dvd_ne_zero hd.2 hd.1
  have han := Nat.le_of_dvd (Nat.pos_of_ne_zero hd.2) hd.1
  have hpa := Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero ha0) (han.trans_lt hn)
  simpa only [inv_pow] using (integral_nat_inv (p := p) hpa).pow 3

theorem lambert_cap_three (N : ℕ) (hN : N ≤ p ^ 2) :
    Cap N 3 (GSeries.map (algebraMap ℚ ℚ_[p])) := by
  intro n hn
  rw [coeff_map, GSeries_coeff]
  simp only [map_sum, map_inv₀, map_pow, map_natCast, Finset.mul_sum]
  apply integral_sum
  intro a ha
  have hd := Nat.mem_divisors.mp (Finset.mem_filter.mp ha).1
  have ha0 := ne_zero_of_dvd_ne_zero hd.2 hd.1
  have han := Nat.le_of_dvd (Nat.pos_of_ne_zero hd.2) hd.1
  have hh := (integral_prime_div_nat (p := p) ha0 (han.trans_lt (hn.trans_le hN))).pow 3
  simpa only [div_pow, div_eq_mul_inv, mul_pow, inv_pow] using hh

theorem lambert_cap_zero : Cap p 0 (GSeries.map (algebraMap ℚ ℚ_[p])) := by
  intro n hn
  rw [pow_zero, one_mul, coeff_map]
  change Integral ((coeff n GSeries : ℚ) : ℚ_[p])
  exact lambert_integral_below_prime (p := p) n hn

end Zeta7Auxiliary

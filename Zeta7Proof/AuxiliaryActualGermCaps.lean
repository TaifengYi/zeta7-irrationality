import Zeta7Proof.AuxiliaryTransportCaps
import Zeta7Proof.ActualLH

/-! Actual low-row integrality and the cap-four cancellation for K, using DK = RH. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
namespace Zeta7Auxiliary
open PowerSeries Zeta7Main Zeta7Common
variable {p : ℕ} [Fact p.Prime]

theorem IntegerSeries.natCast (n : ℕ) : IntegerSeries (n : PowerSeries ℚ) :=
  ⟨n, by simp⟩

theorem rationalForcing_integer : IntegerSeries rationalForcing := by
  have hP : IntegerSeries (1 + 13 * X + 49 * X ^ 2 : PowerSeries ℚ) :=
    (IntegerSeries.one.add ((IntegerSeries.natCast 13).mul IntegerSeries.X)).add
      ((IntegerSeries.natCast 49).mul (IntegerSeries.X.pow 2))
  exact (IntegerSeries.X.mul (IntegerSeries.one.add
    ((IntegerSeries.natCast 10).mul IntegerSeries.X))).mul (hP.inv (by simp))

theorem rationalK_constant (c : ℚ) : constantCoeff (quadratic rationalPotential (rationalH c)) = 0 := by
  simp [quadratic, euler, rationalPotential]

theorem cap_of_euler {N e : ℕ} {F : PowerSeries ℚ_[p]} (hN : N ≤ p ^ 2)
    (h0 : constantCoeff F = 0) (hF : Cap N e (euler F)) : Cap N (e + 1) F := by
  intro n hn
  by_cases hn0 : n = 0
  · subst n
    simpa only [coeff_zero_eq_constantCoeff, h0, mul_zero] using (integral_zero (p := p))
  · have hnQ : (n : ℚ_[p]) ≠ 0 := by exact_mod_cast hn0
    have hh := (integral_prime_div_nat (p := p) hn0 (hn.trans_le hN)).mul (hF n hn)
    rw [euler_coeff] at hh
    convert hh using 1 <;> field_simp <;> ring

theorem cap_zero_of_euler {F : PowerSeries ℚ_[p]} (h0 : constantCoeff F = 0)
    (hF : Cap p 0 (euler F)) : Cap p 0 F := by
  intro n hn
  by_cases hn0 : n = 0
  · subst n
    simpa only [coeff_zero_eq_constantCoeff, h0, mul_zero] using (integral_zero (p := p))
  · have hnQ : (n : ℚ_[p]) ≠ 0 := by exact_mod_cast hn0
    have hi := integral_nat_inv (p := p) (Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hn0) hn)
    have hh := hi.mul (hF n hn)
    rw [euler_coeff] at hh
    convert hh using 1 <;> field_simp <;> ring

theorem Cap.primitive_zero {F : PowerSeries ℚ_[p]} (hF : Cap p 0 F) :
    Cap p 0 (primitive F) := by
  intro n hn
  simp only [primitive, coeff_mk]
  split_ifs with hn0
  · simpa using (integral_zero (p := p))
  · have hi := integral_nat_inv (p := p) (Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hn0) hn)
    simpa only [div_eq_mul_inv, mul_assoc] using (hF (n - 1) (by omega)).mul hi

theorem rationalK_cap_four (c : ℚ) (hc : ¬ p ∣ c.den) (N : ℕ) (hN : N ≤ p ^ 2) :
    Cap N 4 ((quadratic rationalPotential (rationalH c)).map (algebraMap ℚ ℚ_[p])) := by
  apply cap_of_euler hN
  · change (algebraMap ℚ ℚ_[p]) (constantCoeff (quadratic rationalPotential (rationalH c))) = 0
    rw [rationalK_constant, map_zero]
  · rw [← map_euler, rationalH_quadratic_derivative, map_mul]
    simpa only [Nat.zero_add] using
      (rationalForcing_integer.cap_zero N).mul (rationalH_cap_three c hc N hN)

theorem rationalK_cap_zero (c : ℚ) (hc : ¬ p ∣ c.den) :
    Cap p 0 ((quadratic rationalPotential (rationalH c)).map (algebraMap ℚ ℚ_[p])) := by
  apply cap_zero_of_euler
  · change (algebraMap ℚ ℚ_[p]) (constantCoeff (quadratic rationalPotential (rationalH c))) = 0
    rw [rationalK_constant, map_zero]
  · rw [← map_euler, rationalH_quadratic_derivative, map_mul]
    simpa only [Nat.zero_add] using
      (rationalForcing_integer.cap_zero p).mul (rationalH_cap_zero c hc)

theorem actual_germs_cap_zero (c : ℚ) (hc : ¬ p ∣ c.den) (j : Fin 6) :
    Cap p 0 ((rationalGerms c j).map (algebraMap ℚ ℚ_[p])) := by
  have hH := rationalH_cap_zero c hc
  have hK := rationalK_cap_zero c hc
  fin_cases j
  · simpa [rationalGerms, germs] using hH
  · simpa [rationalGerms, germs, map_euler] using hH.euler
  · simpa [rationalGerms, germs, map_euler] using hH.euler.euler
  · simpa [rationalGerms, germs] using hK
  · simpa [rationalGerms, germs, map_primitive] using hK.primitive_zero
  · simpa [rationalGerms, germs, map_primitive] using hK.primitive_zero.primitive_zero

end Zeta7Auxiliary

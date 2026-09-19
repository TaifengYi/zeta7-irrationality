import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
import Mathlib.NumberTheory.Padics.PadicIntegers

/-! P1: the all-degree congruence for the actual normalized level-one Eisenstein
q-expansion. This is not the level-seven Hasse quotient or a determinant bound. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
namespace Zeta7Auxiliary
open scoped ArithmeticFunction.sigma

def eisensteinCoefficient (k n : ℕ) : ℚ :=
  if n = 0 then 1 else -(2 * k / bernoulli k) * (ArithmeticFunction.sigma (k - 1) n)

def eisensteinSeries (k : ℕ) : PowerSeries ℚ := PowerSeries.mk (eisensteinCoefficient k)

theorem eisensteinSeries_complex (k : ℕ) (hk : 3 ≤ k) (hk2 : Even k) :
    (eisensteinSeries k).map (algebraMap ℚ ℂ) =
      UpperHalfPlane.qExpansion 1 (ModularForm.E hk) := by
  ext n
  rw [PowerSeries.coeff_map, EisensteinSeries.E_qExpansion_coeff hk hk2]
  simp only [eisensteinSeries, PowerSeries.coeff_mk, eisensteinCoefficient]
  split_ifs <;> simp

variable (p : ℕ) [Fact p.Prime]

theorem bernoulli_predecessor_valuation (hp : 3 ≤ p) :
    padicValRat p (bernoulli (p - 1)) = -1 := by
  have he := (Fact.out : p.Prime).even_sub_one (by omega)
  obtain ⟨k, hk⟩ := he
  have hk' : p - 1 = 2 * k := by omega
  rw [hk']
  exact Bernoulli.padicValRat_bernoulli (by omega) (by rw [← hk'])

theorem bernoulli_predecessor_norm (hp : 3 ≤ p) :
    ‖(bernoulli (p - 1) : ℚ_[p])‖ = p := by
  have hv := bernoulli_predecessor_valuation p hp
  have hb : bernoulli (p - 1) ≠ 0 := by
    intro h; rw [h, padicValRat.zero] at hv; norm_num at hv
  have hbp : (bernoulli (p - 1) : ℚ_[p]) ≠ 0 := by exact_mod_cast hb
  rw [Padic.norm_eq_zpow_neg_valuation hbp, Padic.valuation_ratCast, hv]
  norm_num

theorem eisensteinCoefficient_congruence (hp : 3 ≤ p) (n : ℕ) (hn : n ≠ 0) :
    ‖(eisensteinCoefficient (p - 1) n : ℚ_[p])‖ ≤ (p : ℝ)⁻¹ := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hn1 : ‖((2 * (p - 1) : ℕ) : ℚ_[p])‖ ≤ 1 := by
    simpa only [Int.cast_natCast] using Padic.norm_int_le_one (p := p) (2 * (p - 1) : ℕ)
  have hn2 : ‖((ArithmeticFunction.sigma (p - 2) n : ℕ) : ℚ_[p])‖ ≤ 1 := by
    simpa only [Int.cast_natCast] using
      Padic.norm_int_le_one (p := p) (ArithmeticFunction.sigma (p - 2) n : ℕ)
  simp only [eisensteinCoefficient, if_neg hn, Rat.cast_mul, Rat.cast_neg, Rat.cast_div,
    Rat.cast_natCast, Rat.cast_ofNat, norm_mul, norm_neg, norm_div]
  rw [bernoulli_predecessor_norm p hp]
  have hnum' : ‖(2 : ℚ_[p])‖ * ‖((p - 1 : ℕ) : ℚ_[p])‖ ≤ 1 := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat, norm_mul] using hn1
  have hs : p - 1 - 1 = p - 2 := by omega
  rw [hs]
  calc
    _ ≤ (1 / (p : ℝ)) * 1 :=
      mul_le_mul (div_le_div_of_nonneg_right hnum' hp0.le) hn2 (norm_nonneg _)
        (by positivity)
    _ = _ := by simp [one_div]

/-- Complete coefficientwise E_(p-1) = 1 mod p, with an integral quotient.
The preceding complex identification links this series to the actual modular form. -/
theorem eisensteinSeries_congruence (hp : 3 ≤ p) :
    ∃ F : PowerSeries ℤ_[p],
      (eisensteinSeries (p - 1)).map (algebraMap ℚ ℚ_[p]) =
        1 + PowerSeries.C (p : ℚ_[p]) * F.map (algebraMap ℤ_[p] ℚ_[p]) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hpq : (p : ℚ_[p]) ≠ 0 := by
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  let f : ℕ → ℚ_[p] := fun n =>
    ((eisensteinCoefficient (p - 1) n : ℚ_[p]) - if n = 0 then 1 else 0) / p
  have hf (n : ℕ) : ‖f n‖ ≤ 1 := by
    by_cases hn : n = 0
    · simp [f, eisensteinCoefficient, hn]
    · dsimp [f]
      rw [if_neg hn, sub_zero, norm_div, Padic.norm_p,
        div_le_one (inv_pos.mpr hp0)]
      exact eisensteinCoefficient_congruence p hp n hn
  refine ⟨PowerSeries.mk (fun n => (⟨f n, hf n⟩ : ℤ_[p])), ?_⟩
  ext n
  simp only [PowerSeries.coeff_map, eisensteinSeries, PowerSeries.coeff_mk,
    map_add, PowerSeries.coeff_one, PowerSeries.coeff_C_mul,
    PadicInt.algebraMap_apply]
  change (eisensteinCoefficient (p - 1) n : ℚ_[p]) =
    (if n = 0 then 1 else 0) + (p : ℚ_[p]) * f n
  dsimp [f]
  field_simp
  ring

end Zeta7Auxiliary

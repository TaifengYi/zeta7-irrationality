import Zeta7Proof.AnnularProgressionValuation
import Zeta7Proof.SevenAdicSeriesEvaluation
import Mathlib.Analysis.SpecificLimits.Normed

/-! The all-degree logarithmic estimate and convergence for the actual A1
Pochhammer coefficients. Neither this estimate nor its convergence uses radius49. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
open PowerSeries Filter Topology
namespace Zeta7Annulus
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

theorem annularHypergeometricCoefficient_log_bound (i : Fin 2) (n : ℕ) (hn : 0 < n) :
    -(Nat.log 7 (12 * n) : ℤ) ≤ padicValRat 7 (annularHypergeometricCoefficient i n) := by
  have hnum := hypergeometricNumerator_valuation_lower i n
  have hden := double_factorial_valuation_deficit i n hn
  rw [annularHypergeometricCoefficient_factorial]
  have hN : (hypergeometricNumerator i n : ℚ) ≠ 0 := by
    exact_mod_cast ne_of_gt (hypergeometricNumerator_pos i n)
  have hF : ((2 * n + i.val).factorial : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero _
  have h36 : padicValRat 7 (36 : ℚ) = 0 := by
    have h := padicValRat.of_nat (p := 7) (n := 36)
    norm_num only [Nat.cast_ofNat, padicValNat.eq_zero_of_not_dvd (by decide : ¬ 7 ∣ 36)] at h
    exact h
  rw [padicValRat.div hN (mul_ne_zero (pow_ne_zero _ (by norm_num)) hF),
    padicValRat.mul (pow_ne_zero _ (by norm_num)) hF, padicValRat.pow, h36]
  simp only [mul_zero, zero_add, padicValRat.of_nat]
  omega

theorem annularHypergeometricA_log_bound (n : ℕ) (hn : 0 < n) :
    -(Nat.log 7 (12 * n) : ℤ) ≤ padicValRat 7 (coeff n annularHypergeometricA) := by
  simpa [annularHypergeometricA, hypergeometricTaylor, annularHypergeometricCoefficient]
    using annularHypergeometricCoefficient_log_bound 0 n hn

theorem annularHypergeometricC_log_bound (n : ℕ) (hn : 0 < n) :
    -(Nat.log 7 (12 * n) : ℤ) ≤ padicValRat 7 (coeff n annularHypergeometricC) := by
  have h := annularHypergeometricCoefficient_log_bound 1 n hn
  norm_num [annularHypergeometricCoefficient] at h
  simpa only [annularHypergeometricC, hypergeometricTaylor, coeff_mk] using h

theorem annularHypergeometricCoefficient_norm_bound (i : Fin 2) (n : ℕ) (hn : 0 < n) :
    ‖(annularHypergeometricCoefficient i n : ℚ_[7])‖ ≤ 12 * (n : ℝ) := by
  have hv := annularHypergeometricCoefficient_log_bound i n hn
  have hb := Zeta7Section3.norm_bound_of_valuation
    (annularHypergeometricCoefficient i n : ℚ_[7]) (-(Nat.log 7 (12 * n) : ℝ)) (by
      intro _
      rw [Padic.valuation_ratCast]
      exact_mod_cast hv)
  simp only [neg_neg, Real.rpow_natCast] at hb
  apply hb.trans
  exact_mod_cast Nat.pow_log_le_self 7 (by omega : 12 * n ≠ 0)

def annularHypergeometricPadic (i : Fin 2) : ℚ_[7]⟦X⟧ :=
  mk (fun n => (annularHypergeometricCoefficient i n : ℚ_[7]))

theorem annularHypergeometricPadic_zero :
    annularHypergeometricPadic 0 = annularHypergeometricA.map (algebraMap ℚ ℚ_[7]) := by
  ext n
  simp [annularHypergeometricPadic, annularHypergeometricCoefficient,
    annularHypergeometricA, hypergeometricTaylor]

theorem annularHypergeometricPadic_one :
    annularHypergeometricPadic 1 = annularHypergeometricC.map (algebraMap ℚ ℚ_[7]) := by
  ext n
  norm_num [annularHypergeometricPadic, annularHypergeometricCoefficient,
    annularHypergeometricC, hypergeometricTaylor]

theorem annularHypergeometricPadic_restricted (i : Fin 2) (r : ℝ)
    (hr : 0 ≤ r) (hr1 : r < 1) : IsRestricted r (annularHypergeometricPadic i) := by
  rw [isRestricted_iff']
  have ht := (tendsto_self_mul_const_pow_of_lt_one hr hr1).const_mul (12 : ℝ)
  apply squeeze_zero' (Eventually.of_forall (fun n =>
    mul_nonneg (norm_nonneg _) (pow_nonneg hr n))) ?_ (by simpa using ht)
  filter_upwards [eventually_gt_atTop 0] with n hn
  simp only [annularHypergeometricPadic, coeff_mk]
  calc
    _ ≤ (12 * (n : ℝ)) * r ^ n := mul_le_mul_of_nonneg_right
      (annularHypergeometricCoefficient_norm_bound i n hn) (pow_nonneg hr n)
    _ = _ := by ring

theorem square_le_seven_pow (J : ℕ) : J ^ 2 ≤ 7 ^ J := by
  induction J with
  | zero => norm_num
  | succ J ih =>
      change (J + 1) ^ 2 ≤ 7 ^ J * 7
      by_cases hJ : J = 0
      · subst J; norm_num
      · have hj : 1 ≤ J := by omega
        nlinarith

theorem logarithmic_substitution_bound (n : ℕ) (hn : 0 < n) (m : ℝ) (hm : 0 < m) :
    -3 / m ≤ m * (n : ℝ) - Nat.log 7 (12 * n) := by
  have hsq : ((Nat.log 7 (12 * n) : ℕ) : ℝ) ^ 2 ≤ 12 * (n : ℝ) := by
    exact_mod_cast (square_le_seven_pow _).trans
      (Nat.pow_log_le_self 7 (by omega : 12 * n ≠ 0))
  have hh := sq_nonneg (m * (Nat.log 7 (12 * n) : ℝ) - 6)
  have hmul := mul_le_mul_of_nonneg_left hsq (sq_nonneg m)
  apply (div_le_iff₀ hm).mpr
  nlinarith

theorem annularHypergeometricCoefficient_quantitative (i : Fin 2) (n : ℕ)
    (hn : 0 < n) (m : ℝ) (hm : 0 < m) :
    -3 / m ≤ (padicValRat 7 (annularHypergeometricCoefficient i n) : ℝ) + m * n := by
  have hv : -(Nat.log 7 (12 * n) : ℝ) ≤
      (padicValRat 7 (annularHypergeometricCoefficient i n) : ℝ) := by
    exact_mod_cast annularHypergeometricCoefficient_log_bound i n hn
  have h := logarithmic_substitution_bound n hn m hm
  linarith

end Zeta7Annulus

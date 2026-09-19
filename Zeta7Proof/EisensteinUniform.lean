/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
import Zeta7Proof.EisensteinLimit
import Zeta7Proof.UniformPowerSeries
import Mathlib.NumberTheory.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Topology.Instances.ZMod

/-! Uniform approximation of the existing, independently evaluated target
by full level-one Eisenstein q-expansions. The integral congruence and the
ultrametric finite-sum bound are uniform in the divisor and coefficient index.
All constants refer to the preserved Kubota--Leopoldt construction. -/

set_option autoImplicit false
namespace Zeta7Main
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩
open Filter Topology PowerSeries PadicLFunctions

/-- The requested sequence includes weight four at index zero. -/
def serreWeight (r : ℕ) : ℕ := 6 * 7 ^ r - 2

theorem serreWeight_succ (r : ℕ) : serreWeight (r + 1) = interpolationWeight r := rfl

theorem serreWeight_ge_four (r : ℕ) : 4 ≤ serreWeight r := by
  have h : 0 < 7 ^ r := pow_pos (by decide) _
  unfold serreWeight
  omega

theorem serreWeight_branch (r : ℕ) : (serreWeight r : ZMod 6) = 4 := by
  have h : 0 < 7 ^ r := pow_pos (by decide) _
  rw [serreWeight, Nat.cast_sub (by omega)]
  push_cast
  rw [show (6 : ZMod 6) = 0 from by decide, zero_mul]
  decide

theorem serreWeight_even (r : ℕ) : Even (serreWeight r) := by
  have h := (ZMod.natCast_eq_natCast_iff (serreWeight r) 4 6).mp (serreWeight_branch r)
  change serreWeight r % 6 = 4 % 6 at h
  rw [Nat.even_iff]
  omega

theorem serreWeight_exponent_ge (r : ℕ) : r + 1 ≤ serreWeight r - 1 := by
  have h : r + 1 ≤ 7 ^ r := by
    induction r with
    | zero => norm_num
    | succ r ih => rw [pow_succ]; nlinarith
  unfold serreWeight
  omega

theorem serreWeight_tendsto :
    Tendsto (fun r => (serreWeight r : ℤ_[7])) atTop (𝓝 (-2)) := by
  apply (tendsto_add_atTop_iff_nat 1).mp
  have h := (tendsto_const_nhds (x := (1 : ℤ_[7]))).sub interpolationArgument_tendsto
  convert h using 1
  · funext r
    rw [serreWeight_succ]
    ring
  · norm_num

/-- Standard weight-space coordinates: residue component and principal weight. -/
theorem serreWeight_weightSpace_tendsto :
    Tendsto (fun r => ((serreWeight r : ZMod 6), (serreWeight r : ℤ_[7])))
      atTop (𝓝 (4, -2)) := by
  simpa only [serreWeight_branch] using
    (tendsto_const_nhds (x := (4 : ZMod 6))).prodMk_nhds serreWeight_tendsto

/-- The weight coordinates agree with the constructed inverse-square character. -/
theorem serreWeight_characters_tendsto (x : ℤ_[7]ˣ) :
    Tendsto (fun r => (((x : ℤ_[7]) : ℚ_[7]) ^ serreWeight r)) atTop
      (𝓝 (((((x : ℤ_[7]) : ℚ_[7]) ^ 2))⁻¹)) := by
  have hc : Continuous (fun s : ℤ_[7] => ((branchChar 7 4 s x : ℤ_[7]) : ℚ_[7])) :=
    continuous_subtype_val.comp
      (continuous_const.mul (PadicInt.continuous_onePAdicPow 7 _ _))
  have h := hc.continuousAt.tendsto.comp serreWeight_tendsto
  rw [branch_four_neg_two_eq_inv_square] at h
  convert h using 1
  funext r
  simp only [Function.comp_apply]
  rw [branchChar_natCast 7 (serreWeight_branch r)]
  simp [PadicMeasure.unitsPowCM]

/-- Full classical coefficients, with NO Euler factor in degree zero. -/
noncomputable def fullEisensteinCoeff (k n : ℕ) : ℚ :=
  if n = 0 then zetaNeg (k - 1) / 2 else ∑ d ∈ n.divisors, (d : ℚ) ^ (k - 1)

noncomputable def classicalRationalSeries (r : ℕ) : ℚ⟦X⟧ :=
  mk (fullEisensteinCoeff (serreWeight r))

noncomputable def classicalEisensteinSeries (r : ℕ) : ℚ_[7]⟦X⟧ :=
  (classicalRationalSeries r).map (algebraMap ℚ ℚ_[7])

theorem classicalEisensteinSeries_coeff (r n : ℕ) :
    coeff n (classicalEisensteinSeries r) = (fullEisensteinCoeff (serreWeight r) n : ℚ_[7]) := by
  simp [classicalEisensteinSeries, classicalRationalSeries]

/-- Fermat followed by lifting the congruence, in the ordinary integer ring. -/
theorem seven_unit_power_dvd {d : ℕ} (hd : ¬ 7 ∣ d) (r : ℕ) :
    (7 : ℤ) ^ (r + 1) ∣ (d : ℤ) ^ (6 * 7 ^ r) - 1 := by
  have hc : IsCoprime (d : ℤ) 7 := by
    exact_mod_cast ((Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 7)).mpr hd).symm
  have h : (7 : ℤ) ∣ (d : ℤ) ^ 6 - 1 := Int.prime_dvd_pow_sub_one (by decide) hc
  simpa only [one_pow, ← pow_mul, Nat.cast_ofNat] using dvd_sub_pow_of_dvd_sub h r

theorem seven_unit_power_norm {d : ℕ} (hd : ¬ 7 ∣ d) (r : ℕ) :
    ‖(d : ℚ_[7]) ^ (6 * 7 ^ r) - 1‖ ≤ (7 : ℝ) ^ (-(r + 1 : ℕ) : ℤ) := by
  have h := (Padic.norm_int_le_pow_iff_dvd (p := 7)
    ((d : ℤ) ^ (6 * 7 ^ r) - 1) (r + 1)).mpr (seven_unit_power_dvd hd r)
  simpa only [Int.cast_sub, Int.cast_pow, Int.cast_natCast, Int.cast_one, Nat.cast_ofNat] using h

/-- Norm/valuation translation, including zero with additive valuation infinity.
Adapted from ANR-FALSE ForMathlib/Padic at the same pinned commit; codomain
is WithTop Z directly, so no extended-integer auxiliary theory is needed. -/
theorem seven_le_addValuation_iff (m : ℤ) (x : ℚ_[7]) :
    (m : WithTop ℤ) ≤ Padic.addValuation x ↔ ‖x‖ ≤ (7 : ℝ) ^ (-m) := by
  by_cases hx : x = 0
  · simp [hx, zpow_nonneg (by norm_num : (0 : ℝ) ≤ 7)]
  · rw [Padic.addValuation.apply hx, Padic.norm_eq_zpow_neg_valuation hx, Nat.cast_ofNat,
      zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 7), WithTop.coe_le_coe]
    omega

theorem seven_unit_power_valuation {d : ℕ} (hd : ¬ 7 ∣ d) (r : ℕ) :
    ((r + 1 : ℕ) : WithTop ℤ) ≤ Padic.addValuation ((d : ℚ_[7]) ^ (6 * 7 ^ r) - 1) :=
  (seven_le_addValuation_iff (r + 1) _).mpr (seven_unit_power_norm hd r)

theorem seven_unit_inverse_cube_error {d : ℕ} (hd : ¬ 7 ∣ d) (r : ℕ) :
    ‖(d : ℚ_[7]) ^ (serreWeight r - 1) - ((d : ℚ_[7]) ^ 3)⁻¹‖ ≤
      (7 : ℝ) ^ (-(r + 1 : ℕ) : ℤ) := by
  have hd0 : (d : ℚ_[7]) ≠ 0 := by
    exact_mod_cast (show d ≠ 0 from fun h => hd (h ▸ dvd_zero 7))
  have hdNorm : ‖(d : ℚ_[7])‖ = 1 :=
    Padic.norm_natCast_eq_one_iff.mpr
      ((Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 7)).mpr hd)
  have he : serreWeight r - 1 + 3 = 6 * 7 ^ r := by
    have := serreWeight_ge_four r
    unfold serreWeight at *
    omega
  have hid : (d : ℚ_[7]) ^ (serreWeight r - 1) - ((d : ℚ_[7]) ^ 3)⁻¹ =
      ((d : ℚ_[7]) ^ (6 * 7 ^ r) - 1) * ((d : ℚ_[7]) ^ 3)⁻¹ := by
    apply (mul_right_cancel₀ (pow_ne_zero 3 hd0))
    simp only [sub_mul, mul_assoc, inv_mul_cancel₀ (pow_ne_zero 3 hd0), mul_one]
    rw [← pow_add, he]
  rw [hid, norm_mul, norm_inv, norm_pow, hdNorm, one_pow, inv_one, mul_one]
  exact seven_unit_power_norm hd r

theorem seven_nonunit_power_norm {d : ℕ} (hd : 7 ∣ d) (r : ℕ) :
    ‖(d : ℚ_[7]) ^ (serreWeight r - 1)‖ ≤
      (7 : ℝ) ^ (-(serreWeight r - 1 : ℕ) : ℤ) := by
  have hi : (7 : ℤ) ∣ (d : ℤ) := by exact_mod_cast hd
  have h := (Padic.norm_int_le_pow_iff_dvd (p := 7)
    ((d : ℤ) ^ (serreWeight r - 1)) (serreWeight r - 1)).mpr
      (pow_dvd_pow_of_dvd hi _)
  simpa only [Int.cast_pow, Int.cast_natCast, Nat.cast_ofNat] using h

theorem seven_nonunit_power_valuation {d : ℕ} (hd : 7 ∣ d) (r : ℕ) :
    ((serreWeight r - 1 : ℕ) : WithTop ℤ) ≤
      Padic.addValuation ((d : ℚ_[7]) ^ (serreWeight r - 1)) :=
  (seven_le_addValuation_iff (serreWeight r - 1 : ℕ) _).mpr (seven_nonunit_power_norm hd r)

/-- The finite sum bound has no divisor-count factor. -/
theorem classical_nonconstant_uniform_norm (r n : ℕ) (hn : n ≠ 0) :
    ‖coeff n (classicalEisensteinSeries r - eisensteinMinusTwo)‖ ≤
      (7 : ℝ) ^ (-(r + 1 : ℕ) : ℤ) := by
  rw [map_sub, classicalEisensteinSeries_coeff, eisensteinMinusTwo_coeff hn,
    fullEisensteinCoeff, ite_eq_right hn]
  push_cast
  rw [Finset.sum_filter, ← Finset.sum_sub_distrib]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
  intro d _
  by_cases hd : 7 ∣ d
  · simp only [hd, not_true_eq_false, ite_false, sub_zero]
    exact (seven_nonunit_power_norm hd r).trans
      (zpow_le_zpow_right₀ (by norm_num) (by have := serreWeight_exponent_ge r; omega))
  · simp only [hd, not_false_eq_true, ite_true]
    exact seven_unit_inverse_cube_error hd r

theorem classical_nonconstant_uniform_valuation (r n : ℕ) (hn : n ≠ 0) :
    ((r + 1 : ℕ) : WithTop ℤ) ≤
      Padic.addValuation (coeff n (classicalEisensteinSeries r - eisensteinMinusTwo)) :=
  (seven_le_addValuation_iff (r + 1) _).mpr (classical_nonconstant_uniform_norm r n hn)

/-- The index R precedes the universal quantifier over all positive degrees. -/
theorem classical_nonconstant_all_precisions :
    ∀ M : ℤ, ∃ R : ℕ, ∀ r ≥ R, ∀ n ≥ 1,
      (M : WithTop ℤ) ≤
        Padic.addValuation (coeff n (classicalEisensteinSeries r - eisensteinMinusTwo)) := by
  intro M
  refine ⟨M.toNat, fun r hr n hn => ?_⟩
  have hm : M ≤ (r + 1 : ℕ) := by omega
  exact (WithTop.coe_le_coe.mpr hm).trans (classical_nonconstant_uniform_valuation r n (by omega))

/-- The stabilizing Euler correction vanishes along the full weight sequence. -/
theorem serre_euler_power_tendsto_zero :
    Tendsto (fun r => (7 : ℚ_[7]) ^ (serreWeight r - 1)) atTop (𝓝 0) := by
  have he : Tendsto (fun r => serreWeight r - 1) atTop atTop :=
    tendsto_atTop_mono (fun r => (Nat.le_succ r).trans (serreWeight_exponent_ge r)) tendsto_id
  exact (tendsto_pow_atTop_nhds_zero_of_norm_lt_one
    (Padic.norm_p_lt_one (p := 7))).comp he

theorem serre_euler_factor_ne_zero (r : ℕ) :
    1 - (7 : ℚ_[7]) ^ (serreWeight r - 1) ≠ 0 := by
  have he : 0 < serreWeight r - 1 := by have := serreWeight_ge_four r; omega
  have hnorm : ‖(7 : ℚ_[7]) ^ (serreWeight r - 1)‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) (Padic.norm_p_lt_one (p := 7)) he.ne'
  intro h
  rw [← sub_eq_zero.mp h, norm_one] at hnorm
  exact (lt_irrefl 1) hnorm

/-- Explicit shift back to index zero, whose weight is four. -/
theorem serre_stabilised_constant_tendsto_eta :
    Tendsto (fun r => ((stabilisedCoeff 7 (serreWeight r) 0 : ℚ) : ℚ_[7]))
      atTop (𝓝 eta) := by
  apply (tendsto_add_atTop_iff_nat 1).mp
  exact classical_constant_tendsto_eta

theorem full_constant_eq_stabilised_div (r : ℕ) :
    (fullEisensteinCoeff (serreWeight r) 0 : ℚ_[7]) =
      (stabilisedCoeff 7 (serreWeight r) 0 : ℚ_[7]) /
        (1 - (7 : ℚ_[7]) ^ (serreWeight r - 1)) := by
  rw [eq_div_iff (serre_euler_factor_ne_zero r)]
  simp only [fullEisensteinCoeff, stabilisedCoeff]
  push_cast
  ring

/-- Removing the Euler factor preserves the already proved half-zeta limit. -/
theorem full_classical_constant_tendsto_eta :
    Tendsto (fun r => coeff 0 (classicalEisensteinSeries r)) atTop (𝓝 eta) := by
  have he : Tendsto (fun r => 1 - (7 : ℚ_[7]) ^ (serreWeight r - 1)) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℚ_[7]))).sub serre_euler_power_tendsto_zero
  have h := serre_stabilised_constant_tendsto_eta.div he one_ne_zero
  convert h using 1
  · funext r
    rw [classicalEisensteinSeries_coeff, full_constant_eq_stabilised_div]
    rfl
  · simp

theorem seven_precision_bound_tendsto_zero :
    Tendsto (fun r : ℕ => (7 : ℝ) ^ (-(r + 1 : ℕ) : ℤ)) atTop (𝓝 0) := by
  have h : Tendsto (fun r : ℕ => ((7 : ℝ)⁻¹) ^ r) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by norm_num)
  convert h.comp (tendsto_add_atTop_nat 1) using 1
  funext r
  simp only [Function.comp_apply, zpow_neg, zpow_natCast, inv_pow]

/-- One error bound covers the constant term and all positive degrees. -/
theorem classical_all_coefficients_norm (r n : ℕ) :
    ‖coeff n (classicalEisensteinSeries r - eisensteinMinusTwo)‖ ≤
      max ‖coeff 0 (classicalEisensteinSeries r) - eta‖
        ((7 : ℝ) ^ (-(r + 1 : ℕ) : ℤ)) := by
  by_cases hn : n = 0
  · subst n
    simpa only [map_sub, coeff_zero_eq_constantCoeff, eisensteinMinusTwo_constant] using
      le_max_left ‖constantCoeff (classicalEisensteinSeries r) - eta‖
        ((7 : ℝ) ^ (-(r + 1 : ℕ) : ℤ))
  · exact (classical_nonconstant_uniform_norm r n hn).trans (le_max_right _ _)

/-- Unconditional uniform convergence to the EXISTING measure specialization. -/
theorem classical_eisenstein_tendstoUniformly :
    TendstoUniformly (fun r n => coeff n (classicalEisensteinSeries r))
      (fun n => coeff n eisensteinMinusTwo) atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have hc : Tendsto (fun r => ‖coeff 0 (classicalEisensteinSeries r) - eta‖)
      atTop (𝓝 0) := by
    simpa using (full_classical_constant_tendsto_eta.sub
      (tendsto_const_nhds (x := eta))).norm
  filter_upwards [hc.eventually (gt_mem_nhds hε),
    seven_precision_bound_tendsto_zero.eventually (gt_mem_nhds hε)] with r hr hpow n
  rw [dist_eq_norm', ← map_sub]
  exact (classical_all_coefficients_norm r n).trans_lt (max_lt hr hpow)

open scoped Zeta7UniformTopology in
/-- Convergence in the proved uniform coefficient topology, not the product topology. -/
theorem classical_eisenstein_tendsto_uniform_topology :
    Tendsto classicalEisensteinSeries atTop (𝓝 eisensteinMinusTwo) :=
  Zeta7UniformTopology.tendsto_iff_tendstoUniformly.mpr classical_eisenstein_tendstoUniformly

end Zeta7Main

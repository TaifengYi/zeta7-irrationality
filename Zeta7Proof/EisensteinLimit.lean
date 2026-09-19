import Zeta7Proof.EisensteinSpecialization
import PadicLFunctions.EisensteinComplex

/-! Classical Eisenstein coefficients converge to the evaluated family.
The convergence stated here is for each fixed coefficient, not uniform
convergence over all coefficients or analytic continuation. -/

set_option autoImplicit false
namespace Zeta7Main
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩
open PowerSeries PadicLFunctions PadicInt Filter Topology

theorem interpolationWeight_ge_four (m : ℕ) : 4 ≤ interpolationWeight m := by
  have hp : 7 ≤ 7 ^ (m + 1) := by
    calc 7 = 7 ^ 1 := by norm_num
         _ ≤ 7 ^ (m + 1) := Nat.pow_le_pow_right (by decide) (by omega)
  unfold interpolationWeight
  omega

theorem interpolationWeight_even (m : ℕ) : Even (interpolationWeight m) := by
  have h := interpolationWeight_branch m
  have hm := (ZMod.natCast_eq_natCast_iff (interpolationWeight m) 4 6).mp h
  change interpolationWeight m % 6 = 4 % 6 at hm
  rw [Nat.even_iff]
  omega

theorem inverseCubeArgument_tendsto :
    Tendsto (fun m => ((interpolationWeight m - 1 : ℕ) : ℤ_[7])) atTop (𝓝 (-3)) := by
  have h := interpolationArgument_tendsto.neg
  convert h using 1
  funext m
  rw [Nat.cast_sub (by have := interpolationWeight_pos m; omega)]
  push_cast
  ring

theorem unit_weight_moments_tendsto (x : ℤ_[7]ˣ) :
    Tendsto (fun m => (((x : ℤ_[7]) : ℚ_[7]) ^ (interpolationWeight m - 1)))
      atTop (𝓝 (((((x : ℤ_[7]) : ℚ_[7]) ^ 3))⁻¹)) := by
  have hc : Continuous (fun s : ℤ_[7] => ((branchChar 7 3 s x : ℤ_[7]) : ℚ_[7])) :=
    continuous_subtype_val.comp (continuous_const.mul (continuous_onePAdicPow 7 _ _))
  have h := hc.continuousAt.tendsto.comp inverseCubeArgument_tendsto
  rw [branch_three_neg_three_eq_inv_cube] at h
  convert h using 1
  funext m
  simp only [Function.comp_apply]
  have hm : ((interpolationWeight m - 1 : ℕ) : ZMod 6) = (3 : ℕ) := by
    rw [Nat.cast_sub (by have := interpolationWeight_pos m; omega), interpolationWeight_branch]
    norm_num
  rw [branchChar_natCast 7 hm]
  simp [PadicMeasure.unitsPowCM]

theorem classical_constant_tendsto_eta :
    Tendsto (fun m => ((stabilisedCoeff 7 (interpolationWeight m) 0 : ℚ) : ℚ_[7]))
      atTop (𝓝 eta) := by
  have h := (continuousAt_zetaSevenBranch_three.tendsto.comp
    interpolationArgument_tendsto).div_const (2 : ℚ_[7])
  change Tendsto _ atTop (𝓝 (zetaSevenBranch 3 / 2))
  convert h using 1
  funext m
  simp only [Function.comp_apply]
  rw [zetaSevenBranch_interpolation (interpolationWeight_pos m) (interpolationWeight_branch m)]
  simp only [stabilisedCoeff, if_pos rfl]
  push_cast
  rw [show ((interpolationWeight m : ℤ) - 1) = ((interpolationWeight m - 1 : ℕ) : ℤ) by
    have := interpolationWeight_pos m
    omega, zpow_natCast]

/-- All-degree classical coefficient limit for the exact constructed target. -/
theorem classical_coefficients_tendsto (n : ℕ) :
    Tendsto (fun m => ((stabilisedCoeff 7 (interpolationWeight m) n : ℚ) : ℚ_[7]))
      atTop (𝓝 (coeff n eisensteinMinusTwo)) := by
  by_cases hn : n = 0
  · subst n
    simpa only [coeff_zero_eq_constantCoeff, eisensteinMinusTwo_constant] using
      classical_constant_tendsto_eta
  · rw [eisensteinMinusTwo_coeff hn]
    have h := tendsto_finset_sum (n.divisors.filter (fun a => ¬ 7 ∣ a))
      (fun a ha => unit_weight_moments_tendsto (unitOfNat 7 a))
    convert h using 1
    · funext m
      simp only [stabilisedCoeff, if_neg hn, sigmaP, Nat.cast_sum, Nat.cast_pow, Rat.cast_natCast]
      push_cast
      apply Finset.sum_congr rfl
      intro a ha
      rw [unitOfNat_coe 7 (Finset.mem_filter.mp ha).2]
      simp
    · congr 1
      apply Finset.sum_congr rfl
      intro a ha
      rw [unitOfNat_coe 7 (Finset.mem_filter.mp ha).2]
      simp

end Zeta7Main

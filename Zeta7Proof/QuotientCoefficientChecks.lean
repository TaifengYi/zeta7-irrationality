import Zeta7Proof.ActualAEisenstein
import Zeta7Proof.LambertForcing

/-! Kernel checked low coefficients of the original series. These checks alone
do not assert an all-degree modular identity. -/
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open PowerSeries Zeta7Main
namespace Zeta7Common

theorem ASeries_coeff_small (n : ℕ) (hn : n ≤ 4) :
    coeff n ASeries = ![1, 4, 12, 16, 28] ⟨n, by omega⟩ := by
  interval_cases n <;> rw [ASeries_coeff] <;> decide +kernel +revert

theorem xSeries_coeff_two : coeff 2 xSeries = 4 := by
  have h := congrArg (coeff 2) ASeries_mul_xSeries
  change coeff 2 (ASeries * xSeries) = coeff 2 (euler xSeries) at h
  norm_num [coeff_mul, Finset.Nat.antidiagonal_succ, euler_coeff,
    ASeries_coeff_small, coeff_zero_eq_constantCoeff, xSeries_constant, xSeries_linear] at h
  linear_combination -h

theorem xSeries_coeff_three : coeff 3 xSeries = 14 := by
  have h := congrArg (coeff 3) ASeries_mul_xSeries
  change coeff 3 (ASeries * xSeries) = coeff 3 (euler xSeries) at h
  norm_num [coeff_mul, Finset.Nat.antidiagonal_succ, euler_coeff,
    ASeries_coeff_small, coeff_zero_eq_constantCoeff, xSeries_constant, xSeries_linear,
    xSeries_coeff_two] at h
  linear_combination (-1 / 2 : ℚ) * h

theorem xSeries_coeff_four : coeff 4 xSeries = 40 := by
  have h := congrArg (coeff 4) ASeries_mul_xSeries
  change coeff 4 (ASeries * xSeries) = coeff 4 (euler xSeries) at h
  norm_num [coeff_mul, Finset.Nat.antidiagonal_succ, euler_coeff,
    ASeries_coeff_small, coeff_zero_eq_constantCoeff, xSeries_constant, xSeries_linear,
    xSeries_coeff_two, xSeries_coeff_three] at h
  linear_combination (-1 / 3 : ℚ) * h

def firstQuotientDifference : ℚ⟦X⟧ :=
  (1 + C 13 * xSeries + C 49 * xSeries ^ 2) * eisensteinFourQ -
    ASeries ^ 2 * (1 + C 245 * xSeries + C 2401 * xSeries ^ 2)

def secondQuotientDifference : ℚ⟦X⟧ :=
  (1 + C 13 * xSeries + C 49 * xSeries ^ 2) * (expand 7 (by decide) eisensteinFourQ) -
    ASeries ^ 2 * (1 + C 5 * xSeries + xSeries ^ 2)

theorem eisensteinFourQ_coeff_small (n : ℕ) (hn : n ≤ 4) :
    coeff n eisensteinFourQ = ![1, 240, 2160, 6720, 17520] ⟨n, by omega⟩ := by
  rw [eisensteinFourQ]
  simp only [map_add, coeff_one, coeff_C_mul, coeff_mk, sigmaThree]
  interval_cases n <;> decide +kernel +revert

theorem firstQuotientDifference_coeff_small (n : ℕ) (hn : n ≤ 4) :
    coeff n firstQuotientDifference = 0 := by
  interval_cases n <;>
    norm_num [firstQuotientDifference, pow_two, coeff_mul,
      Finset.Nat.antidiagonal_succ, ASeries_coeff_small, eisensteinFourQ_coeff_small,
      coeff_zero_eq_constantCoeff, xSeries_constant, xSeries_linear,
      xSeries_coeff_two, xSeries_coeff_three, xSeries_coeff_four] <;>
    norm_num [← coeff_zero_eq_constantCoeff, ASeries_coeff_small,
      eisensteinFourQ_coeff_small, ← map_ofNat C, coeff_C, map_ofNat]

theorem secondQuotientDifference_coeff_small (n : ℕ) (hn : n ≤ 4) :
    coeff n secondQuotientDifference = 0 := by
  interval_cases n <;>
    norm_num [secondQuotientDifference, pow_two, coeff_mul, coeff_expand,
      Finset.Nat.antidiagonal_succ, ASeries_coeff_small, eisensteinFourQ_coeff_small,
      coeff_zero_eq_constantCoeff, xSeries_constant, xSeries_linear,
      xSeries_coeff_two, xSeries_coeff_three, xSeries_coeff_four] <;>
    norm_num [← coeff_zero_eq_constantCoeff, ASeries_coeff_small,
      eisensteinFourQ_coeff_small, ← map_ofNat C, coeff_C, map_ofNat]

end Zeta7Common

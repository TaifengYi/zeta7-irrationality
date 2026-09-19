import Zeta7Proof.ClosedAnnulusMaps
import Zeta7Proof.ActualTargetClearedEquation

/-! The actual P and N polynomials are units on every closed annulus strictly
inside 1 < |Y| < 49, by explicit strict contractions. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
namespace Zeta7Annulus.ClosedAnnulus
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩
variable {r R : ℝ} [Fact (0 < r)] [Fact (0 < R)]

def annularP : ClosedAnnulus r R := 1 + monomial 1 13 + monomial 2 49
def annularN : ClosedAnnulus r R := 1 + monomial 1 245 + monomial 2 2401
def pContraction : ClosedAnnulus r R := monomial (-1) (1 / 13) + monomial 1 (49 / 13)
def nContraction : ClosedAnnulus r R := monomial 1 245 + monomial 2 2401

theorem norm_thirteen : ‖(13 : ℚ_[7])‖ = 1 :=
  Padic.norm_natCast_eq_one_iff.mpr (by decide : Nat.Coprime 7 13)

theorem norm_fortynine : ‖(49 : ℚ_[7])‖ = (1 / 49 : ℝ) := by
  have he : (49 : ℚ_[7]) = 7 ^ 2 := by norm_num
  have hp : ‖(7 : ℚ_[7])‖ = (7 : ℝ)⁻¹ := by simpa using (Padic.norm_p (p := 7))
  rw [he, norm_pow, hp]
  norm_num

theorem norm_twofortyfive : ‖(245 : ℚ_[7])‖ = (1 / 49 : ℝ) := by
  have he : (245 : ℚ_[7]) = 5 * 49 := by norm_num
  have h5 : ‖(5 : ℚ_[7])‖ = 1 := Padic.norm_natCast_eq_one_iff.mpr (by decide)
  rw [he, norm_mul, h5, norm_fortynine, one_mul]

theorem norm_twentyfourhundredone : ‖(2401 : ℚ_[7])‖ = (1 / 2401 : ℝ) := by
  have he : (2401 : ℚ_[7]) = 49 ^ 2 := by norm_num
  rw [he, norm_pow, norm_fortynine]
  norm_num

theorem pContraction_norm_lt_one (hr : 1 < r) (hR : R < 49) (hrR : r ≤ R) :
    ‖pContraction (r := r) (R := R)‖ < 1 := by
  have hR1 : 1 < R := hr.trans_le hrR
  have hr49 : r < 49 := hrR.trans_lt hR
  apply (norm_add_le_max _ _).trans_lt
  rw [max_lt_iff]
  constructor
  · simp only [monomial_norm, norm_div, norm_one, norm_thirteen, div_one, one_mul,
      zpow_neg_one, max_lt_iff]
    exact ⟨(inv_lt_one₀ (Fact.out : 0 < r)).mpr hr,
      (inv_lt_one₀ (Fact.out : 0 < R)).mpr hR1⟩
  · simp only [monomial_norm, norm_div, norm_fortynine, norm_thirteen, div_one,
      zpow_one, max_lt_iff]
    constructor <;> nlinarith

theorem nContraction_norm_lt_one (hr : 1 < r) (hR : R < 49) (hrR : r ≤ R) :
    ‖nContraction (r := r) (R := R)‖ < 1 := by
  have hr49 : r < 49 := hrR.trans_lt hR
  have hr0 : 0 < r := Fact.out
  have hR0 : 0 < R := Fact.out
  apply (norm_add_le_max _ _).trans_lt
  rw [max_lt_iff]
  constructor
  · simp only [monomial_norm, norm_twofortyfive, zpow_one, max_lt_iff]
    constructor <;> nlinarith
  · simp only [monomial_norm, norm_twentyfourhundredone,
      show (2 : ℤ) = (2 : ℕ) from rfl, zpow_natCast, max_lt_iff]
    constructor <;> nlinarith [sq_nonneg (r - 49), sq_nonneg (R - 49)]

theorem annularP_factorization : annularP (r := r) (R := R) =
    monomial 1 13 * (1 + pContraction) := by
  rw [pContraction, mul_add, mul_add, mul_one, monomial_mul, monomial_mul]
  norm_num only [Int.reduceAdd, show (13 : ℚ_[7]) * (1 / 13) = 1 by norm_num,
    show (13 : ℚ_[7]) * (49 / 13) = 49 by norm_num, monomial_zero_one]
  simp only [annularP, add_comm, add_left_comm, add_assoc]

theorem annularP_isUnit (hr : 1 < r) (hR : R < 49) (hrR : r ≤ R) :
    IsUnit (annularP (r := r) (R := R)) := by
  rw [annularP_factorization]
  apply (monomial_isUnit 1 (by norm_num : (13 : ℚ_[7]) ≠ 0)).mul
  have hh := isUnit_one_sub_of_norm_lt_one (x := -pContraction (r := r) (R := R))
    (by simpa only [norm_neg] using pContraction_norm_lt_one hr hR hrR)
  simpa only [sub_neg_eq_add] using hh

theorem annularN_isUnit (hr : 1 < r) (hR : R < 49) (hrR : r ≤ R) :
    IsUnit (annularN (r := r) (R := R)) := by
  have hh := isUnit_one_sub_of_norm_lt_one (x := -nContraction (r := r) (R := R))
    (by simpa only [norm_neg] using nContraction_norm_lt_one hr hR hrR)
  simpa only [sub_neg_eq_add, annularN, nContraction, add_assoc] using hh

theorem annularP_coeffs : (annularP (r := r) (R := R)).coeffs =
    Zeta7Annulus.ofPowerSeries Zeta7Common.targetP := by
  funext k
  cases k with
  | ofNat n =>
      change (annularP (r := r) (R := R)).coeffs (n : ℤ) =
        PowerSeries.coeff n Zeta7Common.targetP
      have h13 : (13 : PowerSeries ℚ_[7]) = PowerSeries.C 13 :=
        (map_ofNat PowerSeries.C 13).symm
      have h49 : (49 : PowerSeries ℚ_[7]) = PowerSeries.C 49 :=
        (map_ofNat PowerSeries.C 49).symm
      simp only [annularP, coeffs_add, coeffs_one, monomial_coeffs, Pi.add_apply,
        bilateralMonomial, Zeta7Annulus.ofPowerSeries_nat, Zeta7Common.targetP,
        map_add, h13, h49, PowerSeries.coeff_C_mul,
        PowerSeries.coeff_X_pow, PowerSeries.coeff_X, PowerSeries.coeff_one]
      split_ifs <;> norm_num at * <;> omega
  | negSucc n => simp [annularP, bilateralMonomial]

end Zeta7Annulus.ClosedAnnulus

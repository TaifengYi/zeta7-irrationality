import Zeta7Proof.AnnularActualTails

/-! Exact transport of complete power series into bilateral coefficient families.
The multiplication proof uses the finite coefficient formula, not convergence assumptions. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
namespace Zeta7Annulus
local instance AnnularPowerSeriesTransport_prime : Fact (Nat.Prime 7) := ⟨by decide⟩
open PowerSeries

theorem ofPowerSeries_of_nonneg (f : ℚ_[7]⟦X⟧) {k : ℤ} (hk : 0 ≤ k) :
    ofPowerSeries f k = coeff k.toNat f := by
  lift k to ℕ using hk
  rfl

theorem ofPowerSeries_of_neg (f : ℚ_[7]⟦X⟧) {k : ℤ} (hk : k < 0) :
    ofPowerSeries f k = 0 := by
  cases k with
  | ofNat n => exact False.elim ((not_lt_of_ge (Int.natCast_nonneg n)) hk)
  | negSucc n => rfl

theorem ofPowerSeries_add (f g : ℚ_[7]⟦X⟧) :
    ofPowerSeries (f + g) = ofPowerSeries f + ofPowerSeries g := by
  funext k; cases k <;> simp [ofPowerSeries]

theorem ofPowerSeries_neg (f : ℚ_[7]⟦X⟧) : ofPowerSeries (-f) = -ofPowerSeries f := by
  funext k; cases k <;> simp [ofPowerSeries]

theorem ofPowerSeries_C (z : ℚ_[7]) : ofPowerSeries (C z) = bilateralMonomial 0 z := by
  funext k; cases k <;> simp [ofPowerSeries, bilateralMonomial, coeff_C]

theorem ofPowerSeries_X : ofPowerSeries (X : ℚ_[7]⟦X⟧) = bilateralMonomial 1 1 := by
  funext k; cases k <;> simp [ofPowerSeries, bilateralMonomial, coeff_X]

theorem ofPowerSeries_mul (f g : ℚ_[7]⟦X⟧) :
    ofPowerSeries (f * g) = bilateralConvolution (ofPowerSeries f) (ofPowerSeries g) := by
  classical
  funext k
  by_cases hk : 0 ≤ k
  · lift k to ℕ using hk
    rw [ofPowerSeries_nat, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    unfold bilateralConvolution
    symm
    rw [tsum_eq_sum (s := (Finset.range (k + 1)).image (fun n : ℕ => (n : ℤ))) (by
      intro i hi
      by_cases hi0 : 0 ≤ i
      · have hki : (k : ℤ) < i := by
          by_contra hn
          apply hi
          exact Finset.mem_image.mpr ⟨i.toNat, Finset.mem_range.mpr (by omega), by omega⟩
        rw [ofPowerSeries_of_neg g (by omega), mul_zero]
      · rw [ofPowerSeries_of_neg f (by omega), zero_mul])]
    rw [Finset.sum_image (by intro a _ b _ h; exact Int.natCast_inj.mp h)]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i ≤ k := by simpa using Finset.mem_range.mp hi
    rw [ofPowerSeries_nat, ← Int.natCast_sub hi', ofPowerSeries_nat]
  · rw [ofPowerSeries_of_neg (f * g) (by omega)]
    unfold bilateralConvolution
    have hz (i : ℤ) : ofPowerSeries f i * ofPowerSeries g (k - i) = 0 := by
      by_cases hi : i < 0
      · rw [ofPowerSeries_of_neg f hi, zero_mul]
      · rw [ofPowerSeries_of_neg g (by omega), mul_zero]
    simp only [hz, tsum_zero]

theorem reverse_add (a b : LaurentCoefficients) : reverse (a + b) = reverse a + reverse b := rfl
theorem reverse_neg (a : LaurentCoefficients) : reverse (-a) = -reverse a := rfl

theorem reverse_monomial (n : ℤ) (z : ℚ_[7]) :
    reverse (bilateralMonomial n z) = bilateralMonomial (-n) z := by
  funext k
  simp only [reverse, bilateralMonomial, neg_eq_iff_eq_neg]

theorem reverse_convolution (a b : LaurentCoefficients) :
    reverse (bilateralConvolution a b) = bilateralConvolution (reverse a) (reverse b) := by
  funext k
  unfold bilateralConvolution reverse
  rw [← (Equiv.neg ℤ).tsum_eq]
  apply tsum_congr
  intro i
  simp only [Equiv.neg_apply]
  congr 1 <;> congr 1 <;> omega

def oppositeSeries (f : ℚ_[7]⟦X⟧) : LaurentCoefficients :=
  reverse (ofPowerSeries (rescale (49 : ℚ_[7])⁻¹ f))

theorem oppositeSeries_add (f g : ℚ_[7]⟦X⟧) :
    oppositeSeries (f + g) = oppositeSeries f + oppositeSeries g := by
  simp only [oppositeSeries, map_add, ofPowerSeries_add, reverse_add]

theorem oppositeSeries_neg (f : ℚ_[7]⟦X⟧) : oppositeSeries (-f) = -oppositeSeries f := by
  simp only [oppositeSeries, map_neg, ofPowerSeries_neg, reverse_neg]

theorem oppositeSeries_mul (f g : ℚ_[7]⟦X⟧) :
    oppositeSeries (f * g) = bilateralConvolution (oppositeSeries f) (oppositeSeries g) := by
  simp only [oppositeSeries, map_mul, ofPowerSeries_mul, reverse_convolution]

theorem oppositeSeries_C (z : ℚ_[7]) : oppositeSeries (C z) = bilateralMonomial 0 z := by
  have he : rescale (49 : ℚ_[7])⁻¹ (C z) = C z := by
    ext n
    simp only [coeff_rescale, coeff_C]
    split_ifs with hn
    · subst n; simp
    · simp
  simp only [oppositeSeries, he, ofPowerSeries_C, reverse_monomial, neg_zero]

theorem oppositeSeries_X : oppositeSeries (X : ℚ_[7]⟦X⟧) = bilateralMonomial (-1) (49 : ℚ_[7])⁻¹ := by
  simp only [oppositeSeries, rescale_X, ofPowerSeries_mul, ofPowerSeries_C,
    ofPowerSeries_X, reverse_convolution, reverse_monomial, neg_zero]
  funext k
  simp [bilateralMonomial_convolution, bilateralMonomial]

theorem oppositeSeries_euler (f : ℚ_[7]⟦X⟧) :
    oppositeSeries (Zeta7Common.euler f) = -bilateralEuler (oppositeSeries f) := by
  funext k
  by_cases hk : 0 ≤ -k
  · simp only [oppositeSeries, reverse, Pi.neg_apply, bilateralEuler,
      ofPowerSeries_of_nonneg _ hk, coeff_rescale, Zeta7Common.euler_coeff]
    have he : ((-k).toNat : ℚ_[7]) = -(k : ℚ_[7]) := by
      exact_mod_cast Int.toNat_of_nonneg hk
    rw [he]; ring
  · simp only [oppositeSeries, reverse, Pi.neg_apply, bilateralEuler,
      ofPowerSeries_of_neg _ (by omega : -k < 0), mul_zero, neg_zero]

end Zeta7Annulus

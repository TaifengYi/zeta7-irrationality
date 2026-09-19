import Zeta7Proof.AnnulusEstimates
import Mathlib.Analysis.Normed.Module.Basic

/-! The concrete polynomial estimates of manuscript Section 3, equation (10).
They hold in every ultrametric normed field extending Q_7 isometrically.
No modular interpretation of j or of the ordinary components is assumed. -/

set_option autoImplicit false
noncomputable section
namespace Zeta7Section3
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩
variable (K : Type*) [NormedField K] [NormedAlgebra ℚ_[7] K] [IsUltrametricDist K]

def domainP (x : K) : K := 1 + 13 * x + 49 * x ^ 2
def domainN (x : K) : K := 1 + 245 * x + 2401 * x ^ 2
def domainT (x : K) : K := 1 - 490 * x - 21609 * x ^ 2 - 235298 * x ^ 3 - 823543 * x ^ 4
def domainJ (x : K) : K := domainP K x * domainN K x ^ 3 / x

theorem norm_nat_unit (u : ℕ) (hu : Nat.Coprime 7 u) : ‖(u : K)‖ = 1 := by
  have h := norm_algebraMap' K (u : ℚ_[7])
  simpa only [map_natCast, Padic.norm_natCast_eq_one_iff.mpr hu] using h

theorem norm_seven : ‖(7 : K)‖ = (7 : ℝ)⁻¹ := by
  have h := norm_algebraMap' K (7 : ℚ_[7])
  have hp := Padic.norm_p (p := 7)
  norm_num only [Nat.cast_ofNat] at hp
  simpa only [map_ofNat, hp, one_div] using h

theorem norm_unit_seven_power (u k : ℕ) (hu : Nat.Coprime 7 u) :
    ‖((u * 7 ^ k : ℕ) : K)‖ = ((7 : ℝ) ^ k)⁻¹ := by
  push_cast
  rw [norm_mul, norm_pow, norm_nat_unit K u hu, norm_seven, one_mul, inv_pow]

theorem domain_coefficient_norms :
    ‖(13 : K)‖ = 1 ∧ ‖(49 : K)‖ = 1 / 49 ∧
    ‖(245 : K)‖ = 1 / 49 ∧ ‖(2401 : K)‖ = 1 / 2401 ∧
    ‖(490 : K)‖ = 1 / 49 ∧ ‖(21609 : K)‖ = 1 / 2401 ∧
    ‖(235298 : K)‖ = 1 / 117649 ∧ ‖(823543 : K)‖ = 1 / 823543 := by
  refine ⟨norm_nat_unit K 13 (by decide), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert norm_unit_seven_power K 1 2 (by decide) using 1 <;> norm_num
  · convert norm_unit_seven_power K 5 2 (by decide) using 1 <;> norm_num
  · convert norm_unit_seven_power K 1 4 (by decide) using 1 <;> norm_num
  · convert norm_unit_seven_power K 10 2 (by decide) using 1 <;> norm_num
  · convert norm_unit_seven_power K 9 4 (by decide) using 1 <;> norm_num
  · convert norm_unit_seven_power K 2 6 (by decide) using 1 <;> norm_num
  · convert norm_unit_seven_power K 1 7 (by decide) using 1 <;> norm_num

/-- The unique dominant P-term on the exact annulus. -/
theorem domainP_norm (x : K) (hx1 : 1 < ‖x‖) (hx49 : ‖x‖ < 49) :
    ‖domainP K x‖ = ‖x‖ := by
  obtain ⟨h13, h49, _⟩ := domain_coefficient_norms K
  have hx0 : 0 < ‖x‖ := by linarith
  have hs : ‖1 + (49 : K) * x ^ 2‖ < ‖x‖ := by
    apply (IsUltrametricDist.norm_add_le_max _ _).trans_lt
    rw [max_lt_iff, norm_one, norm_mul, norm_pow, h49]
    constructor
    · exact hx1
    · nlinarith
  have h13x : ‖(13 : K) * x‖ = ‖x‖ := by rw [norm_mul, h13, one_mul]
  rw [domainP, show (1 : K) + 13 * x + 49 * x ^ 2 = (13 * x) + (1 + 49 * x ^ 2) by ring,
    IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [h13x]; exact hs.ne'),
    h13x, max_eq_left hs.le]

theorem domainN_norm (x : K) (hx49 : ‖x‖ < 49) :
    ‖domainN K x‖ = 1 := by
  obtain ⟨_, _, h245, h2401, _⟩ := domain_coefficient_norms K
  have hx0 := norm_nonneg x
  have hs : ‖(245 : K) * x + 2401 * x ^ 2‖ < 1 := by
    apply (IsUltrametricDist.norm_add_le_max _ _).trans_lt
    rw [max_lt_iff, norm_mul, norm_mul, norm_pow, h245, h2401]
    constructor <;> nlinarith
  rw [domainN, add_assoc,
    IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_one]; exact hs.ne'),
    norm_one, max_eq_left hs.le]

/-- Exact finite-sum bound: the middle three terms all have norm below one. -/
theorem domainT_norm_bound (x : K) (hx49 : ‖x‖ < 49) :
    ‖domainT K x‖ ≤ max 1 (‖x‖ ^ 4 / 823543) := by
  obtain ⟨_, _, _, _, h490, h21609, h235298, h823543⟩ := domain_coefficient_norms K
  have hx0 := norm_nonneg x
  have h2 : ‖x‖ ^ 2 < (49 : ℝ) ^ 2 := pow_lt_pow_left₀ hx49 hx0 (by decide : 2 ≠ 0)
  have h3 : ‖x‖ ^ 3 < (49 : ℝ) ^ 3 := pow_lt_pow_left₀ hx49 hx0 (by decide : 3 ≠ 0)
  have hsub (a b : K) : ‖a - b‖ ≤ max ‖a‖ ‖b‖ := by
    simpa only [sub_eq_add_neg, norm_neg] using IsUltrametricDist.norm_add_le_max a (-b)
  have hsum : ‖1 - (490 : K) * x - 21609 * x ^ 2 - 235298 * x ^ 3‖ ≤ 1 := by
    apply (hsub _ _).trans
    apply max_le
    · apply (hsub _ _).trans
      apply max_le
      · apply (hsub _ _).trans
        apply max_le
        · exact (norm_one : ‖(1 : K)‖ = 1).le
        · rw [norm_mul, h490]; nlinarith
      · rw [norm_mul, norm_pow, h21609]; nlinarith
    · rw [norm_mul, norm_pow, h235298]; nlinarith
  apply (hsub _ _).trans
  apply max_le
  · exact hsum.trans (le_max_left _ _)
  · rw [norm_mul, norm_pow, h823543]
    exact le_of_eq_of_le (by ring) (le_max_right 1 (‖x‖ ^ 4 / 823543))

theorem domain_polynomial_identity (x : K) :
    domainP K x * domainN K x ^ 3 - domainT K x ^ 2 = 1728 * x := by
  simp only [domainP, domainN, domainT]
  ring

theorem domainJ_sub (x : K) (hx : x ≠ 0) :
    domainJ K x - 1728 = domainT K x ^ 2 / x := by
  rw [domainJ, sub_eq_iff_eq_add]
  apply (div_eq_iff hx).mpr
  have h := domain_polynomial_identity K x
  field_simp
  linear_combination h

/-- The norm form of equation (10), at all points over normed extensions. -/
theorem domainJ_sub_norm_bound (x : K) (hx1 : 1 < ‖x‖) (hx49 : ‖x‖ < 49) :
    ‖domainJ K x - 1728‖ ≤ max (1 / ‖x‖) (‖x‖ ^ 7 / 678223072849) := by
  have hx0 : 0 < ‖x‖ := by linarith
  have hx : x ≠ 0 := norm_pos_iff.mp hx0
  rw [domainJ_sub K x hx, norm_div, norm_pow]
  have h := domainT_norm_bound K x hx49
  have hsq : ‖domainT K x‖ ^ 2 ≤ (max 1 (‖x‖ ^ 4 / 823543)) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h 2
  apply (div_le_div_of_nonneg_right hsq hx0.le).trans
  by_cases hcase : ‖x‖ ^ 4 / 823543 ≤ 1
  · rw [max_eq_left hcase, one_pow]
    exact le_max_left _ _
  · rw [max_eq_right (le_of_not_ge hcase)]
    have heq : (‖x‖ ^ 4 / 823543) ^ 2 / ‖x‖ =
        ‖x‖ ^ 7 / 678223072849 := by field_simp; ring
    rw [heq]
    exact le_max_right _ _

theorem domainJ_supersingular_norm (x : K) (hx1 : 1 < ‖x‖) (hx49 : ‖x‖ < 49) :
    ‖domainJ K x - 1728‖ < 1 := by
  apply (domainJ_sub_norm_bound K x hx1 hx49).trans_lt
  rw [max_lt_iff]
  constructor
  · exact (div_lt_one (by linarith)).mpr hx1
  · have hp : ‖x‖ ^ 7 < (49 : ℝ) ^ 7 :=
      pow_lt_pow_left₀ hx49 (norm_nonneg x) (by decide : 7 ≠ 0)
    norm_num at hp ⊢
    linarith

/-- The ordinary-disc calculation used in the paragraph preceding equation (11). -/
theorem domainT_sub_one_norm (x : K) (hx : ‖x‖ ≤ 1) :
    ‖domainT K x - 1‖ < 1 := by
  obtain ⟨_, _, _, _, h490, h21609, h235298, h823543⟩ := domain_coefficient_norms K
  have ht (c : K) (n : ℕ) (hc : ‖c‖ < 1) : ‖c * x ^ n‖ < 1 := by
    rw [norm_mul, norm_pow]
    exact (mul_le_of_le_one_right (norm_nonneg c)
      (pow_le_one₀ (norm_nonneg x) hx)).trans_lt hc
  have h1 : ‖(490 : K) * x‖ < 1 := by
    simpa only [pow_one] using ht 490 1 (by rw [h490]; norm_num)
  have h2 := ht 21609 2 (by rw [h21609]; norm_num)
  have h3 := ht 235298 3 (by rw [h235298]; norm_num)
  have h4 := ht 823543 4 (by rw [h823543]; norm_num)
  have hsum (a b : K) (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) : ‖a + b‖ < 1 :=
    (IsUltrametricDist.norm_add_le_max a b).trans_lt (max_lt ha hb)
  rw [domainT, show (1 : K) - 490*x - 21609*x^2 - 235298*x^3 - 823543*x^4 - 1 =
    -(490*x + 21609*x^2 + 235298*x^3 + 823543*x^4) by ring, norm_neg]
  exact hsum _ _ (hsum _ _ (hsum _ _ h1 h2) h3) h4

theorem domainT_norm_unit_disc (x : K) (hx : ‖x‖ ≤ 1) :
    ‖domainT K x‖ = 1 := by
  have h := domainT_sub_one_norm K x hx
  have hid : domainT K x = 1 + (domainT K x - 1) := by ring
  conv_lhs => rw [hid]
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_one]; exact h.ne'),
    norm_one, max_eq_left h.le]

/-- On the unit disc, j-1728 cannot have strictly positive valuation. -/
theorem domainJ_sub_norm_unit_disc (x : K) (hx0 : x ≠ 0) (hx : ‖x‖ ≤ 1) :
    ‖domainJ K x - 1728‖ = 1 / ‖x‖ := by
  rw [domainJ_sub K x hx0, norm_div, norm_pow, domainT_norm_unit_disc K x hx, one_pow]

theorem domainJ_sub_norm_boundary (x : K) (hx : ‖x‖ = 1) :
    ‖domainJ K x - 1728‖ = 1 := by
  have hx0 : x ≠ 0 := norm_pos_iff.mp (by rw [hx]; norm_num)
  rw [domainJ_sub_norm_unit_disc K x hx0 hx.le, hx, div_one]


end Zeta7Section3

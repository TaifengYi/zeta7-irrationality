import Zeta7Proof.Section3DomainEstimates

/-! The remaining ordinary-disc arithmetic in paper Section 5.3.
Reuses the already compiled annulus estimates without changing the coordinate. -/

set_option autoImplicit false
namespace Zeta7Radius49
open Zeta7Section3
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩
variable (K : Type*) [NormedField K] [NormedAlgebra ℚ_[7] K] [IsUltrametricDist K]

theorem domainP_norm_small (x : K) (hx : ‖x‖ < 1) : ‖domainP K x‖ = 1 := by
  obtain ⟨h13, h49, _⟩ := domain_coefficient_norms K
  have hx0 := norm_nonneg x
  have h : ‖(13 : K) * x + 49*x^2‖ < 1 := by
    apply (IsUltrametricDist.norm_add_le_max _ _).trans_lt
    rw [max_lt_iff, norm_mul, norm_mul, norm_pow, h13, h49, one_mul]
    constructor
    · exact hx
    · nlinarith
  rw [domainP, add_assoc,
    IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_one]; exact h.ne'),
    norm_one, max_eq_left h.le]

theorem domainJ_norm_small (x : K) (hx0 : x ≠ 0) (hx : ‖x‖ < 1) :
    ‖domainJ K x‖ = 1 / ‖x‖ := by
  rw [domainJ, norm_div, norm_mul, norm_pow, domainP_norm_small K x hx,
    domainN_norm K x (by linarith), one_pow, mul_one]

theorem domainP_norm_le_one (x : K) (hx : ‖x‖ ≤ 1) : ‖domainP K x‖ ≤ 1 := by
  obtain ⟨h13, h49, _⟩ := domain_coefficient_norms K
  apply (IsUltrametricDist.norm_add_le_max _ _).trans
  apply max_le
  · apply (IsUltrametricDist.norm_add_le_max _ _).trans
    rw [max_le_iff, norm_one, norm_mul, h13, one_mul]
    exact ⟨le_rfl, hx⟩
  · rw [norm_mul, norm_pow, h49]
    have hx0 := norm_nonneg x
    nlinarith

theorem domainJ_norm_boundary (x : K) (hx : ‖x‖ = 1) : ‖domainJ K x‖ ≤ 1 := by
  rw [domainJ, norm_div, norm_mul, norm_pow, domainN_norm K x (by linarith),
    hx, one_pow, mul_one, div_one]
  exact domainP_norm_le_one K x hx.le

theorem domainJ_norm_annulus (x : K) (hx1 : 1 < ‖x‖) (hx49 : ‖x‖ < 49) :
    ‖domainJ K x‖ = 1 := by
  rw [domainJ, norm_div, norm_mul, norm_pow, domainP_norm K x hx1 hx49,
    domainN_norm K x hx49, one_pow, mul_one]
  exact div_self (by linarith)

end Zeta7Radius49

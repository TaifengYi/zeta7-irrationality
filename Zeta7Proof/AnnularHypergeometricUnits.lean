import Zeta7Proof.AnnularGlobalCandidates
import Zeta7Proof.AnnularHypergeometricFactorials

/-! Strict radius-seven tail bounds for the original hypergeometric factors. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
namespace Zeta7Annulus
local instance AnnularHypergeometricUnits_local1 : Fact (Nat.Prime 7) := ⟨by decide⟩

theorem annularHypergeometricCoefficient_zero (i : Fin 2) :
    annularHypergeometricCoefficient i 0 = 1 := by
  simp [annularHypergeometricCoefficient, ordinaryHypergeometricCoefficient]

theorem hypergeometric_term_seven_bound (i : Fin 2) (n : ℕ) (hn : 0 < n) :
    ‖(annularHypergeometricCoefficient i n : ℚ_[7])‖ * ((7 : ℝ)⁻¹) ^ n ≤ (7 : ℝ)⁻¹ := by
  have hv := annularHypergeometricCoefficient_gauss_one i n hn
  have hv' : (0 : ℤ) < padicValRat 7 (annularHypergeometricCoefficient i n) + n := by
    exact_mod_cast hv
  have hv7 : padicValRat 7 (7 : ℚ) = 1 := by
    simpa using padicValRat.self (p := 7) (by decide)
  have hval : 1 ≤ padicValRat 7 (annularHypergeometricCoefficient i n * (7 : ℚ) ^ n) := by
    rw [padicValRat.mul (annularHypergeometricCoefficient_nonzero i n)
      (pow_ne_zero n (by norm_num)), padicValRat.pow, hv7]
    simp only [mul_one]
    omega
  have hb := Zeta7Section3.norm_bound_of_valuation
    ((annularHypergeometricCoefficient i n * (7 : ℚ) ^ n : ℚ) : ℚ_[7]) 1 (by
      intro _
      rw [Padic.valuation_ratCast]
      exact_mod_cast hval)
  have h7 : ‖(7 : ℚ_[7])‖ = (7 : ℝ)⁻¹ := by simpa using (Padic.norm_p (p := 7))
  simpa only [Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat, norm_mul, norm_pow,
    h7, Nat.cast_ofNat, Real.rpow_neg_one] using hb

namespace ClosedAnnulus
variable {r R : ℝ} [Fact (0 < r)] [Fact (0 < R)]

theorem hypergeometricCompose_sub_one_bound (i : Fin 2) (s : ClosedAnnulus r R)
    (hs : ‖s‖ ≤ (7 : ℝ)⁻¹) : ‖hypergeometricCompose i s - 1‖ ≤ (7 : ℝ)⁻¹ := by
  have hs1 : ‖s‖ < 1 := hs.trans_lt (by norm_num)
  have hf := hypergeometric_terms_summable i s hs1
  have htail : Summable (fun n : ℕ => constant (annularHypergeometricCoefficient i (n + 1) : ℚ_[7]) *
      s ^ (n + 1)) := hf.comp_injective (fun a b h => Nat.succ_injective h)
  have he : hypergeometricCompose i s - 1 =
      ∑' n : ℕ, constant (annularHypergeometricCoefficient i (n + 1) : ℚ_[7]) * s ^ (n + 1) := by
    rw [hypergeometricCompose, hf.tsum_eq_zero_add]
    simp only [annularHypergeometricCoefficient_zero, Rat.cast_one, map_one, pow_zero,
      mul_one, add_sub_cancel_left]
  rw [he]
  apply norm_le_of_hasSum htail.hasSum (by norm_num)
  intro n
  calc
    _ ≤ ‖constant (r := r) (R := R) (annularHypergeometricCoefficient i (n + 1) : ℚ_[7])‖ *
        ‖s ^ (n + 1)‖ := norm_mul_le _ _
    _ ≤ ‖(annularHypergeometricCoefficient i (n + 1) : ℚ_[7])‖ * ((7 : ℝ)⁻¹) ^ (n + 1) := by
      rw [constant_norm]
      exact mul_le_mul_of_nonneg_left ((norm_pow_le _ _).trans
        (pow_le_pow_left₀ (norm_nonneg _) hs _)) (norm_nonneg _)
    _ ≤ _ := hypergeometric_term_seven_bound i (n + 1) (by omega)

theorem hypergeometricCompose_isUnit (i : Fin 2) (s : ClosedAnnulus r R)
    (hs : ‖s‖ ≤ (7 : ℝ)⁻¹) : IsUnit (hypergeometricCompose i s) := by
  have ht : ‖1 - hypergeometricCompose i s‖ < 1 := by
    rw [norm_sub_rev]
    exact (hypergeometricCompose_sub_one_bound i s hs).trans_lt (by norm_num)
  simpa only [sub_sub_cancel] using isUnit_one_sub_of_norm_lt_one ht

end ClosedAnnulus
end Zeta7Annulus

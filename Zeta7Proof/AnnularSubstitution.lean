import Zeta7Proof.AnnularInverseBounds
import Zeta7Proof.AnnularHypergeometricComposition

/-! The actual T²/(PN³) substitution is a strict contraction on every closed
annulus inside 1 < |Y| < 49. Hence both original hypergeometric series can be
evaluated there. This does not yet prove the homogeneous differential equation. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
namespace Zeta7Annulus.ClosedAnnulus
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩
variable {r R : ℝ} [Fact (0 < r)] [Fact (0 < R)]

def annularT : ClosedAnnulus r R :=
  1 + monomial 1 (-490) + monomial 2 (-21609) +
    monomial 3 (-235298) + monomial 4 (-823543)

def annularSubstitution : ClosedAnnulus r R := annularT ^ 2 * pInverse * nInverse ^ 3

theorem norm_integer_factor (n b k : ℕ) (hn : n = b * 7 ^ k) (hb : Nat.Coprime 7 b) :
    ‖(n : ℚ_[7])‖ = (7 : ℝ)⁻¹ ^ k := by
  rw [hn, Nat.cast_mul, Nat.cast_pow, norm_mul, norm_pow,
    Padic.norm_natCast_eq_one_iff.mpr hb, Padic.norm_p, one_mul]
  norm_num

theorem annularT_circle_bound {ρ : ℝ} [Fact (0 < ρ)] (hρ : ρ < 49) :
    ‖annularT (r := ρ) (R := ρ)‖ ≤ max 1 (ρ ^ 4 / 823543) := by
  have h490 : ‖(-490 : ℚ_[7])‖ = (1 / 49 : ℝ) := by
    convert norm_integer_factor 490 10 2 (by decide) (by decide) using 1 <;> norm_num [norm_neg]
  have h21609 : ‖(-21609 : ℚ_[7])‖ = (1 / 2401 : ℝ) := by
    convert norm_integer_factor 21609 9 4 (by decide) (by decide) using 1 <;> norm_num [norm_neg]
  have h235298 : ‖(-235298 : ℚ_[7])‖ = (1 / 117649 : ℝ) := by
    convert norm_integer_factor 235298 2 6 (by decide) (by decide) using 1 <;> norm_num [norm_neg]
  have h823543 : ‖(-823543 : ℚ_[7])‖ = (1 / 823543 : ℝ) := by
    convert norm_integer_factor 823543 1 7 (by decide) (by decide) using 1 <;> norm_num [norm_neg]
  have hp : 0 < ρ := Fact.out
  have h2 := pow_le_pow_left₀ hp.le hρ.le 2
  have h3 := pow_le_pow_left₀ hp.le hρ.le 3
  norm_num at h2 h3
  have hb1 : ‖monomial (r := ρ) (R := ρ) 1 (-490)‖ ≤ 1 := by
    rw [monomial_norm, max_self, h490, zpow_one]
    nlinarith
  have hb2 : ‖monomial (r := ρ) (R := ρ) 2 (-21609)‖ ≤ 1 := by
    rw [monomial_norm, max_self, h21609]
    change (1 / 2401 : ℝ) * ρ ^ (2 : ℕ) ≤ 1
    nlinarith
  have hb3 : ‖monomial (r := ρ) (R := ρ) 3 (-235298)‖ ≤ 1 := by
    rw [monomial_norm, max_self, h235298]
    change (1 / 117649 : ℝ) * ρ ^ (3 : ℕ) ≤ 1
    nlinarith
  have hb4 : ‖monomial (r := ρ) (R := ρ) 4 (-823543)‖ = ρ ^ 4 / 823543 := by
    rw [monomial_norm, max_self, h823543]
    change (1 / 823543 : ℝ) * ρ ^ (4 : ℕ) = ρ ^ 4 / 823543
    ring
  unfold annularT
  apply (norm_add_le_max _ _).trans
  apply max_le_max _ hb4.le
  apply (norm_add_le_max _ _).trans (max_le _ hb3)
  apply (norm_add_le_max _ _).trans (max_le _ hb2)
  exact (norm_add_le_max _ _).trans (max_le (by simp only [norm_one]; exact le_rfl) hb1)

theorem substitution_scalar_bound (ρ : ℝ) (hρ : 1 < ρ) (h49 : ρ < 49) :
    (max 1 (ρ ^ 4 / 823543)) ^ 2 * ρ⁻¹ < 1 := by
  have hp : 0 < ρ := by linarith
  rw [mul_inv_lt_iff₀ hp, one_mul]
  by_cases hc : ρ ^ 4 / 823543 ≤ 1
  · rw [max_eq_left hc, one_pow]; exact hρ
  · rw [max_eq_right (le_of_not_ge hc)]
    have h7 := pow_lt_pow_left₀ h49 hp.le (by decide : (7 : ℕ) ≠ 0)
    norm_num at h7
    have h8 := mul_lt_mul_of_pos_right h7 hp
    have he : (ρ ^ 4 / 823543) ^ 2 * (823543 : ℝ) ^ 2 = ρ ^ 7 * ρ := by ring
    nlinarith

theorem annularSubstitution_circle_lt_one {ρ : ℝ} [Fact (0 < ρ)]
    (hρ : 1 < ρ) (h49 : ρ < 49) : ‖annularSubstitution (r := ρ) (R := ρ)‖ < 1 := by
  have ht := annularT_circle_bound (ρ := ρ) h49
  have hp := pInverse_norm_le hρ h49 le_rfl
  have hn := nInverse_norm_le hρ h49 le_rfl
  have hm : 0 ≤ max 1 (ρ ^ 4 / 823543) := zero_le_one.trans (le_max_left _ _)
  apply lt_of_le_of_lt _ (substitution_scalar_bound ρ hρ h49)
  unfold annularSubstitution
  calc
    _ ≤ (‖annularT (r := ρ) (R := ρ)‖ ^ 2 * ‖pInverse (r := ρ) (R := ρ)‖) *
        ‖nInverse (r := ρ) (R := ρ)‖ ^ 3 := by
      exact (norm_mul_le _ _).trans (mul_le_mul
        ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_pow_le _ _) (norm_nonneg _)))
        (norm_pow_le _ _) (norm_nonneg _) (by positivity))
    _ ≤ ((max 1 (ρ ^ 4 / 823543)) ^ 2 * ρ⁻¹) * 1 :=
      mul_le_mul (mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) ht 2) hp
        (norm_nonneg _) (sq_nonneg _))
        (pow_le_one₀ (norm_nonneg _) hn) (by positivity) (by positivity)
    _ = _ := mul_one _

theorem restrict_T {s S : ℝ} [Fact (0 < s)] [Fact (0 < S)]
    (hrs : r ≤ s) (hsS : s ≤ S) (hSR : S ≤ R) :
    restrict hrs hsS hSR annularT = annularT := by
  simp only [annularT, map_add, map_one, restrict_monomial]

theorem restrict_annularSubstitution {s S : ℝ} [Fact (0 < s)] [Fact (0 < S)]
    (hr : 1 < r) (hR : R < 49) (hrs : r ≤ s) (hsS : s ≤ S) (hSR : S ≤ R) :
    restrict hrs hsS hSR annularSubstitution = annularSubstitution := by
  simp only [annularSubstitution, map_mul, map_pow, restrict_T,
    restrict_pInverse hr hR hrs hsS hSR, restrict_nInverse hr hR hrs hsS hSR]

theorem annularSubstitution_norm_lt_one (hr : 1 < r) (hR : R < 49) (hrR : r ≤ R) :
    ‖annularSubstitution (r := r) (R := R)‖ < 1 := by
  have h1 := annularSubstitution_circle_lt_one hr (hrR.trans_lt hR)
  have h2 := annularSubstitution_circle_lt_one (hr.trans_le hrR) hR
  rw [← restrict_annularSubstitution hr hR (le_refl r) (le_refl r) hrR] at h1
  rw [← restrict_annularSubstitution hr hR hrR (le_refl R) (le_refl R)] at h2
  simp only [norm_eq, closedAnnulusGauss, restrict_coeffs, max_self] at h1 h2
  exact max_lt h1 h2

def actualHypergeometricValue (i : Fin 2) : ClosedAnnulus r R :=
  hypergeometricCompose i annularSubstitution

theorem actualHypergeometricValue_hasSum (hr : 1 < r) (hR : R < 49) (hrR : r ≤ R) (i : Fin 2) :
    HasSum (fun n : ℕ => constant (annularHypergeometricCoefficient i n : ℚ_[7]) *
      annularSubstitution ^ n) (actualHypergeometricValue (r := r) (R := R) i) :=
  hypergeometricCompose_hasSum i _ (annularSubstitution_norm_lt_one hr hR hrR)

theorem restrict_actualHypergeometricValue {s S : ℝ} [Fact (0 < s)] [Fact (0 < S)]
    (hr : 1 < r) (hR : R < 49) (hrs : r ≤ s) (hsS : s ≤ S) (hSR : S ≤ R) (i : Fin 2) :
    restrict hrs hsS hSR (actualHypergeometricValue i) = actualHypergeometricValue i := by
  rw [actualHypergeometricValue, restrict_hypergeometricCompose hrs hsS hSR i _
    (annularSubstitution_norm_lt_one hr hR (hrs.trans (hsS.trans hSR))),
    restrict_annularSubstitution hr hR hrs hsS hSR]
  rfl

end Zeta7Annulus.ClosedAnnulus

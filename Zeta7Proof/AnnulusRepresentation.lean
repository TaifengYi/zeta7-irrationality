import Zeta7Proof.AnnulusCoefficients
import Zeta7Proof.UniformEndpoints

/-! Exact coordinate and coefficient identifications only.
The target weight-minus-two section has q-expansion E. The scalar x-series is
H = A(q(x))*E(q(x)), not E with its q variable silently renamed x. -/

set_option autoImplicit false
noncomputable section
namespace Zeta7Main
open Filter Topology PowerSeries Zeta7Annulus
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

def normalisedHSeries : ℚ_[7]⟦X⟧ := rescale (49 : ℚ_[7])⁻¹ HSeries

def oppositeH : LaurentCoefficients := reverse (ofPowerSeries normalisedHSeries)

theorem HSeries_eq_eisenstein_subst :
    HSeries = BSeries.map (algebraMap ℚ ℚ_[7]) *
      eisensteinMinusTwo.subst (qSeries.map (algebraMap ℚ ℚ_[7])) := by
  have hq : HasSubst qSeries := HasSubst.of_constantCoeff_zero' qSeries_constant
  have hqm : HasSubst (qSeries.map (algebraMap ℚ ℚ_[7])) :=
    HasSubst.of_constantCoeff_zero' (by
      rw [← coeff_zero_eq_constantCoeff, coeff_map, coeff_zero_eq_constantCoeff,
        qSeries_constant, map_zero])
  rw [eisensteinMinusTwo_eq_G_add_eta, subst_add hqm, subst_C]
  unfold HSeries
  congr 2
  exact map_subst hq GSeries

theorem HSeries_constant : constantCoeff HSeries = eta := by
  have hq : HasSubst qSeries := HasSubst.of_constantCoeff_zero' qSeries_constant
  have hG : constantCoeff (GSeries.subst qSeries) = 0 :=
    constantCoeff_subst_eq_zero qSeries_constant GSeries GSeries_constant
  have hA : constantCoeff (X * derivative ℚ xUnit * xUnit⁻¹) = 0 := by simp
  have hB : constantCoeff BSeries = 1 := by
    rw [BSeries, ASeries, subst_add hq]
    have h1 : (1 : ℚ⟦X⟧).subst qSeries = 1 := by
      rw [← coe_substAlgHom hq, map_one]
    have hsub : constantCoeff ((X * derivative ℚ xUnit * xUnit⁻¹).subst qSeries) = 0 :=
      constantCoeff_subst_eq_zero qSeries_constant _ hA
    rw [h1, map_add, map_one, hsub, add_zero]
  simp only [HSeries, map_mul, map_add, constantCoeff_C]
  simp only [PowerSeries.constantCoeff, PowerSeries.map,
    MvPowerSeries.constantCoeff_map] at hB hG ⊢
  rw [hB, hG, map_one, map_zero, zero_add, one_mul]

theorem normalisedHSeries_coeff (n : ℕ) :
    coeff n normalisedHSeries = (49 : ℚ_[7])⁻¹ ^ n * coeff n HSeries := by
  simp [normalisedHSeries, coeff_rescale]

theorem normalisedHSeries_constant : constantCoeff normalisedHSeries = eta := by
  rw [← coeff_zero_eq_constantCoeff, normalisedHSeries_coeff]
  simpa only [pow_zero, one_mul, coeff_zero_eq_constantCoeff] using HSeries_constant

theorem oppositeH_nonpositive_coeff (n : ℕ) :
    oppositeH (-(n : ℤ)) = (49 : ℚ_[7])⁻¹ ^ n * coeff n HSeries := by
  simpa only [oppositeH, reverse, neg_neg, ofPowerSeries_nat] using normalisedHSeries_coeff n

theorem oppositeH_positive_coeff (n : ℕ) :
    oppositeH (n + 1 : ℤ) = 0 := by
  change ofPowerSeries normalisedHSeries (Int.negSucc n) = 0
  rfl

theorem oppositeH_constant : oppositeH 0 = zeta7Three / 2 := by
  change coeff 0 normalisedHSeries = zeta7Three / 2
  rw [coeff_zero_eq_constantCoeff, normalisedHSeries_constant]
  rfl

theorem norm_seven_square : ‖(49 : ℚ_[7])‖ = (49 : ℝ)⁻¹ := by
  have hp := Padic.norm_p (p := 7)
  norm_num only [Nat.cast_ofNat] at hp
  rw [show (49 : ℚ_[7]) = (7 : ℚ_[7]) ^ 2 by norm_num, norm_pow, hp]
  norm_num

/-- Exact radius rescaling, valid for every coefficient and every real radius. -/
theorem normalisedHSeries_weighted_coeff (n : ℕ) (ρ : ℝ) :
    ‖coeff n normalisedHSeries‖ * ρ ^ n =
      ‖coeff n HSeries‖ * (49 * ρ) ^ n := by
  rw [normalisedHSeries_coeff, norm_mul, norm_pow, norm_inv, norm_seven_square, inv_inv,
    mul_pow]
  ring

/-- The scalar continuation obligation is exactly radius 49 in x and radius 1 in t. -/
theorem normalisedHSeries_decay_iff (ρ : ℝ) :
    Tendsto (fun n => ‖coeff n normalisedHSeries‖ * ρ ^ n) atTop (𝓝 0) ↔
      Tendsto (fun n => ‖coeff n HSeries‖ * (49 * ρ) ^ n) atTop (𝓝 0) := by
  simp only [normalisedHSeries_weighted_coeff]

/-- This is an equivalence of concrete coefficient conditions, not a continuation proof. -/
theorem oppositeH_decay_iff (ρ : ℝ) :
    DecaysAt oppositeH ρ ↔
      Tendsto (fun n => ‖coeff n HSeries‖ * (49 * ρ⁻¹) ^ n) atTop (𝓝 0) := by
  rw [oppositeH, reverse_decaysAt_iff, ofPowerSeries_decaysAt_iff,
    normalisedHSeries_decay_iff]

/-- The exact open annulus is preserved, with no assertion at either boundary. -/
theorem oppositeH_decaysOn_iff :
    DecaysOn oppositeH 1 49 ↔
      ∀ r : ℝ, 1 < r → r < 49 →
        Tendsto (fun n => ‖coeff n HSeries‖ * r ^ n) atTop (𝓝 0) := by
  constructor
  · intro h r hr1 hr49
    have hr0 : 0 < r := by linarith
    have hlow : 1 < 49 / r := (lt_div_iff₀ hr0).mpr (by linarith)
    have hhigh : 49 / r < 49 := (div_lt_iff₀ hr0).mpr (by nlinarith)
    have ht := (oppositeH_decay_iff (49 / r)).mp (h _ hlow hhigh)
    have heq : (49 : ℝ) * (49 / r)⁻¹ = r := by field_simp
    simpa only [heq] using ht
  · intro h ρ hρ1 hρ49
    have hρ0 : 0 < ρ := by linarith
    apply (oppositeH_decay_iff ρ).mpr
    rw [← div_eq_mul_inv]
    exact h (49 / ρ) ((lt_div_iff₀ hρ0).mpr (by linarith))
      ((div_lt_iff₀ hρ0).mpr (by nlinarith))

end Zeta7Main

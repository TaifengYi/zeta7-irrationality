import Zeta7Proof.Section3ScalarCriterion
import Zeta7Proof.Section3DomainEstimates

/-! Exact comparison with equations (1)--(4) of the radius-49 paper.
The limit used below is proved convergent before its value is named. -/

set_option autoImplicit false
noncomputable section
namespace Zeta7Radius49
open Zeta7Main PowerSeries PadicLFunctions Filter Topology
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

def paperEulerZeta (ν : ℕ) : ℚ_[7] :=
  (1 - (7 : ℚ_[7]) ^ (serreWeight ν - 1)) *
    ((zetaNeg (serreWeight ν - 1) : ℚ) : ℚ_[7])

theorem paperEulerZeta_eq_stabilised (ν : ℕ) :
    paperEulerZeta ν = 2 * (stabilisedCoeff 7 (serreWeight ν) 0 : ℚ_[7]) := by
  simp only [paperEulerZeta, stabilisedCoeff]
  push_cast
  ring

theorem paperEulerZeta_tendsto :
    Tendsto paperEulerZeta atTop (𝓝 zeta7Three) := by
  have h := serre_stabilised_constant_tendsto_eta.const_mul (2 : ℚ_[7])
  simpa only [← paperEulerZeta_eq_stabilised, eta, mul_div_cancel₀ _ (by norm_num : (2 : ℚ_[7]) ≠ 0)] using h

def paperEta : ℚ_[7] := (limUnder atTop paperEulerZeta) / 2

theorem paperEta_eq : paperEta = zeta7Three / 2 := by
  rw [paperEta, paperEulerZeta_tendsto.limUnder_eq]

theorem paperEta_eq_eta : paperEta = eta := paperEta_eq

def paperH : ℚ_[7]⟦X⟧ :=
  (ASeries.map (algebraMap ℚ ℚ_[7])).subst (qSeries.map (algebraMap ℚ ℚ_[7])) *
    ((GSeries.map (algebraMap ℚ ℚ_[7])).subst (qSeries.map (algebraMap ℚ ℚ_[7])) +
      C paperEta)

theorem paperH_eq : paperH = HSeries := by
  have hq : HasSubst qSeries := HasSubst.of_constantCoeff_zero' qSeries_constant
  rw [paperH, paperEta_eq_eta]
  unfold HSeries BSeries
  exact congrArg₂ (fun u v : ℚ_[7]⟦X⟧ => u * (v + C eta))
    (map_subst (h := algebraMap ℚ ℚ_[7]) hq ASeries).symm
    (map_subst (h := algebraMap ℚ ℚ_[7]) hq GSeries).symm

theorem paperH_eisenstein :
    paperH = BSeries.map (algebraMap ℚ ℚ_[7]) *
      eisensteinMinusTwo.subst (qSeries.map (algebraMap ℚ ℚ_[7])) := by
  rw [paperH_eq, HSeries_eq_eisenstein_subst]

theorem normalisedHSeries_eq_paper_rescale :
    normalisedHSeries = rescale (49 : ℚ_[7])⁻¹ paperH := by
  rw [paperH_eq]
  rfl

theorem normalisedHSeries_coeff_zpow (n : ℕ) :
    coeff n normalisedHSeries = (49 : ℚ_[7]) ^ (-(n : ℤ)) * coeff n HSeries := by
  rw [normalisedHSeries_coeff, zpow_neg, zpow_natCast, inv_pow]

theorem nonzero_norm_valuation (a : ℚ_[7]) (ha : a ≠ 0) :
    ‖a‖ = (7 : ℝ) ^ (-(Padic.valuation a : ℤ)) := by
  simpa only [Nat.cast_ofNat] using Padic.norm_eq_zpow_neg_valuation ha

end Zeta7Radius49

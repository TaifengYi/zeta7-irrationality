import Zeta7Proof.ModularDifferentialTransport
import Zeta7Proof.LambertForcing

/-! Exact reduction of the actual LH=R equation to modular identities.
The residuals below are concrete power series, not assumed vanishing data. -/
set_option autoImplicit false
noncomputable section
open PowerSeries
namespace Zeta7Common
open Zeta7Main

/-- The rational Eisenstein series used in the forcing is the complete
q-expansion of the genuine classical normalized weight-four form. -/
theorem eisensteinFourQ_classical :
    eisensteinFourQ.map (algebraMap ℚ ℂ) =
      UpperHalfPlane.qExpansion 1 (ModularForm.E (k := 4) (by decide)) := by
  ext n
  rw [coeff_map, EisensteinSeries.E_qExpansion_coeff _ (by decide)]
  by_cases hn : n = 0
  · subst n
    simp [eisensteinFourQ, sigmaThree]
  · have hb : bernoulli 4 = (-1 / 30 : ℚ) := by decide +kernel
    simp [eisensteinFourQ, sigmaThree, coeff_one, hn, hb,
      ArithmeticFunction.sigma_apply]
    ring

def forcingDefect : ℚ⟦X⟧ :=
  C (1 / 240 : ℚ) * (eisensteinFourQ - (expand 7 (by decide)) eisensteinFourQ).subst qSeries -
    BSeries ^ 2 * rationalForcing

theorem actual_forcing_transport :
    (euler (euler (euler GSeries))).subst qSeries =
      C (1 / 240 : ℚ) *
        (eisensteinFourQ - (expand 7 (by decide)) eisensteinFourQ).subst qSeries := by
  rw [← GSeries_euler_three_eisenstein, subst_mul q_hasSubst, subst_C]
  change _ = C (1 / 240 : ℚ) * (C (240 : ℚ) * _)
  rw [← mul_assoc, ← map_mul]
  norm_num

/-- The exact residual equation for the actual H, valid for every rational c. -/
theorem rationalH_modularL_residual (c : ℚ) :
    BSeries ^ 2 * (modularL (rationalH c) - rationalForcing) = forcingDefect +
      BSeries ^ 2 * (modularDefect * euler (rationalH c) +
        C (1 / 2 : ℚ) * euler modularDefect * rationalH c) := by
  have h := rationalH_differential_transport c
  rw [actual_forcing_transport] at h
  unfold forcingDefect
  linear_combination h

/-- The two required all-degree modular identities suffice, without any
additional analytic or recurrence identification. This is a reduction only. -/
theorem rationalH_modularL_of_identities
    (hV : coordinatePotential = rationalPotential)
    (hE : (eisensteinFourQ - (expand 7 (by decide)) eisensteinFourQ).subst qSeries =
      C (240 : ℚ) * BSeries ^ 2 * rationalForcing) (c : ℚ) :
    modularL (rationalH c) = rationalForcing := by
  have hd : modularDefect = 0 := by simp [modularDefect, hV]
  have h := rationalH_modularL_residual c
  have hF : forcingDefect = 0 := by
    rw [forcingDefect, hE]
    have hc : (C (1 / 240 : ℚ) : ℚ⟦X⟧) * C 240 = 1 := by rw [← map_mul]; norm_num
    calc
      _ = (C (1 / 240 : ℚ) * C 240 - 1) * (BSeries ^ 2 * rationalForcing) := by ring
      _ = 0 := by rw [hc]; ring
  rw [hd, hF] at h
  simp only [euler_zero, zero_mul, mul_zero, add_zero] at h
  have hb : BSeries ≠ 0 := by
    intro hz
    have := BSeries_mul_inv
    rw [hz, zero_mul] at this
    exact zero_ne_one this
  exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left (pow_ne_zero 2 hb))

end Zeta7Common

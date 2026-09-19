import Zeta7Proof.ActualRiccati

/-! Section 1.1 for the original modular coordinate and rationalH. -/
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open PowerSeries Zeta7Main
namespace Zeta7Common

theorem short_forcing_numerator : shortN - (1 + 5 * X + X ^ 2) =
    240 * X * (1 + 10 * X) := by
  have h := congrArg Polynomial.coeToPowerSeries.ringHom Zeta7Riccati.forcing_numerator
  simpa only [map_sub, map_add, map_mul, map_pow, map_one, map_ofNat,
    Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X, shortN] using h

theorem rationalForcing_cleared : shortP * rationalForcing = X * (1 + 10 * X) := by
  rw [rationalForcing, ← shortP_value]
  calc
    _ = X * (1 + 10 * X) * (shortP * shortP⁻¹) := by ring
    _ = _ := by rw [shortP_mul_inv, mul_one]

theorem actual_forcing_identity :
    (eisensteinFourQ - (expand 7 (by decide)) eisensteinFourQ).subst qSeries =
      C (240 : ℚ) * BSeries ^ 2 * rationalForcing := by
  rw [← qTransport_apply, map_sub, map_ofNat]
  change pulledE4 - pulledE4Seven = 240 * BSeries ^ 2 * rationalForcing
  apply mul_left_cancel₀ shortP_ne_zero
  linear_combination pulledE4_cleared - pulledE4Seven_cleared +
    BSeries ^ 2 * short_forcing_numerator - 240 * BSeries ^ 2 * rationalForcing_cleared

/-- The actual all-degree modular differential equation, for every rational constant.
This theorem does not use any radius-49 input. -/
theorem rationalH_modularL (c : ℚ) : modularL (rationalH c) = rationalForcing :=
  rationalH_modularL_of_identities coordinatePotential_eq_rationalPotential actual_forcing_identity c

theorem rationalH_quadratic_derivative (c : ℚ) :
    euler (quadratic rationalPotential (rationalH c)) = rationalForcing * rationalH c := by
  rw [euler_quadratic, rationalH_modularL, mul_comm]

end Zeta7Common

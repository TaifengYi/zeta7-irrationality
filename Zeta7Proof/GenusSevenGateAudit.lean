import Zeta7Proof.GenusSevenCoordinate
import Mathlib.NumberTheory.Padics.Hensel

/-! Exact arithmetic at the weight-compatibility boundary. These statements do not
construct a trivialization of the Hodge bundle or an analytic Hecke correspondence. -/

set_option autoImplicit false
noncomputable section
namespace Zeta7GenusSeven
open Zeta7Main Zeta7Section3 PadicLFunctions
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

def unitTwo : ℤ_[7]ˣ :=
  (PadicInt.isUnit_iff.mpr
    (PadicInt.norm_natCast_eq_one_iff.mpr (by decide : Nat.Coprime 7 2))).unit

theorem unitTwo_value : (unitTwo : ℤ_[7]) = 2 := IsUnit.unit_spec _

theorem genuine_weight_at_two :
    ((branchChar 7 4 (-2) unitTwo : ℤ_[7]) : ℚ_[7]) = 1 / 4 := by
  rw [branch_four_neg_two_eq_inv_square, unitTwo_value]
  change ((2 : ℚ_[7]) ^ 2)⁻¹ = 1 / 4
  norm_num

theorem genuine_weight_not_zero :
    ((branchChar 7 4 (-2) unitTwo : ℤ_[7]) : ℚ_[7]) ≠ 1 := by
  rw [genuine_weight_at_two]
  norm_num

/-- This is only the numerical extent of the published canonical-subgroup domain. -/
theorem canonical_radius_gap (r : ℝ) (hr : r < 7 / 8) :
    (7 : ℝ) ^ (2 * r) < (7 : ℝ) ^ (7 / 4 : ℝ) ∧
      (7 : ℝ) ^ (7 / 4 : ℝ) < 49 := by
  constructor
  · exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
  · have h := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 7)
      (by norm_num : (7 / 4 : ℝ) < 2)
    norm_num at h ⊢
    exact h

def ellipticFactor : Polynomial ℤ :=
  1 + Polynomial.C 13 * Polynomial.X + Polynomial.C 49 * Polynomial.X ^ 2

theorem ellipticFactor_at_one : ellipticFactor.aeval (1 : ℤ_[7]) = 63 := by
  norm_num [ellipticFactor, Polynomial.aeval_def]

theorem ellipticFactor_derivative_at_one :
    ellipticFactor.derivative.aeval (1 : ℤ_[7]) = 111 := by
  norm_num [ellipticFactor, Polynomial.aeval_def, Polynomial.derivative_add,
    Polynomial.derivative_mul, Polynomial.derivative_pow]

theorem ellipticFactor_hensel_data :
    ‖ellipticFactor.aeval (1 : ℤ_[7])‖ = (7 : ℝ)⁻¹ ∧
      ‖ellipticFactor.derivative.aeval (1 : ℤ_[7])‖ = 1 := by
  rw [ellipticFactor_at_one, ellipticFactor_derivative_at_one]
  have h7 : ‖(7 : ℤ_[7])‖ = (7 : ℝ)⁻¹ := by
    simpa only [Nat.cast_ofNat] using PadicInt.norm_p (p := 7)
  constructor
  · rw [show (63 : ℤ_[7]) = 9 * 7 by norm_num, norm_mul,
      show ‖(9 : ℤ_[7])‖ = 1 from
        PadicInt.norm_natCast_eq_one_iff.mpr (by decide : Nat.Coprime 7 9), h7]
    norm_num
  · exact PadicInt.norm_natCast_eq_one_iff.mpr (by decide)

/-- The polynomial P has an actual Q_7 root of norm one, not just a numerical approximation. -/
theorem ellipticFactor_root_on_unit_circle :
    ∃ α : ℚ_[7], ‖α‖ = 1 ∧ domainP ℚ_[7] α = 0 := by
  obtain ⟨hF, hdF⟩ := ellipticFactor_hensel_data
  obtain ⟨z, hz, hzdist, _⟩ := hensels_lemma
    (F := ellipticFactor) (a := (1 : ℤ_[7])) (by rw [hF, hdF]; norm_num)
  have hzval : 1 + 13 * z + 49 * z ^ 2 = 0 := by
    simpa [ellipticFactor, Polynomial.aeval_def] using hz
  have hznorm : ‖z‖ = 1 := by
    rw [hdF] at hzdist
    have h := PadicInt.norm_eq_of_norm_add_lt_right
      (z1 := z) (z2 := (-1 : ℤ_[7])) (by simpa [sub_eq_add_neg] using hzdist)
    simpa using h
  refine ⟨z, by simpa using hznorm, ?_⟩
  have h := congrArg (fun a : ℤ_[7] => (a : ℚ_[7])) hzval
  exact h

/-- Consequently 1/P cannot be an everywhere defined reciprocal even on the unit disc. -/
theorem no_pointwise_reciprocal_on_unit_disc :
    ¬ ∃ g : ℚ_[7] → ℚ_[7], ∀ x : ℚ_[7], ‖x‖ ≤ 1 → domainP ℚ_[7] x * g x = 1 := by
  obtain ⟨α, hα, hP⟩ := ellipticFactor_root_on_unit_circle
  rintro ⟨g, hg⟩
  have h := hg α hα.le
  rw [hP, zero_mul] at h
  exact zero_ne_one h

end Zeta7GenusSeven

import Zeta7Proof.ValenceGeneric
import Zeta7Proof.EtaCoordinateQExpansion
import Zeta7Proof.Section3DomainEstimates

/-! Radius internalization, Phase I: the exact coordinate normalization (frozen).

The project coordinate `x` is the eta quotient `η(7τ)⁴/η(τ)⁴ = q ∏_{7∤m} (1-q^m)^{-4}`, i.e. the
reciprocal of the standard `X₀(7)` Hauptmodul `t = (η(τ)/η(7τ))⁴`. The Fricke involution
`w₇ : τ ↦ -1/(7τ)` acts by `x ↦ 1/(49x)` (equivalently `t ↦ 49/t`). Consequently, for the
`7`-adic norm, `w₇` acts on radii by `|x| ↦ 49/|x|`: it exchanges the canonical ordinary disc
`|x| ≤ 1` with the non-canonical ordinary region `|x| ≥ 49`, preserves the supersingular annulus
`1 < |x| < 49`, and fixes the circle `|x| = 7`. This is the precise sense of the number `49`.

The explicit `w₇`-transforms of the polynomials `P, N, T` of the modular `j`-invariant
`j = P N³/x` are recorded; `Tt` (the transform of `T`) is the polynomial whose zeros are the
zeros of `E₆(7τ)`, used for the Katz ratio `E₆(7τ)/E₆(τ) = Tt(x)/T(x)`. -/

set_option autoImplicit false
noncomputable section
namespace Zeta7Radius49
open Complex UpperHalfPlane ModularForm Zeta7Valence Zeta7LevelSeven Zeta7Section3

/-- **Coordinate normalization I.** The project coordinate is the eta quotient `η(7τ)⁴/η(τ)⁴`. -/
theorem projectX_eq_etaQuotient (τ : ℍ) :
    Zeta7LevelSeven.etaCoordinate τ = ModularForm.eta (7 * (τ : ℂ)) ^ 4 / ModularForm.eta τ ^ 4 :=
  etaCoordinate_value τ

/-- **Coordinate normalization II.** Its `q`-expansion is exactly the project series `xSeries`. -/
theorem projectX_qExpansion :
    qExpansion 1 Zeta7LevelSeven.etaCoordinate = Zeta7Main.xSeries.map (algebraMap ℚ ℂ) :=
  etaCoordinate_qExpansion

/-- The standard genus-zero Hauptmodul `t = (η(τ)/η(7τ))⁴`. -/
def standardT (z : ℂ) : ℂ := ModularForm.eta z ^ 4 / ModularForm.eta (7 * z) ^ 4

/-- **Coordinate normalization III.** `x = 1/t`. -/
theorem projectX_eq_inv_standardT (z : ℂ) : Xf z = (standardT z)⁻¹ := by
  simp only [Xf, standardT, inv_div]

/-- **Coordinate normalization IV (Fricke).** `x(-1/(7z)) = 1/(49 x(z))`. -/
theorem projectX_fricke {z : ℂ} (hz : 0 < z.im) : Xf (-1 / (7 * z)) = (49 * Xf z)⁻¹ := by
  have h7 : 0 < (7 * z).im := by simp; linarith
  have h := Xf_S h7
  rwa [show 7 * z / 7 = z by ring] at h

/-- The same for the standard Hauptmodul: `t(-1/(7z)) = 49/t(z)`. -/
theorem standardT_fricke {z : ℂ} (hz : 0 < z.im) :
    standardT (-1 / (7 * z)) = 49 / standardT z := by
  have h := projectX_fricke hz
  rw [projectX_eq_inv_standardT, projectX_eq_inv_standardT] at h
  rw [inv_inj.mp h, div_eq_mul_inv]

section Transforms
variable {F : Type*} [Field F] [CharZero F]

/-- The Fricke transform of the polynomial `T` (up to the factor `-7x⁴`). -/
def polyTt (x : F) : F := 1 + 14 * x + 63 * x ^ 2 + 70 * x ^ 3 - 7 * x ^ 4

theorem fricke_P (x : F) (hx : x ≠ 0) :
    (1 + 13 * (49 * x)⁻¹ + 49 * ((49 * x)⁻¹) ^ 2) * (49 * x ^ 2) = 1 + 13 * x + 49 * x ^ 2 := by
  field_simp; ring

theorem fricke_N (x : F) (hx : x ≠ 0) :
    (1 + 245 * (49 * x)⁻¹ + 2401 * ((49 * x)⁻¹) ^ 2) * x ^ 2 = 1 + 5 * x + x ^ 2 := by
  field_simp; ring

theorem fricke_T (x : F) (hx : x ≠ 0) :
    (1 - 490 * (49 * x)⁻¹ - 21609 * ((49 * x)⁻¹) ^ 2 - 235298 * ((49 * x)⁻¹) ^ 3 -
      823543 * ((49 * x)⁻¹) ^ 4) * (7 * x ^ 4) = -polyTt x := by
  simp only [polyTt]; field_simp; ring

/-- `j(7τ) = P(x) (x²+5x+1)³ / x⁷`, the Fricke transform of `j = P N³/x`. -/
theorem fricke_j (x : F) (hx : x ≠ 0) :
    (1 + 13 * (49 * x)⁻¹ + 49 * ((49 * x)⁻¹) ^ 2) *
        (1 + 245 * (49 * x)⁻¹ + 2401 * ((49 * x)⁻¹) ^ 2) ^ 3 / (49 * x)⁻¹ =
      (1 + 13 * x + 49 * x ^ 2) * (1 + 5 * x + x ^ 2) ^ 3 / x ^ 7 := by
  field_simp; ring

end Transforms

section Norms
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩
variable (K : Type*) [NormedField K] [NormedAlgebra ℚ_[7] K] [IsUltrametricDist K]

theorem norm_fortynine : ‖(49 : K)‖ = (49 : ℝ)⁻¹ := by
  have h := norm_seven K
  rw [show (49 : K) = 7 * 7 by norm_num, norm_mul, h]; norm_num

/-- **The radius normalization.** The Fricke involution acts on radii by `r ↦ 49/r`. -/
theorem norm_fricke (x : K) (hx : x ≠ 0) : ‖(49 * x)⁻¹‖ = 49 / ‖x‖ := by
  rw [norm_inv, norm_mul, norm_fortynine]; field_simp

/-- Consequently the open supersingular annulus `1 < |x| < 49` is Fricke-stable. -/
theorem fricke_annulus (x : K) (hx1 : 1 < ‖x‖) (hx49 : ‖x‖ < 49) :
    1 < ‖(49 * x)⁻¹‖ ∧ ‖(49 * x)⁻¹‖ < 49 := by
  have hx0 : x ≠ 0 := norm_pos_iff.mp (by linarith)
  have hp : 0 < ‖x‖ := by linarith
  rw [norm_fricke K x hx0]
  exact ⟨(one_lt_div hp).mpr hx49, (div_lt_iff₀ hp).mpr (by nlinarith)⟩

/-- The canonical ordinary disc `|x| ≤ 1` is exchanged with `|x| ≥ 49`. -/
theorem fricke_ordinary (x : K) (hx0 : x ≠ 0) (hx : ‖x‖ ≤ 1) : 49 ≤ ‖(49 * x)⁻¹‖ := by
  have hp : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  rw [norm_fricke K x hx0, le_div_iff₀ hp]; nlinarith

/-- The fixed circle of the Fricke involution is `|x| = 7`. -/
theorem fricke_fixed_circle (x : K) (hx0 : x ≠ 0) : ‖(49 * x)⁻¹‖ = ‖x‖ ↔ ‖x‖ = 7 := by
  have hp : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  rw [norm_fricke K x hx0, div_eq_iff hp.ne']
  constructor
  · intro h
    have h2 : (‖x‖ - 7) * (‖x‖ + 7) = 0 := by nlinarith
    rcases mul_eq_zero.mp h2 with h3 | h3 <;> linarith
  · intro h; rw [h]; norm_num

end Norms
end Zeta7Radius49

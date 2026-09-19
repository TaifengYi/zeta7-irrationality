import Zeta7Proof.Section3DomainEstimates
import Zeta7Proof.Radius49DiscArithmetic
import Zeta7Proof.Radius49Hasse
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! Phase VI, R2: the Weierstrass model `y² = z³ - 3z + b` with prescribed `j`, and the
supersingular tube of the radius-49 annulus.

* `model_j`, `model_j_tube`: the model with `b² = 4(j-1728)/j` has `j`-invariant `j`.
* `reduced_model_supersingular`: in characteristic seven the model with `b = 0` is elliptic, has
  `j = 1728`, and its Hasse coefficient (the `z⁶` coefficient of `(z³-3z+b)³`) vanishes.
* `supersingular_tube`: on `1 < |x| < 49`, `|P(x)| = |x|`, `|N(x)| = 1`, `|j| = 1`, `|j-1728| < 1`,
  and for every model of `j(x)` one has `|b| < 1`, the Hasse coefficient has norm `< 1` (so it
  reduces to zero), and the model has `j`-invariant `j(x)`.
* `boundary_ordinary`: on `|x| = 1` with `|j| = 1`, `|b| = 1` and the Hasse coefficient is a unit.

No modular interpretation is assumed and no declaration uses the published radius input. -/

set_option autoImplicit false
noncomputable section
namespace Zeta7Radius49
open Polynomial Zeta7Section3
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

section Model
variable {F : Type*} [Field F]

theorem model_discriminant (b : F) : (shortCurve (-3) b).Δ = 432 * (4 - b ^ 2) := by
  rw [shortCurve_discriminant]; ring

theorem model_c_four (b : F) : (shortCurve (-3) b).c₄ = 144 := by
  rw [shortCurve_c_four]; ring

theorem model_isElliptic (b : F) (h : (432 : F) * (4 - b ^ 2) ≠ 0) :
    (shortCurve (-3) b).IsElliptic :=
  ⟨by rw [model_discriminant]; exact isUnit_iff_ne_zero.mpr h⟩

theorem model_j (b : F) [(shortCurve (-3) b).IsElliptic] :
    (shortCurve (-3) b).j = 144 ^ 3 / (432 * (4 - b ^ 2)) := by
  rw [WeierstrassCurve.j_eq, model_discriminant, model_c_four, div_eq_inv_mul]

/-- The square of the model parameter attached to `j`. -/
def tubeB2 (j : F) : F := 4 * (j - 1728) / j

theorem four_sub_tubeB2 (j : F) (hj : j ≠ 0) : 4 - tubeB2 j = 6912 / j := by
  rw [tubeB2]; field_simp; ring

theorem model_isElliptic_tube (j b : F) (hj : j ≠ 0) (h : (2985984 : F) ≠ 0)
    (hb : b ^ 2 = tubeB2 j) : (shortCurve (-3) b).IsElliptic := by
  apply model_isElliptic
  rw [hb, four_sub_tubeB2 j hj]
  intro h0
  apply h
  have : (432 : F) * (6912 / j) * j = 2985984 := by field_simp; norm_num
  rw [← this, h0, zero_mul]

theorem model_j_tube (j b : F) (hj : j ≠ 0) (h : (2985984 : F) ≠ 0)
    (hb : b ^ 2 = tubeB2 j) [(shortCurve (-3) b).IsElliptic] :
    (shortCurve (-3) b).j = j := by
  rw [model_j, hb, four_sub_tubeB2 j hj]
  field_simp
  norm_num
  exact h

end Model

section Reduction
variable {k : Type*} [Field k] [CharP k 7]

theorem reduced_model_isElliptic : (shortCurve (-3 : k) 0).IsElliptic := by
  apply model_isElliptic
  have h : ((1728 : ℕ) : k) ≠ 0 := (CharP.cast_eq_zero_iff k 7 1728).not.mpr (by decide)
  intro h0
  apply h
  rw [← h0]
  push_cast
  ring

/-- In characteristic seven, the model with `b = 0` is the supersingular curve: its
`j`-invariant is `1728` and its Hasse coefficient vanishes. -/
theorem reduced_model_supersingular :
    haveI := reduced_model_isElliptic (k := k)
    (shortCurve (-3 : k) 0).j = 1728 ∧
      ((X ^ 3 + C (-3 : k) * X + C 0 : k[X]) ^ 3).coeff 6 = 0 := by
  have := reduced_model_isElliptic (k := k)
  exact ⟨(shortCurve_j_eq_1728_iff (-3 : k) 0).mpr rfl,
    (cubic_cube_coeff_six_eq_zero (-3 : k) 0).mpr rfl⟩

/-- A parameter in the maximal ideal of a local ring reduces to the supersingular model. -/
theorem local_reduction {A : Type*} [CommRing A] [IsLocalRing A] (b : A)
    (hb : b ∈ IsLocalRing.maximalIdeal A) :
    shortCurve (-3 : IsLocalRing.ResidueField A) (IsLocalRing.residue A b) =
      shortCurve (-3) 0 := by
  rw [(IsLocalRing.residue_eq_zero_iff b).mpr hb]

end Reduction

section Tube
variable (K : Type*) [NormedField K] [NormedAlgebra ℚ_[7] K] [IsUltrametricDist K]

theorem norm_four : ‖(4 : K)‖ = 1 := by
  simpa using norm_nat_unit K 4 (by norm_num)

theorem norm_three : ‖(3 : K)‖ = 1 := by
  simpa using norm_nat_unit K 3 (by norm_num)

theorem ne_2985984 : (2985984 : K) ≠ 0 := by
  intro h
  have := norm_nat_unit K 2985984 (by norm_num)
  push_cast at this
  rw [h, norm_zero] at this
  norm_num at this

theorem norm_tubeB2 (j : K) (hj : ‖j‖ = 1) : ‖tubeB2 j‖ = ‖j - 1728‖ := by
  rw [tubeB2, norm_div, norm_mul, norm_four, hj, one_mul, div_one]

theorem hasse_coeff_norm (b : K) :
    ‖((X ^ 3 + C (-3 : K) * X + C b : K[X]) ^ 3).coeff 6‖ = ‖b‖ := by
  rw [cubic_cube_coeff_six, norm_mul, norm_three, one_mul]

/-- **The supersingular tube.** -/
theorem supersingular_tube (x : K) (hx1 : 1 < ‖x‖) (hx49 : ‖x‖ < 49) :
    ‖domainP K x‖ = ‖x‖ ∧ ‖domainN K x‖ = 1 ∧ ‖domainJ K x‖ = 1 ∧
      ‖domainJ K x - 1728‖ < 1 ∧
      ∀ b : K, b ^ 2 = tubeB2 (domainJ K x) →
        ‖b‖ < 1 ∧ ‖((X ^ 3 + C (-3 : K) * X + C b : K[X]) ^ 3).coeff 6‖ < 1 ∧
        ∃ _ : (shortCurve (-3) b).IsElliptic, (shortCurve (-3) b).j = domainJ K x := by
  have hJ := domainJ_norm_annulus K x hx1 hx49
  have hJ0 : domainJ K x ≠ 0 := norm_ne_zero_iff.mp (by rw [hJ]; norm_num)
  have hS := domainJ_supersingular_norm K x hx1 hx49
  refine ⟨domainP_norm K x hx1 hx49, domainN_norm K x hx49, hJ, hS, fun b hb => ?_⟩
  have hb1 : ‖b‖ < 1 := by
    have h2 : ‖b‖ ^ 2 < 1 ^ 2 := by
      rw [← norm_pow, hb, norm_tubeB2 K _ hJ, one_pow]; exact hS
    exact lt_of_pow_lt_pow_left₀ 2 zero_le_one h2
  haveI hE := model_isElliptic_tube _ b hJ0 (ne_2985984 K) hb
  exact ⟨hb1, by rw [hasse_coeff_norm]; exact hb1,
    hE, model_j_tube _ b hJ0 (ne_2985984 K) hb⟩

/-- Models exist over algebraically closed fields. -/
theorem tube_model_exists [IsAlgClosed K] (j : K) : ∃ b : K, b ^ 2 = tubeB2 j :=
  IsAlgClosed.exists_pow_nat_eq _ (by norm_num)

/-- The ordinary complement: on the closed unit disc `|j - 1728| ≥ 1`, and on the boundary
circle with `|j| = 1` the Hasse coefficient of every model is a unit. -/
theorem boundary_ordinary (x : K) (hx : ‖x‖ = 1) (hJ : ‖domainJ K x‖ = 1)
    (b : K) (hb : b ^ 2 = tubeB2 (domainJ K x)) :
    ‖b‖ = 1 ∧ ‖((X ^ 3 + C (-3 : K) * X + C b : K[X]) ^ 3).coeff 6‖ = 1 := by
  have h2 : ‖b‖ ^ 2 = 1 := by
    rw [← norm_pow, hb, norm_tubeB2 K _ hJ, domainJ_sub_norm_boundary K x hx]
  have hb1 : ‖b‖ = 1 := by
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg b) (by norm_num)).mp h2
  exact ⟨hb1, by rw [hasse_coeff_norm, hb1]⟩

theorem unit_disc_not_supersingular (x : K) (hx0 : x ≠ 0) (hx : ‖x‖ ≤ 1) :
    1 ≤ ‖domainJ K x - 1728‖ := by
  rw [domainJ_sub_norm_unit_disc K x hx0 hx]
  exact (one_le_div (norm_pos_iff.mpr hx0)).mpr hx

end Tube
end Zeta7Radius49

import Zeta7Proof.ValenceGeneric
import Zeta7Proof.ArchCircleAnalytic

/-! The analytic coordinate on the q-disc and its behaviour under `Γ₀(7)`.

* `xFun_qParam`: `xFun (e^{2πiτ}) = x(τ)`: the evaluated q-series of the C1 measure is the actual
  modular coordinate (Mathlib's `hasSum_qExpansion` and `etaCoordinate_qExpansion`).
* `xFun_ne_zero`: `xFun q ≠ 0` for `0 < |q| < 1`.
* `deriv_Xf_eq`: `X'(z) = xFun'(q) · 2πi q` for `q = e^{2πiz}`.
* `mobC`, `Xf_mob`, `deriv_Xf_mob`: for `γ ∈ Γ₀(7)`, `X(γz) = X(z)` and
  `X'(γz) = X'(z) (cz + d)²`. -/
noncomputable section
set_option autoImplicit false
namespace Zeta7Valence
open Complex Filter Topology Zeta7LevelSeven Zeta7Arch ModularForm Function
open UpperHalfPlane hiding I
open scoped MatrixGroups

theorem etaCoordinate_bdd : IsBoundedAtImInfty etaCoordinate :=
  Filter.ZeroAtFilter.boundedAtFilter etaCoordinate_tendsto

/-- **The q-series coordinate is the modular coordinate.** -/
theorem xFun_qParam (τ : ℍ) : xFun (Periodic.qParam 1 τ) = etaCoordinate τ := by
  have h := hasSum_qExpansion (h := 1) one_pos etaCoordinate_periodic etaCoordinate_holo
    etaCoordinate_bdd τ
  rw [etaCoordinate_qExpansion] at h
  rw [← h.tsum_eq, xFun, evalQ]
  congr 1

theorem Xf_qParam {z : ℂ} (hz : 0 < z.im) : Xf z = xFun (Periodic.qParam 1 z) := by
  have := xFun_qParam ⟨z, hz⟩
  rw [← Xf_eq] at this
  exact this.symm

theorem invQParam_im_pos {q : ℂ} (hq0 : q ≠ 0) (hq1 : ‖q‖ < 1) :
    0 < (Periodic.invQParam 1 q).im := by
  rw [Periodic.im_invQParam]
  have hl : Real.log ‖q‖ < 0 := Real.log_neg (norm_pos_iff.mpr hq0) hq1
  have : 0 < -1 / (2 * Real.pi) * Real.log ‖q‖ := by
    have hp : 0 < 2 * Real.pi := by positivity
    rw [div_mul_eq_mul_div, lt_div_iff₀ hp]
    linarith
  exact this

theorem xFun_ne_zero {q : ℂ} (hq0 : q ≠ 0) (hq1 : ‖q‖ < 1) : xFun q ≠ 0 := by
  have hpos := invQParam_im_pos hq0 hq1
  have h := Xf_qParam hpos
  rw [Periodic.qParam_right_inv one_ne_zero hq0] at h
  rw [← h]
  exact Xf_ne_zero hpos

theorem hasDerivAt_qParam (z : ℂ) :
    HasDerivAt (Periodic.qParam 1) (2 * Real.pi * I * Periodic.qParam 1 z) z := by
  have h1 : HasDerivAt (fun w : ℂ => 2 * (Real.pi : ℂ) * I * w / ((1 : ℝ) : ℂ))
      (2 * (Real.pi : ℂ) * I * 1 / ((1 : ℝ) : ℂ)) z :=
    ((hasDerivAt_id z).const_mul (2 * (Real.pi : ℂ) * I)).div_const _
  refine h1.cexp.congr_deriv ?_
  simp only [Periodic.qParam, Complex.ofReal_one, div_one, mul_one]
  ring

/-- `X'(z) = xFun'(q) · 2πi q`. -/
theorem deriv_Xf_eq {z : ℂ} (hz : 0 < z.im) :
    deriv Xf z = deriv xFun (Periodic.qParam 1 z) * (2 * Real.pi * I * Periodic.qParam 1 z) := by
  have hq1 : ‖Periodic.qParam 1 z‖ < 1 := Periodic.norm_qParam_lt_one one_pos hz
  have hev : Xf =ᶠ[𝓝 z] xFun ∘ Periodic.qParam 1 := by
    filter_upwards [Hset_isOpen.mem_nhds hz] with w hw
    exact Xf_qParam hw
  rw [hev.deriv_eq]
  have hx : HasDerivAt xFun (deriv xFun (Periodic.qParam 1 z)) (Periodic.qParam 1 z) :=
    (xFun_analytic _ (by simpa using hq1)).differentiableAt.hasDerivAt
  exact (hx.comp z (hasDerivAt_qParam z)).deriv

/-! ### Möbius transformations -/

/-- `z ↦ (az + b)/(cz + d)` on `ℂ`. -/
def mobC (γ : SL(2, ℤ)) (z : ℂ) : ℂ := ((γ 0 0 : ℂ) * z + γ 0 1) / ((γ 1 0 : ℂ) * z + γ 1 1)

theorem mob_coe (γ : SL(2, ℤ)) (τ : ℍ) : ((γ • τ : ℍ) : ℂ) = mobC γ τ := by
  rw [coe_specialLinearGroup_apply, mobC]
  simp

theorem denom_ne {γ : SL(2, ℤ)} {z : ℂ} (hz : 0 < z.im) : (γ 1 0 : ℂ) * z + γ 1 1 ≠ 0 := by
  have h := UpperHalfPlane.denom_ne_zero γ ⟨z, hz⟩
  simpa [UpperHalfPlane.denom] using h

theorem mob_im_pos {γ : SL(2, ℤ)} {z : ℂ} (hz : 0 < z.im) : 0 < (mobC γ z).im := by
  rw [← mob_coe γ ⟨z, hz⟩]
  exact (γ • (⟨z, hz⟩ : ℍ)).im_pos

theorem Xf_mob {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma0 7) {z : ℂ} (hz : 0 < z.im) :
    Xf (mobC γ z) = Xf z := by
  have h := x_gamma γ hγ ⟨z, hz⟩
  rw [← Xf_eq, ← Xf_eq, mob_coe] at h
  exact h

theorem hasDerivAt_mob (γ : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im) :
    HasDerivAt (mobC γ) (1 / ((γ 1 0 : ℂ) * z + γ 1 1) ^ 2) z := by
  have hd := denom_ne (γ := γ) hz
  have hdet : (γ 0 0 : ℂ) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.2
    rw [Matrix.det_fin_two] at this
    exact_mod_cast this
  have h := (((hasDerivAt_id z).const_mul (γ 0 0 : ℂ)).add_const (γ 0 1 : ℂ)).div
    (((hasDerivAt_id z).const_mul (γ 1 0 : ℂ)).add_const (γ 1 1 : ℂ)) hd
  unfold mobC
  refine h.congr_deriv ?_
  simp only [id, mul_one]
  congr 1
  linear_combination hdet

/-- `X'(γz) = X'(z) (cz + d)²` for `γ ∈ Γ₀(7)`. -/
theorem deriv_Xf_mob {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma0 7) {z : ℂ}
    (hz : 0 < z.im) :
    deriv Xf (mobC γ z) = deriv Xf z * ((γ 1 0 : ℂ) * z + γ 1 1) ^ 2 := by
  have hd := denom_ne (γ := γ) hz
  have hmob := hasDerivAt_mob γ hz
  have hX : HasDerivAt Xf (deriv Xf (mobC γ z)) (mobC γ z) :=
    (Xf_differentiableOn.differentiableAt (Hset_isOpen.mem_nhds (mob_im_pos hz))).hasDerivAt
  have hcomp := hX.comp z hmob
  have hev : Xf ∘ mobC γ =ᶠ[𝓝 z] Xf := by
    filter_upwards [Hset_isOpen.mem_nhds hz] with w hw
    exact Xf_mob hγ hw
  have h1 := hcomp.deriv
  rw [hev.deriv_eq] at h1
  rw [h1]
  field_simp

end Zeta7Valence

import Zeta7Proof.PNT.Sobolev

/- Ported from PrimeNumberTheoremAnd (https://github.com/AlexKontorovich/PrimeNumberTheoremAnd),
commit a5040887e6bb24f7c201db8568e7755c138b3878, Apache License 2.0
(see reference/pnt_audit_20260916/LICENSE). Adapted to the pinned Mathlib; declarations are
placed in the namespace `Zeta7PNT`. -/

noncomputable section

namespace Zeta7PNT


/-! ### Compatibility layer for the Fourier transform API of the pinned Mathlib

The ported source used `𝓕` for `Real.fourierIntegral` on functions `ℝ → ℂ`. The pinned Mathlib
provides the typeclass `FourierTransform`; `FT` is its instance on `ℝ → ℂ`, and the notation `𝓕`
below refers to it, so that `W21`, `CS` and Schwartz functions coerce as in the source. -/

/-- The Fourier transform of a function `ℝ → ℂ`. -/
def FT (f : ℝ → ℂ) : ℝ → ℂ := FourierTransform.fourier f

scoped notation "𝓕" => FT

theorem FT_eq_vector (f : ℝ → ℂ) :
    FT f = VectorFourier.fourierIntegral Real.fourierChar MeasureTheory.volume
      (innerₗ ℝ) f := rfl

theorem fourierIntegral_real_eq (f : ℝ → ℂ) (w : ℝ) :
    FT f w = ∫ v, Real.fourierChar (-(v * w)) • f v := _root_.Real.fourier_real_eq f w

theorem fourierIntegral_eq (f : ℝ → ℂ) (w : ℝ) :
    FT f w = ∫ v, Real.fourierChar (-(inner ℝ v w)) • f v := _root_.Real.fourier_eq f w

theorem fourierIntegral_eq' (f : ℝ → ℂ) (w : ℝ) :
    FT f w = ∫ v, Complex.exp ((↑(-2 * Real.pi * inner ℝ v w) * Complex.I)) • f v :=
  _root_.Real.fourier_eq' f w

theorem fourierIntegral_deriv' {f : ℝ → ℂ} (hf : MeasureTheory.Integrable f)
    (h'f : Differentiable ℝ f) (hf' : MeasureTheory.Integrable (deriv f)) :
    FT (deriv f) = fun x : ℝ ↦ (2 * Real.pi * Complex.I * x) • (FT f x) :=
  _root_.Real.fourier_deriv hf h'f hf'

theorem zero_at_infty_fourierIntegral (f : ℝ → ℂ) :
    Filter.Tendsto (FT f) (Filter.cocompact ℝ) (nhds 0) :=
  _root_.Real.zero_at_infty_fourier f


open Real Complex MeasureTheory Filter Topology BoundedContinuousFunction SchwartzMap VectorFourier BigOperators

local instance {E : Type*} : Coe (E → ℝ) (E → ℂ) := ⟨fun f n => f n⟩

section lemmas

@[simp]
theorem nnnorm_eq_of_mem_circle (z : Circle) : ‖z.val‖₊ = 1 := NNReal.coe_eq_one.mp (by simp [Circle.norm_coe])

@[simp]
theorem nnnorm_circle_smul (z : Circle) (s : ℂ) : ‖z • s‖₊ = ‖s‖₊ := by
  simp [show z • s = z.val * s from rfl]

noncomputable def e (u : ℝ) : ℝ →ᵇ ℂ where
  toFun v := Real.fourierChar (-v * u)
  map_bounded' := ⟨2, fun x y => (dist_le_norm_add_norm _ _).trans (by simp [Circle.norm_coe]; norm_num)⟩

@[simp] lemma e_apply (u : ℝ) (v : ℝ) : e u v = Real.fourierChar (-v * u) := rfl

theorem hasDerivAt_e {u x : ℝ} : HasDerivAt (e u) (-2 * π * u * I * e u x) x := by
  have l2 : HasDerivAt (fun v => -v * u) (-u) x := by simpa only [neg_mul_comm] using hasDerivAt_mul_const (-u)
  refine ((hasDerivAt_fourierChar (-x * u)).scomp x l2).congr_deriv ?_
  simp ; ring

lemma fourierIntegral_deriv_aux2 (e : ℝ →ᵇ ℂ) {f : ℝ → ℂ} (hf : Integrable f) : Integrable (⇑e * f) :=
  hf.bdd_mul e.continuous.aestronglyMeasurable (Filter.Eventually.of_forall e.norm_coe_le_norm)

@[simp] lemma F_neg {f : ℝ → ℂ} {u : ℝ} : 𝓕 (fun x => -f x) u = - 𝓕 f u := by
  simp [fourierIntegral_eq, integral_neg]

@[simp] lemma F_add {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (x : ℝ) :
    𝓕 (fun x => f x + g x) x = 𝓕 f x + 𝓕 g x := by
  have : Continuous fun p : ℝ × ℝ ↦ ((innerₗ ℝ) p.1) p.2 := continuous_inner
  have := fourierIntegral_add continuous_fourierChar this hf hg
  exact congr_fun this x

@[simp] lemma F_sub {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (x : ℝ) :
    𝓕 (fun x => f x - g x) x = 𝓕 f x - 𝓕 g x := by
  simp_rw [sub_eq_add_neg] ; rw [F_add] ; simp ; exact hf ; exact hg.neg

@[simp] lemma F_mul {f : ℝ → ℂ} {c : ℂ} {u : ℝ} : 𝓕 (fun x => c * f x) u = c * 𝓕 f u := by
  simp [fourierIntegral_real_eq, ← integral_const_mul] ; congr ; ext
  simp [Real.fourierChar, Circle.exp, ← smul_mul_assoc, mul_smul_comm]

end lemmas

theorem fourierIntegral_self_add_deriv_deriv (f : W21) (u : ℝ) :
    (1 + u ^ 2) * 𝓕 f u = 𝓕 (fun u => f u - (1 / (4 * π ^ 2)) * deriv^[2] f u) u := by
  have l1 : Integrable (fun x => (((π : ℂ) ^ 2)⁻¹ * 4⁻¹) * deriv (deriv f) x) := by
    apply Integrable.const_mul ; simpa [iteratedDeriv_succ] using f.integrable le_rfl
  have l4 : Differentiable ℝ f := f.differentiable
  have l5 : Differentiable ℝ (deriv f) := f.deriv.differentiable
  simp [f.hf, l1, add_mul, fourierIntegral_deriv' f.hf' l5 f.hf'', fourierIntegral_deriv' f.hf l4 f.hf']
  field_simp [pi_ne_zero] ; ring_nf ; simp

@[simp] lemma deriv_ofReal : deriv ofReal = fun _ => 1 := by
  ext x ; exact ((hasDerivAt_id x).ofReal_comp).deriv

end Zeta7PNT

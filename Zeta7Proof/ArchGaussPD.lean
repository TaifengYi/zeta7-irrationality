import Mathlib

/-! C3, step 4: the Gaussian kernel is positive definite on differences of finite measures.

For `c > 0`, `g(w) = e^{-c|w|²}` satisfies, for all finite measures `α, β` on `ℂ`,

`∬ g(x-y) dα dα - ∬ g(x-y) dα dβ - ∬ g(x-y) dβ dα + ∬ g(x-y) dβ dβ ≥ 0`.

Proof: `g(w) = (4πc)⁻¹ ∫ e^{-|ξ|²/(4c) + i⟨w, ξ⟩} dξ` (Mathlib's Gaussian integral
`integral_cexp_neg_mul_sq_norm_add` on the real inner product space `ℂ ≅ ℝ²`), and by Fubini
`∬ g(x-y) dα(x) dβ(y) = (4πc)⁻¹ ∫ e^{-|ξ|²/(4c)} F_α(ξ) conj(F_β(ξ)) dξ` with
`F_α(ξ) = ∫ e^{i⟨x, ξ⟩} dα(x)`. The quadratic form is `(4πc)⁻¹ ∫ e^{-|ξ|²/(4c)} |F_α - F_β|² dξ`. -/
noncomputable section
set_option autoImplicit false
namespace Zeta7Arch
open MeasureTheory Complex ComplexConjugate Real

/-- `B_k(α, β) = ∫∫ k(x - y) dβ(y) dα(x)`. -/
def kernelPair (k : ℂ → ℝ) (α β : Measure ℂ) : ℝ := ∫ x, ∫ y, k (x - y) ∂β ∂α

/-- The quadratic form of `α - β` for the kernel `k`. -/
def kernelDiffEnergy (k : ℂ → ℝ) (α β : Measure ℂ) : ℝ :=
  kernelPair k α α - kernelPair k α β - kernelPair k β α + kernelPair k β β

/-- The Gaussian `e^{-c|w|²}`. -/
def gaussK (c : ℝ) (w : ℂ) : ℝ := Real.exp (-c * ‖w‖ ^ 2)

/-- The characteristic function `F_α(ξ) = ∫ e^{i⟨x, ξ⟩} dα(x)`. -/
def charFun (α : Measure ℂ) (ξ : ℂ) : ℂ := ∫ x, cexp (I * (inner ℝ x ξ : ℝ)) ∂α

theorem finrank_real_complex' : (Module.finrank ℝ ℂ : ℂ) / 2 = 1 := by
  rw [Complex.finrank_real_complex]; norm_num

/-- The Fourier representation of the Gaussian. -/
theorem gaussK_repr {c : ℝ} (hc : 0 < c) (w : ℂ) :
    (gaussK c w : ℂ) = (4 * π * c : ℂ)⁻¹ *
      ∫ ξ : ℂ, cexp (-((4 * c : ℝ) : ℂ)⁻¹ * ‖ξ‖ ^ 2 + I * (inner ℝ w ξ : ℝ)) := by
  have hb : 0 < (-(-((4 * c : ℝ) : ℂ)⁻¹)).re := by
    simp only [neg_neg, ← Complex.ofReal_inv, Complex.ofReal_re]
    positivity
  have h := GaussianFourier.integral_cexp_neg_mul_sq_norm_add hb I w
  simp only [neg_neg] at h
  rw [show (fun ξ : ℂ => cexp (-((4 * c : ℝ) : ℂ)⁻¹ * ‖ξ‖ ^ 2 + I * (inner ℝ w ξ : ℝ))) =
    fun ξ : ℂ => cexp (-(((4 * c : ℝ) : ℂ)⁻¹) * ‖ξ‖ ^ 2 + I * (inner ℝ w ξ : ℝ)) from rfl, h,
    finrank_real_complex', Complex.cpow_one]
  have h4c : ((4 * c : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (4 * c : ℝ) ≠ 0)
  rw [gaussK, Complex.ofReal_exp]
  have hI : I ^ 2 * (‖w‖ : ℂ) ^ 2 / (4 * ((4 * c : ℝ) : ℂ)⁻¹) = ((-c * ‖w‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.I_sq]
    push_cast
    field_simp
  rw [hI]
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
  push_cast
  field_simp

/-! ### Fubini representation -/

section Fubini

variable {c : ℝ} (hc : 0 < c) (α β : Measure ℂ) [IsFiniteMeasure α] [IsFiniteMeasure β]
include hc

/-- The Gaussian weight `e^{-|ξ|²/(4c)}`. -/
def gaussW (c : ℝ) (ξ : ℂ) : ℝ := Real.exp (-(4 * c)⁻¹ * ‖ξ‖ ^ 2)

omit [IsFiniteMeasure α] [IsFiniteMeasure β] in
theorem gaussW_integrable : Integrable (gaussW c) := by
  have hb : 0 < (((4 * c)⁻¹ : ℝ) : ℂ).re := by
    rw [Complex.ofReal_re]; positivity
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add hb 0 (0 : ℂ)).norm
  refine h.congr (Filter.Eventually.of_forall fun ξ => ?_)
  simp only [gaussW, zero_mul, add_zero, Complex.norm_exp]
  congr 1
  simp [← Complex.ofReal_pow]

omit hc [IsFiniteMeasure β] in
theorem norm_charFun_le (ξ : ℂ) : ‖charFun α ξ‖ ≤ α.real Set.univ := by
  refine (norm_integral_le_of_norm_le_const (C := 1)
    (Filter.Eventually.of_forall fun x => ?_)).trans (by simp)
  rw [mul_comm, norm_exp_ofReal_mul_I]

omit hc [IsFiniteMeasure β] in
theorem charFun_continuous : Continuous (charFun α) := by
  refine continuous_of_dominated (bound := fun _ => 1) (fun ξ => ?_) (fun ξ => ?_)
    (integrable_const 1) (Filter.Eventually.of_forall fun x => ?_)
  · exact (by fun_prop : Continuous fun x : ℂ => cexp (I * (inner ℝ x ξ : ℝ))).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun x => by rw [mul_comm, norm_exp_ofReal_mul_I]
  · fun_prop

omit hc [IsFiniteMeasure α] [IsFiniteMeasure β] in
/-- The integrand `e^{-|ξ|²/(4c)} e^{i⟨x,ξ⟩} conj e^{i⟨y,ξ⟩}`. -/
theorem gauss_factor (x y ξ : ℂ) :
    cexp (-((4 * c : ℝ) : ℂ)⁻¹ * ‖ξ‖ ^ 2 + I * (inner ℝ (x - y) ξ : ℝ)) =
      (gaussW c ξ : ℂ) * (cexp (I * (inner ℝ x ξ : ℝ)) * conj (cexp (I * (inner ℝ y ξ : ℝ)))) := by
  rw [← Complex.exp_conj, map_mul, Complex.conj_I, Complex.conj_ofReal, gaussW,
    Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add, inner_sub_left]
  congr 1
  push_cast
  ring

theorem kernelPair_gauss_repr :
    (kernelPair (gaussK c) α β : ℂ) =
      (4 * π * c : ℂ)⁻¹ * ∫ ξ, (gaussW c ξ : ℂ) * (charFun α ξ * conj (charFun β ξ)) := by
  have hγ := gaussW_integrable hc
  set H : ℂ → ℂ → ℂ → ℂ := fun x y ξ =>
    (gaussW c ξ : ℂ) * (cexp (I * (inner ℝ x ξ : ℝ)) * conj (cexp (I * (inner ℝ y ξ : ℝ))))
    with hH
  have hHc : Continuous fun p : ℂ × ℂ × ℂ => H p.1 p.2.1 p.2.2 := by
    simp only [hH, gaussW]; fun_prop
  have hHnorm : ∀ x y ξ, ‖H x y ξ‖ = gaussW c ξ := by
    intro x y ξ
    simp only [hH, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), gaussW]
    rw [mul_comm I, norm_exp_ofReal_mul_I, mul_comm I, norm_exp_ofReal_mul_I, mul_one, mul_one]
  have hstep1 : ∀ x : ℂ, ∫ y, ∫ ξ, H x y ξ ∂volume ∂β = ∫ ξ, ∫ y, H x y ξ ∂β ∂volume := by
    intro x
    apply integral_integral_swap
    refine Integrable.mono' ((integrable_const (1 : ℝ)).mul_prod hγ) ?_ ?_
    · exact (hHc.comp (by fun_prop : Continuous fun p : ℂ × ℂ => (x, p.1, p.2))).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun p => ?_
      obtain ⟨y, ξ⟩ := p
      simp only [Function.uncurry_apply_pair, one_mul]
      exact (hHnorm x y ξ).le
  have hinner : ∀ x ξ : ℂ, ∫ y, H x y ξ ∂β =
      (gaussW c ξ : ℂ) * (cexp (I * (inner ℝ x ξ : ℝ)) * conj (charFun β ξ)) := by
    intro x ξ
    simp only [hH]
    rw [integral_const_mul, integral_const_mul, charFun, integral_conj]
  have hΦc : Continuous fun p : ℂ × ℂ =>
      (gaussW c p.2 : ℂ) * (cexp (I * (inner ℝ p.1 p.2 : ℝ)) * conj (charFun β p.2)) := by
    have := charFun_continuous β
    simp only [gaussW]; fun_prop
  have hstep2 : ∫ x, ∫ ξ, (gaussW c ξ : ℂ) * (cexp (I * (inner ℝ x ξ : ℝ)) * conj (charFun β ξ))
      ∂volume ∂α = ∫ ξ, ∫ x, (gaussW c ξ : ℂ) * (cexp (I * (inner ℝ x ξ : ℝ)) *
        conj (charFun β ξ)) ∂α ∂volume := by
    apply integral_integral_swap
    refine Integrable.mono' ((integrable_const (β.real Set.univ)).mul_prod hγ)
      hΦc.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun p => ?_
    obtain ⟨x, ξ⟩ := p
    simp only [Function.uncurry_apply_pair]
    rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs, gaussW,
      abs_of_pos (Real.exp_pos _), mul_comm I, norm_exp_ofReal_mul_I, one_mul]
    have := norm_charFun_le β ξ
    have h0 : 0 ≤ Real.exp (-(4 * c)⁻¹ * ‖ξ‖ ^ 2) := (Real.exp_pos _).le
    nlinarith
  have e1 : (kernelPair (gaussK c) α β : ℂ) = ∫ x, ∫ y, (gaussK c (x - y) : ℂ) ∂β ∂α := by
    rw [kernelPair, ← integral_complex_ofReal]
    congr 1; funext x
    rw [integral_complex_ofReal]
  have e2 : ∀ x y : ℂ, (gaussK c (x - y) : ℂ) = (4 * π * c : ℂ)⁻¹ * ∫ ξ, H x y ξ := by
    intro x y
    rw [gaussK_repr hc]
    congr 1
    congr 1; funext ξ
    exact gauss_factor x y ξ
  have e3 : ∀ x : ℂ, ∫ y, (gaussK c (x - y) : ℂ) ∂β = (4 * π * c : ℂ)⁻¹ *
      ∫ ξ, (gaussW c ξ : ℂ) * (cexp (I * (inner ℝ x ξ : ℝ)) * conj (charFun β ξ)) := by
    intro x
    simp_rw [e2 x]
    rw [integral_const_mul, hstep1 x]
    congr 1; congr 1; funext ξ; exact hinner x ξ
  rw [e1]
  simp_rw [e3]
  rw [integral_const_mul, hstep2]
  congr 1; congr 1; funext ξ
  rw [integral_const_mul, integral_mul_const]
  rfl

end Fubini

/-! ### Positive definiteness -/

theorem integrable_gaussW_mul {c : ℝ} (hc : 0 < c) {G : ℂ → ℂ} (hG : Continuous G) {K : ℝ}
    (hK : ∀ ξ, ‖G ξ‖ ≤ K) : Integrable (fun ξ => (gaussW c ξ : ℂ) * G ξ) := by
  refine Integrable.mono' ((gaussW_integrable hc).mul_const K)
    (by simp only [gaussW]; fun_prop) (Filter.Eventually.of_forall fun ξ => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, gaussW, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_left (hK ξ) (Real.exp_pos _).le

/-- **The Gaussian kernel is positive definite**: `∬ e^{-c|x-y|²} d(α-β) d(α-β) ≥ 0`. -/
theorem gauss_pd {c : ℝ} (hc : 0 < c) (α β : Measure ℂ) [IsFiniteMeasure α]
    [IsFiniteMeasure β] : 0 ≤ kernelDiffEnergy (gaussK c) α β := by
  set Fa := charFun α
  set Fb := charFun β
  have hFa := charFun_continuous α
  have hFb := charFun_continuous β
  have hba := norm_charFun_le α
  have hbb := norm_charFun_le β
  have hint : ∀ (F G : ℂ → ℂ), Continuous F → Continuous G → (∀ ξ, ‖F ξ‖ ≤ α.real Set.univ +
      β.real Set.univ) → (∀ ξ, ‖G ξ‖ ≤ α.real Set.univ + β.real Set.univ) →
      Integrable (fun ξ => (gaussW c ξ : ℂ) * (F ξ * conj (G ξ))) := by
    intro F G hF hG hFb' hGb'
    refine integrable_gaussW_mul hc (by fun_prop) (K := (α.real Set.univ + β.real Set.univ) ^ 2)
      fun ξ => ?_
    rw [norm_mul, Complex.norm_conj, sq]
    exact mul_le_mul (hFb' ξ) (hGb' ξ) (norm_nonneg _) (by positivity)
  have hA0 : 0 ≤ α.real Set.univ := measureReal_nonneg
  have hB0 : 0 ≤ β.real Set.univ := measureReal_nonneg
  have bA : ∀ ξ, ‖Fa ξ‖ ≤ α.real Set.univ + β.real Set.univ := fun ξ => by linarith [hba ξ]
  have bB : ∀ ξ, ‖Fb ξ‖ ≤ α.real Set.univ + β.real Set.univ := fun ξ => by linarith [hbb ξ]
  have key : (kernelDiffEnergy (gaussK c) α β : ℂ) =
      (((4 * π * c)⁻¹ * ∫ ξ, gaussW c ξ * ‖Fa ξ - Fb ξ‖ ^ 2 : ℝ) : ℂ) := by
    have i1 := hint Fa Fa hFa hFa bA bA
    have i2 := hint Fa Fb hFa hFb bA bB
    have i3 := hint Fb Fa hFb hFa bB bA
    have i4 := hint Fb Fb hFb hFb bB bB
    have hsum : ∫ ξ, ((gaussW c ξ : ℂ) * (Fa ξ * conj (Fa ξ)) -
        (gaussW c ξ : ℂ) * (Fa ξ * conj (Fb ξ)) - (gaussW c ξ : ℂ) * (Fb ξ * conj (Fa ξ)) +
        (gaussW c ξ : ℂ) * (Fb ξ * conj (Fb ξ))) =
        (∫ ξ, (gaussW c ξ : ℂ) * (Fa ξ * conj (Fa ξ))) -
          (∫ ξ, (gaussW c ξ : ℂ) * (Fa ξ * conj (Fb ξ))) -
          (∫ ξ, (gaussW c ξ : ℂ) * (Fb ξ * conj (Fa ξ))) +
          (∫ ξ, (gaussW c ξ : ℂ) * (Fb ξ * conj (Fb ξ))) := by
      have i12 : Integrable (fun ξ => (gaussW c ξ : ℂ) * (Fa ξ * conj (Fa ξ)) -
          (gaussW c ξ : ℂ) * (Fa ξ * conj (Fb ξ))) := i1.sub i2
      have i123 : Integrable (fun ξ => (gaussW c ξ : ℂ) * (Fa ξ * conj (Fa ξ)) -
          (gaussW c ξ : ℂ) * (Fa ξ * conj (Fb ξ)) - (gaussW c ξ : ℂ) * (Fb ξ * conj (Fa ξ))) :=
        i12.sub i3
      rw [integral_add i123 i4, integral_sub i12 i3, integral_sub i1 i2]
    rw [kernelDiffEnergy]
    push_cast
    rw [kernelPair_gauss_repr hc α α, kernelPair_gauss_repr hc α β, kernelPair_gauss_repr hc β α,
      kernelPair_gauss_repr hc β β]
    have e : ∀ A B C D : ℂ, (4 * π * c : ℂ)⁻¹ * A - (4 * π * c : ℂ)⁻¹ * B -
        (4 * π * c : ℂ)⁻¹ * C + (4 * π * c : ℂ)⁻¹ * D = (4 * π * c : ℂ)⁻¹ * (A - B - C + D) := by
      intros; ring
    rw [e, ← hsum, ← integral_complex_ofReal]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    simp only
    rw [Complex.ofReal_mul, Complex.ofReal_pow, ← Complex.mul_conj', map_sub]
    ring
  have hreal : kernelDiffEnergy (gaussK c) α β =
      (4 * π * c)⁻¹ * ∫ ξ, gaussW c ξ * ‖Fa ξ - Fb ξ‖ ^ 2 := by exact_mod_cast key
  rw [hreal]
  exact mul_nonneg (by positivity) (integral_nonneg fun ξ =>
    mul_nonneg (Real.exp_pos _).le (sq_nonneg _))

end Zeta7Arch

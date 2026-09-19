import Zeta7Proof.ArchAndreief
import Zeta7Proof.ArchC2Endpoint

/-! C3, step 2: the Gram/Vandermonde identity (42) for the actual weighted Gram matrix.

`gramMeasure d = e^{-2dU} dA` on `𝒦` is a finite measure, and the Gram matrix of
`1, z, …, z^{d-1}` for the norm (39) is `weightedGram d 𝒦 e^{-2dU}`. With `φ_a = z̄^a`,
`ψ_b = z^b`, Andréief's identity and the Vandermonde determinant give

`d! · det G_d = ∫ ∏_{i<j} |z_j - z_i|² d(gramMeasure d)^{⊗d}(z)`,

that is, (42): `det G_d = (1/d!) ∫_{𝒦^d} ∏_{i<j} |z_i - z_j|² e^{-2d Σ_i U(z_i)} ∏ dA(z_i)`,
with the product-density form proved in `pi_gramMeasure` below. -/
noncomputable section
set_option autoImplicit false
namespace Zeta7Arch
open MeasureTheory Matrix ComplexConjugate

/-- The weighted area measure `e^{-2dU} dA` on `𝒦`. -/
def gramMeasure (d : ℕ) : Measure ℂ :=
  (volume.restrict discK).withDensity fun z => ENNReal.ofReal (gramWeight d z)

theorem gramWeight_integrableOn (d : ℕ) : IntegrableOn (gramWeight d) discK :=
  (gramWeight_continuous d).continuousOn.integrableOn_compact isCompact_discK

instance gramMeasure_isFinite (d : ℕ) : IsFiniteMeasure (gramMeasure d) :=
  isFiniteMeasure_withDensity_ofReal (gramWeight_integrableOn d).hasFiniteIntegral

theorem ae_gramMeasure_mem (d : ℕ) : ∀ᵐ z ∂gramMeasure d, z ∈ discK :=
  (withDensity_absolutelyContinuous _ _) (ae_restrict_mem measurableSet_closedBall)

theorem integral_gramMeasure (d : ℕ) (g : ℂ → ℂ) :
    ∫ z, g z ∂gramMeasure d = ∫ z in discK, (gramWeight d z : ℂ) * g z := by
  have hmeas : Measurable fun z => (gramWeight d z).toNNReal :=
    (gramWeight_continuous d).measurable.real_toNNReal
  rw [gramMeasure, show (fun z => ENNReal.ofReal (gramWeight d z)) =
      fun z => (((gramWeight d z).toNNReal : NNReal) : ENNReal) from rfl,
    integral_withDensity_eq_integral_smul hmeas]
  refine setIntegral_congr_fun measurableSet_closedBall fun z _ => ?_
  rw [NNReal.smul_def, Real.coe_toNNReal _ (gramWeight_pos d z).le, Complex.real_smul]

/-- The monomial functions `φ_a = z̄^a`, `ψ_b = z^b`. -/
def conjMono (d : ℕ) : Fin d → ℂ → ℂ := fun a z => conj z ^ (a : ℕ)
def mono (d : ℕ) : Fin d → ℂ → ℂ := fun b z => z ^ (b : ℕ)

theorem pairMatrix_eq_weightedGram (d : ℕ) :
    pairMatrix (gramMeasure d) (conjMono d) (mono d) = weightedGram d discK (gramWeight d) := by
  ext a b
  rw [pairMatrix, integral_gramMeasure]
  rfl

theorem integrable_mono_pair (d : ℕ) (a b : Fin d) :
    Integrable (fun z => conjMono d a z * mono d b z) (gramMeasure d) := by
  have hc : Continuous fun z => conjMono d a z * mono d b z := by unfold conjMono mono; fun_prop
  refine Integrable.of_bound hc.aestronglyMeasurable ((supR + 1) ^ ((a : ℕ) + b)) ?_
  filter_upwards [ae_gramMeasure_mem d] with z hz
  have hzn : ‖z‖ ≤ supR + 1 := by
    rw [discK, Metric.mem_closedBall, dist_zero_right] at hz; exact hz
  simp only [conjMono, mono, norm_mul, norm_pow, Complex.norm_conj]
  rw [← pow_add]
  exact pow_le_pow_left₀ (norm_nonneg _) hzn _

theorem evalMatrix_mono (d : ℕ) (z : Fin d → ℂ) :
    evalMatrix (mono d) z = (vandermonde z)ᵀ := by
  ext a b; simp [evalMatrix, mono, vandermonde_apply]

theorem evalMatrix_conjMono (d : ℕ) (z : Fin d → ℂ) :
    evalMatrix (conjMono d) z = (evalMatrix (mono d) z).map (starRingEnd ℂ) := by
  ext a b; simp [evalMatrix, conjMono, mono, map_pow]

/-- `det Φ(z) · det Ψ(z) = ∏_{i<j} |z_j - z_i|²`. -/
theorem det_conj_mul_det (d : ℕ) (z : Fin d → ℂ) :
    (evalMatrix (conjMono d) z).det * (evalMatrix (mono d) z).det =
      ((∏ i : Fin d, ∏ j ∈ Finset.Ioi i, ‖z j - z i‖ ^ 2 : ℝ) : ℂ) := by
  have hmap : ((evalMatrix (mono d) z).map (starRingEnd ℂ)).det =
      starRingEnd ℂ (evalMatrix (mono d) z).det := by
    rw [RingHom.map_det]; rfl
  rw [evalMatrix_conjMono, hmap, evalMatrix_mono, det_transpose, det_vandermonde,
    Complex.conj_mul', ← Complex.ofReal_pow, norm_prod, ← Finset.prod_pow]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [norm_prod, ← Finset.prod_pow]

/-- **The Gram/Vandermonde identity (42).** -/
theorem gram_vandermonde (d : ℕ) :
    (d.factorial : ℂ) * (weightedGram d discK (gramWeight d)).det =
      ∫ z : Fin d → ℂ, ((∏ i : Fin d, ∏ j ∈ Finset.Ioi i, ‖z j - z i‖ ^ 2 : ℝ) : ℂ)
        ∂(Measure.pi fun _ : Fin d => gramMeasure d) := by
  rw [← pairMatrix_eq_weightedGram,
    andreief (gramMeasure d) (conjMono d) (mono d) (integrable_mono_pair d)]
  exact integral_congr_ae (Filter.Eventually.of_forall fun z => det_conj_mul_det d z)

/-- The real form: `det G_d = (1/d!) ∫ ∏_{i<j} |z_j - z_i|² dν_d^{⊗d}`. -/
theorem gram_det_eq_integral (d : ℕ) :
    (weightedGram d discK (gramWeight d)).det =
      (((d.factorial : ℝ)⁻¹ * ∫ z : Fin d → ℂ, ∏ i : Fin d, ∏ j ∈ Finset.Ioi i, ‖z j - z i‖ ^ 2
        ∂(Measure.pi fun _ : Fin d => gramMeasure d) : ℝ) : ℂ) := by
  have h := gram_vandermonde d
  rw [integral_complex_ofReal] at h
  have hf : (d.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos d).ne'
  rw [Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_natCast, ← h]
  field_simp

/-! ### The product-density form of (42) -/

instance restrictDiscK_isFinite : IsFiniteMeasure (volume.restrict discK) :=
  isFiniteMeasure_restrict.mpr isCompact_discK.measure_lt_top.ne

theorem gramWeight_integrable_restrict (d : ℕ) :
    Integrable (gramWeight d) (volume.restrict discK) := gramWeight_integrableOn d

theorem prod_gramWeight_eq_exp (d : ℕ) (z : Fin d → ℂ) :
    ∏ i, gramWeight d (z i) = Real.exp (-(2 * d) * ∑ i, potentialU (z i)) := by
  rw [Finset.mul_sum, Real.exp_sum]
  rfl

/-- **The product-density form**: `ν_d^{⊗d}` is the measure `e^{-2d Σ U(z_i)} ∏ dA(z_i)` on `𝒦^d`. -/
theorem pi_gramMeasure (d : ℕ) :
    Measure.pi (fun _ : Fin d => gramMeasure d) =
      (Measure.pi fun _ : Fin d => volume.restrict discK).withDensity
        fun z => ENNReal.ofReal (∏ i, gramWeight d (z i)) := by
  have hwm : Measurable (gramWeight d) := (gramWeight_continuous d).measurable
  have hw0 : ∀ z, 0 ≤ gramWeight d z := fun z => (gramWeight_pos d z).le
  have hint := gramWeight_integrable_restrict d
  refine Measure.pi_eq fun s hs => ?_
  have hbox : MeasurableSet (Set.univ.pi s) := MeasurableSet.univ_pi hs
  rw [withDensity_apply _ hbox]
  have hprodm : Measurable fun z : Fin d → ℂ => ∏ i, gramWeight d (z i) :=
    Finset.measurable_prod _ fun i _ => hwm.comp (measurable_pi_apply i)
  have hpint : Integrable (fun z : Fin d → ℂ => ∏ i, gramWeight d (z i))
      (Measure.pi fun _ : Fin d => volume.restrict discK) :=
    Integrable.fintype_prod (f := fun _ => gramWeight d) fun _ => hint
  rw [← ofReal_integral_eq_lintegral_ofReal hpint.integrableOn
    (Filter.Eventually.of_forall fun z => Finset.prod_nonneg fun i _ => hw0 (z i))]
  have hind : (Set.univ.pi s).indicator (fun z : Fin d → ℂ => ∏ i, gramWeight d (z i)) =
      fun z => ∏ i, (s i).indicator (gramWeight d) (z i) := by
    funext z
    by_cases hz : z ∈ Set.univ.pi s
    · rw [Set.indicator_of_mem hz]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [Set.indicator_of_mem (hz i (Set.mem_univ i))]
    · rw [Set.indicator_of_notMem hz]
      simp only [Set.mem_univ_pi, not_forall] at hz
      obtain ⟨i, hi⟩ := hz
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)).symm
  rw [← integral_indicator hbox, hind,
    integral_fintype_prod_eq_prod (f := fun i => (s i).indicator (gramWeight d)),
    ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg fun z =>
      Set.indicator_nonneg (fun z _ => hw0 z) z)]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [gramMeasure, withDensity_apply _ (hs i), integral_indicator (hs i),
    ofReal_integral_eq_lintegral_ofReal hint.integrableOn (Filter.Eventually.of_forall hw0)]

/-- The measure `e^{-2d Σ U(z_i)} ∏ dA(z_i)` on `𝒦^d`. -/
def gramDensityMeasure (d : ℕ) : Measure (Fin d → ℂ) :=
  (Measure.pi fun _ : Fin d => volume.restrict discK).withDensity
    fun z => ENNReal.ofReal (Real.exp (-(2 * d) * ∑ i, potentialU (z i)))

theorem pi_gramMeasure_eq_density (d : ℕ) :
    Measure.pi (fun _ : Fin d => gramMeasure d) = gramDensityMeasure d := by
  rw [pi_gramMeasure, gramDensityMeasure]
  simp_rw [prod_gramWeight_eq_exp]

/-- **(42) in the density form**: `det G_d = (1/d!) ∫_{𝒦^d} ∏_{i<j}|z_j - z_i|² e^{-2dΣU(z_i)} ∏dA`. -/
theorem gram_det_eq_integral_density (d : ℕ) :
    (weightedGram d discK (gramWeight d)).det =
      (((d.factorial : ℝ)⁻¹ * ∫ z : Fin d → ℂ,
        ∏ i : Fin d, ∏ j ∈ Finset.Ioi i, ‖z j - z i‖ ^ 2 ∂gramDensityMeasure d : ℝ) : ℂ) := by
  rw [gram_det_eq_integral, pi_gramMeasure_eq_density]

end Zeta7Arch

import Zeta7Proof.ArchSourceFlag

/-! C2/C4: the weighted Gram matrix of the monomials (norm (39)) and its positivity.

`weightedGram d K w` is the Gram matrix of `1, z, …, z^{d-1}` for the measure `w(z) dA(z)` on
`K`. For a closed disc `K` of positive radius and a continuous weight that is positive on `K`
(for instance `e^{-2dU}` with `U` continuous), it is positive definite:
`x* G x = ∫_K w |Σ x_j z^j|² dA > 0` for `x ≠ 0`. Hence the Gram-determinant representation of
the unchanged determinant applies verbatim to the paper's norm. -/
noncomputable section
set_option autoImplicit false
namespace Zeta7Arch
open MeasureTheory Matrix ComplexConjugate
open scoped ComplexOrder

/-- The Gram matrix of `1, z, …, z^{d-1}` for `w dA` on `K`. -/
def weightedGram (d : ℕ) (K : Set ℂ) (w : ℂ → ℝ) : Matrix (Fin d) (Fin d) ℂ :=
  fun i j => ∫ z in K, (w z : ℂ) * (conj z ^ (i : ℕ) * z ^ (j : ℕ))

/-- The polynomial with coefficient vector `x`. -/
def polyEval {d : ℕ} (x : Fin d → ℂ) (z : ℂ) : ℂ := ∑ j, x j * z ^ (j : ℕ)

variable {d : ℕ} {K : Set ℂ} {w : ℂ → ℝ}

theorem continuousOn_gram_term (hw : ContinuousOn w K) (i j : ℕ) :
    ContinuousOn (fun z => (w z : ℂ) * (conj z ^ i * z ^ j)) K :=
  (Complex.continuous_ofReal.comp_continuousOn hw).mul
    (((Complex.continuous_conj.pow i).mul (continuous_pow j)).continuousOn)

theorem polyEval_norm_sq (x : Fin d → ℂ) (z : ℂ) :
    ((‖polyEval x z‖ ^ 2 : ℝ) : ℂ) =
      ∑ i : Fin d, ∑ j : Fin d, star (x i) * (conj z ^ (i : ℕ) * z ^ (j : ℕ)) * x j := by
  rw [Complex.ofReal_pow, ← Complex.conj_mul', polyEval, map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [map_mul, map_pow, Complex.star_def]
  ring

theorem weightedGram_quad (hK : IsCompact K) (hw : ContinuousOn w K) (x : Fin d → ℂ) :
    star x ⬝ᵥ (weightedGram d K w *ᵥ x) =
      ((∫ z in K, w z * ‖polyEval x z‖ ^ 2 : ℝ) : ℂ) := by
  rw [← integral_complex_ofReal]
  have hpt : ∀ z, ((w z * ‖polyEval x z‖ ^ 2 : ℝ) : ℂ) =
      ∑ i : Fin d, ∑ j : Fin d, star (x i) * ((w z : ℂ) * (conj z ^ (i : ℕ) * z ^ (j : ℕ))) * x j := by
    intro z
    rw [Complex.ofReal_mul, polyEval_norm_sq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  simp_rw [hpt]
  have hint : ∀ i j : Fin d, Integrable (fun z => star (x i) *
      ((w z : ℂ) * (conj z ^ (i : ℕ) * z ^ (j : ℕ))) * x j) (volume.restrict K) := by
    intro i j
    exact (((continuousOn_gram_term hw i j).integrableOn_compact hK).const_mul _).mul_const _
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j]
  simp only [dotProduct, mulVec, weightedGram, Pi.star_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => hint i j, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_mul_const, integral_const_mul]
  ring

theorem polyEval_zero_finite {x : Fin d → ℂ} (hx : x ≠ 0) :
    {z : ℂ | polyEval x z = 0}.Finite := by
  classical
  set p : Polynomial ℂ := ∑ j : Fin d, Polynomial.C (x j) * Polynomial.X ^ (j : ℕ)
  have hev : ∀ z, p.eval z = polyEval x z := fun z => by
    simp [p, polyEval, Polynomial.eval_finsetSum]
  have hcoeff : ∀ j : Fin d, p.coeff j = x j := fun j => by
    simp only [p, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    rw [Finset.sum_eq_single j (fun k _ hk => by
      rw [if_neg (fun h => hk (Fin.ext h.symm)), mul_zero]) (by simp)]
    simp
  have hp : p ≠ 0 := by
    intro h0
    apply hx
    funext j
    rw [← hcoeff j, h0, Polynomial.coeff_zero, Pi.zero_apply]
  refine (Polynomial.finite_setOfPred_isRoot hp).subset fun z hz => ?_
  simp only [Set.mem_ofPred_eq, Polynomial.IsRoot.def, hev] at hz ⊢
  exact hz

theorem weightedGram_isHermitian : (weightedGram d K w).IsHermitian := by
  ext i j
  simp only [conjTranspose_apply, weightedGram]
  rw [Complex.star_def]
  rw [← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only [map_mul, map_pow, Complex.conj_conj, Complex.conj_ofReal]
  ring

/-- **Positivity of the weighted Gram matrix** on a disc with a positive continuous weight. -/
theorem weightedGram_posDef (z₀ : ℂ) {ρ : ℝ} (hρ : 0 < ρ)
    (hw : ContinuousOn w (Metric.closedBall z₀ ρ)) (hwpos : ∀ z ∈ Metric.closedBall z₀ ρ, 0 < w z) :
    (weightedGram d (Metric.closedBall z₀ ρ) w).PosDef := by
  set K := Metric.closedBall z₀ ρ
  have hK : IsCompact K := isCompact_closedBall z₀ ρ
  refine PosDef.of_dotProduct_mulVec_pos weightedGram_isHermitian fun x hx => ?_
  rw [weightedGram_quad hK hw, Complex.zero_lt_real]
  have hint : IntegrableOn (fun z => w z * ‖polyEval x z‖ ^ 2) K := by
    refine ContinuousOn.integrableOn_compact hK (hw.mul ?_)
    exact (Continuous.continuousOn (by unfold polyEval; fun_prop))
  have hnn : 0 ≤ᵐ[volume.restrict K] fun z => w z * ‖polyEval x z‖ ^ 2 := by
    filter_upwards [ae_restrict_mem measurableSet_closedBall] with z hz
    exact mul_nonneg (hwpos z hz).le (sq_nonneg _)
  rw [setIntegral_pos_iff_support_of_nonneg_ae hnn hint]
  set Z := {z : ℂ | polyEval x z = 0}
  have hZ : volume Z = 0 := (polyEval_zero_finite hx).measure_zero _
  have hsub : K \ Z ⊆ Function.support (fun z => w z * ‖polyEval x z‖ ^ 2) ∩ K := by
    intro z hz
    refine ⟨?_, hz.1⟩
    have hz2 : polyEval x z ≠ 0 := hz.2
    exact (mul_pos (hwpos z hz.1) (by positivity)).ne'
  calc (0 : ENNReal) < volume K := Metric.measure_closedBall_pos volume z₀ hρ
    _ = volume (K \ Z) := (measure_sdiff_null hZ).symm
    _ ≤ _ := measure_mono hsub

/-- **C4 endpoint with the weighted norm (39).** For every closed disc of positive radius and
every continuous weight positive on it, the unchanged determinant has the exact representation
`|D_d| = ∏_k |[x^{λ_k}] F_k| · (det G_d)^{7/2}` with `G_d = weightedGram d K w`. -/
theorem actualDeterminant_weighted_representation (d : ℕ) (c : ℚ) (z₀ : ℂ) {ρ : ℝ}
    (hρ : 0 < ρ) (hw : ContinuousOn w (Metric.closedBall z₀ ρ))
    (hwpos : ∀ z ∈ Metric.closedBall z₀ ρ, 0 < w z) :
    ∃ C : Matrix (JIdx d) (JIdx d) ℂ,
      Cᴴ * sourceGram d (weightedGram d (Metric.closedBall z₀ ρ) w) * C = 1 ∧
      (∀ k, adaptedVector d C k ∈ flag d c k) ∧
      (∀ k, ∀ m < jump d c k, PowerSeries.coeff m (sourceMap d c (adaptedVector d C k)) = 0) ∧
      |(Zeta7Common.actualCommonDeterminant d c : ℝ)| =
        (∏ k, ‖PowerSeries.coeff (jump d c k) (sourceMap d c (adaptedVector d C k))‖) *
          Real.sqrt ((weightedGram d (Metric.closedBall z₀ ρ) w).det.re ^ 7) :=
  actualDeterminant_gram_representation d c _ (weightedGram_posDef z₀ hρ hw hwpos)

end Zeta7Arch

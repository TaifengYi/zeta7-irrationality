import Zeta7Proof.ArchSubmean

/-! C2, step 3: the seven-block boundary estimate and the leading-coefficient bound (41).

For a source vector `v` with block polynomials `P_b` (`b = 0` the polynomial block, `b = j+1` the
multiplier of `g_j`), the pole-cleared pullback is

`a(q) F(x(q)) = Σ_b P_b(x(q)) · G_b(q)`,  `G_0 = a = A³`, `G_{j+1} = (A³ g_j)(x(q))`

(`evalQ_pulledSource`). On the `i`-th circle every `|G_b| ≤ B_i`, a constant depending only on the
fixed circle and `c`; every `x(q)` lies in the support of `μ`. With (40), for every source vector
whose blocks satisfy `‖P_b‖_d ≤ 1` (in particular for every vector of norm one for the seven-block
Gram norm):

`|a(q) F(x(q))| ≤ exp(d U(x(q)) + d ω(h) + C_h)`   on `|q| = r_i`,

with `C_h = log(7 B_i (π h²)^{-1/2})`, independent of `d`, of the jump index and of the vector
(`boundary_bound`). Combined with the Jensen step this gives, for every flag vector with nonzero
leading coefficient `c_n`, `n = λ_k`,

`log |c_n| ≤ d W_i - n t_i + d ω(h) + C_h`,   `W_i = ∫ U dμ_i`, `t_i = log r_i`

(`coefficient_bound`), inequality (41) of the paper. -/
noncomputable section
set_option autoImplicit false
namespace Zeta7Arch
open MeasureTheory Set Real Filter Topology PowerSeries

/-! ### Evaluation of the pulled-back source -/

theorem evalQ_smul' (a : ℂ) (f : ℂ⟦X⟧) (q : ℂ) : evalQ (a • f) q = a * evalQ f q := by
  simp only [evalQ, PowerSeries.coeff_smul, smul_eq_mul, mul_assoc, tsum_mul_left]

theorem evalQ_one (q : ℂ) : evalQ 1 q = 1 := by
  simpa using evalQ_C 1 q

theorem evalQ_sum' {ι : Type*} (s : Finset ι) (f : ι → ℂ⟦X⟧) (hf : ∀ i ∈ s, Tempered (f i))
    {q : ℂ} (hq : ‖q‖ < 1) : evalQ (∑ i ∈ s, f i) q = ∑ i ∈ s, evalQ (f i) q := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (evalQ_C 0 q)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      evalQ_add (hf a (by simp)) (tempered_sum _ _ fun i hi => hf i (by simp [hi])) hq,
      ih fun i hi => hf i (by simp [hi])]

theorem evalQ_pow {f : ℂ⟦X⟧} (hf : Tempered f) (n : ℕ) {q : ℂ} (hq : ‖q‖ < 1) :
    evalQ (f ^ n) q = evalQ f q ^ n := by
  induction n with
  | zero => simp [evalQ_one]
  | succ n ih => rw [pow_succ, evalQ_mul (hf.pow n) hf hq, ih, pow_succ]

/-- The block factors `G_b(q)`. -/
def blockFactor (c : ℚ) : Fin 7 → ℂ → ℂ :=
  Fin.cons (evalQ aC) fun j => evalQ ((clearedGerm c j).map (algebraMap ℚ ℂ))

/-- The coefficient vector of block `b` of a source vector. -/
def blockPoly {d : ℕ} (v : Source d) (b : Fin 7) : Fin d → ℂ :=
  fun m => v ((blockPos d).symm (b, m))

theorem clearedBlock_blockPos_symm (d : ℕ) (c : ℚ) (b : Fin 7) (m : Fin d) :
    clearedBlock d c ((blockPos d).symm (b, m)) =
      xC ^ m.val * (Fin.cons aC fun j => (clearedGerm c j).map (algebraMap ℚ ℂ) :
        Fin 7 → ℂ⟦X⟧) b := by
  cases b using Fin.cases <;> simp [blockPos, clearedBlock]

theorem blockFactor_tempered (c : ℚ) (b : Fin 7) :
    Tempered ((Fin.cons aC fun j => (clearedGerm c j).map (algebraMap ℚ ℂ) :
      Fin 7 → ℂ⟦X⟧) b) := by
  cases b using Fin.cases with
  | zero => exact aC_tempered
  | succ j => exact clearedGerm_tempered c j

/-- **Evaluation of `a(q) F(x(q))`** as `Σ_b P_b(x(q)) G_b(q)`. -/
theorem evalQ_pulledSource (d : ℕ) (c : ℚ) (v : Source d) {q : ℂ} (hq : ‖q‖ < 1) :
    evalQ (pulledSource d c v) q =
      ∑ b : Fin 7, polyEval (blockPoly v b) (xFun q) * blockFactor c b q := by
  rw [pulledSource_eq, evalQ_sum' _ _ (fun i _ => (clearedBlock_tempered d c i).smul (v i)) hq,
    ← (blockPos d).symm.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [polyEval, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [evalQ_smul', clearedBlock_blockPos_symm,
    evalQ_mul (xC_tempered.pow _) (blockFactor_tempered c b) hq, evalQ_pow xC_tempered _ hq]
  have hfac : evalQ ((Fin.cons aC fun j => (clearedGerm c j).map (algebraMap ℚ ℂ) :
      Fin 7 → ℂ⟦X⟧) b) q = blockFactor c b q := by
    cases b using Fin.cases <;> simp [blockFactor]
  rw [hfac, blockPoly, xFun]
  ring

/-! ### Points of the circles map into the support -/

theorem circlePt_periodic (r : ℝ) : Function.Periodic (circlePt r) (2 * π) := by
  intro θ
  have h := periodic_circleMap 0 r θ
  simpa [circleMap, circlePt] using h

theorem circFun_mem_supportSet (i : Fin 6) (θ : ℝ) : circFun (circleR i) θ ∈ supportSet := by
  set θ' := toIcoMod two_pi_pos 0 θ with hθ'
  have hmem : θ' ∈ Ico 0 (0 + 2 * π) := toIcoMod_mem_Ico two_pi_pos 0 θ
  have heq : circlePt (circleR i) θ' = circlePt (circleR i) θ := by
    rw [hθ', toIcoMod]
    exact (circlePt_periodic _).sub_zsmul_eq _
  refine mem_iUnion.mpr ⟨i, θ', ⟨hmem.1, by linarith [hmem.2]⟩, ?_⟩
  simp only [circFun, heq]

theorem xFun_mem_supportSet {i : Fin 6} {q : ℂ} (hq : ‖q‖ = circleR i) :
    xFun q ∈ supportSet := by
  have h : q = circlePt (circleR i) (Complex.arg q) := by
    rw [circlePt, ← hq]
    exact (Complex.norm_mul_exp_arg_mul_I q).symm
  rw [h]
  exact circFun_mem_supportSet i _

/-! ### The boundary estimate -/

theorem blockFactor_continuousOn (c : ℚ) (b : Fin 7) :
    ContinuousOn (blockFactor c b) (Metric.ball 0 1) := by
  cases b using Fin.cases with
  | zero => exact aC_tempered.analyticOnNhd.continuousOn
  | succ j => exact (clearedGerm_tempered c j).analyticOnNhd.continuousOn

theorem exists_blockFactor_bound (c : ℚ) (i : Fin 6) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ b : Fin 7, ∀ q : ℂ, ‖q‖ = circleR i → ‖blockFactor c b q‖ ≤ B := by
  have hsub : Metric.sphere (0 : ℂ) (circleR i) ⊆ Metric.ball 0 1 := fun q hq => by
    rw [Metric.mem_sphere, dist_zero_right] at hq
    rw [Metric.mem_ball, dist_zero_right, hq]
    exact circleR_lt_one i
  choose B hB using fun b : Fin 7 =>
    (isCompact_sphere (0 : ℂ) (circleR i)).exists_bound_of_continuousOn
      ((blockFactor_continuousOn c b).mono hsub)
  have hsum0 : 0 ≤ ∑ b, |B b| := Finset.sum_nonneg (fun b _ => abs_nonneg (B b))
  refine ⟨1 + ∑ b, |B b|, by linarith, fun b q hq => ?_⟩
  have h1 := hB b q (by rw [mem_sphere_iff_norm, sub_zero]; exact hq)
  have h2 : |B b| ≤ ∑ b, |B b| :=
    Finset.single_le_sum (fun b _ => abs_nonneg (B b)) (Finset.mem_univ b)
  linarith [le_abs_self (B b)]

/-- **The seven-block boundary estimate.** -/
theorem boundary_bound (c : ℚ) (i : Fin 6) {h : ℝ} (hh : 0 < h) (h1 : h ≤ 1) :
    ∃ Ch : ℝ, ∀ (d : ℕ) (v : Source d), (∀ b, normSqD d (blockPoly v b) ≤ 1) →
      ∀ q : ℂ, ‖q‖ = circleR i →
        ‖evalQ (pulledSource d c v) q‖ ≤
          exp (d * potentialU (xFun q) + d * omegaU h + Ch) := by
  obtain ⟨B, hB1, hB⟩ := exists_blockFactor_bound c i
  set S : ℝ := (Real.sqrt (π * h ^ 2))⁻¹ with hS
  have hS0 : 0 < S := by rw [hS]; positivity
  refine ⟨Real.log (7 * B * S), fun d v hv q hq => ?_⟩
  have hq1 : ‖q‖ < 1 := by rw [hq]; exact circleR_lt_one i
  have hz := xFun_mem_supportSet hq
  set E : ℝ := exp (d * (potentialU (xFun q) + omegaU h)) with hE
  have hterm : ∀ b : Fin 7,
      ‖polyEval (blockPoly v b) (xFun q) * blockFactor c b q‖ ≤ S * E * B := by
    intro b
    rw [norm_mul]
    have hp := weighted_submean d hz hh h1 (blockPoly v b)
    have hsq : Real.sqrt (normSqD d (blockPoly v b)) ≤ 1 := by
      rw [Real.sqrt_le_one]; exact hv b
    have hp' : ‖polyEval (blockPoly v b) (xFun q)‖ ≤ S * E := by
      calc ‖polyEval (blockPoly v b) (xFun q)‖
          ≤ S * E * Real.sqrt (normSqD d (blockPoly v b)) := hp
        _ ≤ S * E * 1 := by gcongr
        _ = S * E := mul_one _
    exact mul_le_mul hp' (hB b q hq) (norm_nonneg _) (by positivity)
  rw [evalQ_pulledSource d c v hq1]
  calc ‖∑ b : Fin 7, polyEval (blockPoly v b) (xFun q) * blockFactor c b q‖
      ≤ ∑ b : Fin 7, ‖polyEval (blockPoly v b) (xFun q) * blockFactor c b q‖ := norm_sum_le _ _
    _ ≤ ∑ _b : Fin 7, S * E * B := Finset.sum_le_sum fun b _ => hterm b
    _ = exp (d * potentialU (xFun q) + d * omegaU h + Real.log (7 * B * S)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Real.exp_add,
          Real.exp_log (by positivity), hE, mul_add]
        push_cast
        ring

/-! ### The full coefficient bound (41) -/

/-- `W_i = ∫ U dμ_i`. -/
def energyW (i : Fin 6) : ℝ := ∫ z, potentialU z ∂circleMeasure i

/-- `t_i = log r_i`. -/
def circleT (i : Fin 6) : ℝ := Real.log (circleR i)

theorem circleAverage_U_x (i : Fin 6) :
    circleAverage (fun q => potentialU (xFun q)) 0 (circleR i) = energyW i := by
  rw [energyW, integral_circleMeasure i potentialU_continuous.aestronglyMeasurable,
    circleAverage_def, smul_eq_mul, intervalIntegral.integral_of_le two_pi_pos.le,
    ← integral_Icc_eq_integral_Ioc]
  congr 1
  refine setIntegral_congr_fun measurableSet_Icc fun θ _ => ?_
  simp [circleMap, circlePt, circFun]

theorem continuousOn_U_x (i : Fin 6) :
    ContinuousOn (fun q => potentialU (xFun q)) (Metric.sphere 0 (circleR i)) := by
  refine potentialU_continuous.comp_continuousOn (xFun_analytic.continuousOn.mono ?_)
  intro q hq
  rw [Metric.mem_sphere, dist_zero_right] at hq
  rw [Metric.mem_ball, dist_zero_right, hq]
  exact circleR_lt_one i

theorem circleIntegrable_U_x (i : Fin 6) :
    CircleIntegrable (fun q => potentialU (xFun q)) 0 (circleR i) :=
  ContinuousOn.circleIntegrable (circleR_pos i).le (continuousOn_U_x i)

/-- **The leading-coefficient bound (41)** on the `i`-th circle. -/
theorem coefficient_bound (c : ℚ) (i : Fin 6) {h : ℝ} (hh : 0 < h) (h1 : h ≤ 1) :
    ∃ Ch : ℝ, ∀ (d : ℕ) (k : JIdx d) (v : Source d), v ∈ flag d c k →
      (∀ b, normSqD d (blockPoly v b) ≤ 1) →
      PowerSeries.coeff (jump d c k) (sourceMap d c v) ≠ 0 →
      Real.log ‖PowerSeries.coeff (jump d c k) (sourceMap d c v)‖ ≤
        d * energyW i - (jump d c k : ℝ) * circleT i + d * omegaU h + Ch := by
  obtain ⟨Ch, hCh⟩ := boundary_bound c i hh h1
  refine ⟨Ch, fun d k v hv hnorm hlead => ?_⟩
  set F : ℂ → ℂ := evalQ (pulledSource d c v) with hF
  set r := circleR i
  have hr0 := circleR_pos i
  have hr1 := circleR_lt_one i
  have habs : |r| = r := abs_of_pos hr0
  have hj := flag_leading_jensen d c k v hv hlead hr0 hr1
  set K : ℝ := d * omegaU h + Ch with hK
  set g₂ : ℂ → ℝ := fun q => d * potentialU (xFun q) + K with hg₂
  have hsph : ∀ q ∈ Metric.sphere (0 : ℂ) |r|, ‖q‖ = r := fun q hq => by
    rw [Metric.mem_sphere, dist_zero_right, habs] at hq; exact hq
  have hlogle : ∀ q ∈ Metric.sphere (0 : ℂ) |r|, F q ≠ 0 → Real.log ‖F q‖ ≤ g₂ q := by
    intro q hq hne
    have hb := hCh d v hnorm q (hsph q hq)
    have hg : g₂ q = d * potentialU (xFun q) + d * omegaU h + Ch := by rw [hg₂, hK]; ring
    calc Real.log ‖F q‖ ≤ Real.log (exp (g₂ q)) := by
          rw [hg]; exact Real.log_le_log (norm_pos_iff.mpr hne) hb
      _ = g₂ q := Real.log_exp _
  obtain ⟨g, hg, hp, hg0⟩ := flag_pulled_factor d c k v hv
  have hFnz : ∀ᶠ q in Filter.codiscreteWithin (Metric.ball (0 : ℂ) 1), F q ≠ 0 := by
    rcases (pulledSource_holomorphic d c v).eqOn_zero_or_eventually_ne_zero_of_preconnected
      (convex_ball 0 1).isPreconnected with hzero | hne
    · exfalso
      have hgc : ContinuousAt (evalQ g) 0 := (hg.analyticOnNhd 0 (by simp)).continuousAt
      have hev : ∀ᶠ q in 𝓝 (0 : ℂ), evalQ g q ≠ 0 :=
        hgc.eventually_ne (by rw [hg0]; exact hlead)
      obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hev
      set ε : ℝ := min (δ / 2) (1 / 2)
      have hε0 : 0 < ε := by positivity
      have hnorm' : ‖(ε : ℂ)‖ = ε := by rw [Complex.norm_real, Real.norm_of_nonneg hε0.le]
      have hεδ : dist (ε : ℂ) 0 < δ := by
        rw [dist_zero_right, hnorm']; exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
      have hε1 : ‖(ε : ℂ)‖ < 1 := by
        rw [hnorm']; exact lt_of_le_of_lt (min_le_right _ _) (by norm_num)
      have hmem : (ε : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
        rw [Metric.mem_ball, dist_zero_right]; exact hε1
      have hz : F ε = 0 := hzero hmem
      have hfac : F ε = (ε : ℂ) ^ jump d c k * evalQ g ε := by
        rw [hF, hp, evalQ_mul (tempered_X_pow _) hg hε1, evalQ_X_pow]
      rw [hfac] at hz
      exact mul_ne_zero (pow_ne_zero _ (by exact_mod_cast hε0.ne')) (hball hεδ) hz
    · exact hne
  have hsub : Metric.sphere (0 : ℂ) |r| ⊆ Metric.ball 0 1 := fun q hq => by
    rw [Metric.mem_ball, dist_zero_right, hsph q hq]; exact hr1
  have hFnz' : ∀ᶠ q in Filter.codiscreteWithin (Metric.sphere (0 : ℂ) |r|), F q ≠ 0 :=
    Filter.codiscreteWithin_mono hsub hFnz
  have hcongr : circleAverage (fun q => Real.log ‖F q‖) 0 r =
      circleAverage (fun q => min (Real.log ‖F q‖) (g₂ q)) 0 r := by
    apply circleAverage_congr_codiscreteWithin _ hr0.ne'
    filter_upwards [hFnz', Filter.self_mem_codiscreteWithin (Metric.sphere (0 : ℂ) |r|)]
      with q hq hqs
    exact (min_eq_left (hlogle q hqs hq)).symm
  have hint1 : CircleIntegrable (fun q => Real.log ‖F q‖) 0 r :=
    ((pulledSource_holomorphic d c v).mono hsub).meromorphicOn.circleIntegrable_log_norm
  have hcont2 : ContinuousOn g₂ (Metric.sphere 0 r) :=
    (continuousOn_const.mul (continuousOn_U_x i)).add continuousOn_const
  have hint2 : CircleIntegrable g₂ 0 r := ContinuousOn.circleIntegrable hr0.le hcont2
  have hint3 : CircleIntegrable (fun q => min (Real.log ‖F q‖) (g₂ q)) 0 r :=
    ⟨hint1.1.inf hint2.1, hint1.2.inf hint2.2⟩
  have hmono : circleAverage (fun q => min (Real.log ‖F q‖) (g₂ q)) 0 r ≤ circleAverage g₂ 0 r :=
    circleAverage_mono hint3 hint2 fun q _ => min_le_right _ _
  have havg : circleAverage g₂ 0 r = d * energyW i + K := by
    rw [← circleAverage_U_x i]
    simp only [circleAverage_def, hg₂, smul_eq_mul]
    have hcU : IntervalIntegrable (fun θ => potentialU (xFun (circleMap 0 r θ))) volume 0
        (2 * π) := circleIntegrable_U_x i
    rw [intervalIntegral.integral_add (hcU.const_mul _) intervalIntegrable_const,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul]
    have hpi : (2 * π) ≠ 0 := by positivity
    field_simp
    ring
  have hlr : Real.log r = circleT i := rfl
  rw [hlr] at hj
  have hF' : (fun q => Real.log ‖evalQ (pulledSource d c v) q‖) = fun q => Real.log ‖F q‖ := rfl
  rw [hF'] at hj
  linarith [hj, hcongr, hmono, havg]

end Zeta7Arch

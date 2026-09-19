import Zeta7Proof.ArchC3Endpoint
import Zeta7Proof.ArchC2Endpoint

/-! C4 / C30: the Archimedean bound for the unchanged determinant.

* `gram_norm_pos`, `gram_det_re_pos`: the norm (39) is positive definite, so `det G_d > 0`
  (in `ℂ`, and its real part is positive); hence the logarithmic form of (45) holds
  unconditionally (`gram_log_limsup`).
* `adapted_coefficient_bound_all`: one adapted orthonormal flag basis satisfies (41) on all six
  circles simultaneously, with one constant `C_h`.
* `phiMin k = min_i (W_i - k t_i)` is Lipschitz, and `riemann_sum_bound` proves
  `|Σ_{j<7d} d⁻¹ φ(j/d) - ∫_0^7 φ| ≤ 7T/d`.
* `log_det_le`: (46) for every `d`, with the jump indices replaced by `j` at cost `O(d)`.
* `c30`: for every rational `c` and `ε > 0`, eventually
  `log |D_d| ≤ (∫_0^7 φ - (7/2) I + ε) d²`. -/
noncomputable section
set_option autoImplicit false
namespace Zeta7Arch
open MeasureTheory Set Real Filter Topology Matrix
open scoped ComplexOrder Interval

/-! ### Gram positivity -/

theorem discK_eq : discK = Metric.closedBall (0 : ℂ) (supR + 1) := rfl

theorem supR_add_one_pos : (0 : ℝ) < supR + 1 := by linarith [supR_nonneg]

/-- The weighted Gram matrix of the norm (39) is positive definite. -/
theorem gram_posDef (d : ℕ) : (weightedGram d discK (gramWeight d)).PosDef :=
  weightedGram_posDef 0 supR_add_one_pos (gramWeight_continuous d).continuousOn
    fun z _ => gramWeight_pos d z

/-- **Positivity of the norm (39)**: `∫_𝒦 |P|² e^{-2dU} dA > 0` for every nonzero `P` of
degree `< d`. -/
theorem gram_norm_pos {d : ℕ} {x : Fin d → ℂ} (hx : x ≠ 0) : 0 < normSqD d x := by
  have h := (gram_posDef d).dotProduct_mulVec_pos hx
  rw [weightedGram_quad isCompact_discK (gramWeight_continuous d).continuousOn,
    Complex.zero_lt_real] at h
  exact h

theorem gram_det_pos (d : ℕ) : 0 < (weightedGram d discK (gramWeight d)).det :=
  (gram_posDef d).det_pos

/-- **Gram determinant positivity**: `0 < det G_d`. -/
theorem gram_det_re_pos (d : ℕ) : 0 < (weightedGram d discK (gramWeight d)).det.re :=
  (Complex.lt_def.mp (gram_det_pos d)).1

/-- (45) in logarithmic form, now unconditional. -/
theorem gram_log_limsup {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ d : ℕ in atTop,
      Real.log (weightedGram d discK (gramWeight d)).det.re ≤ (-energyI + ε) * (d : ℝ) ^ 2 :=
  (gram_limsup_log hε).mono fun d h => h (gram_det_re_pos d)

/-! ### (41) on all six circles for one adapted basis -/

/-- The leading coefficient of the `k`-th adapted vector. -/
abbrev adaptedCoeff (d : ℕ) (c : ℚ) (C : Matrix (JIdx d) (JIdx d) ℂ) (k : JIdx d) : ℂ :=
  PowerSeries.coeff (jump d c k) (sourceMap d c (adaptedVector d C k))

theorem adapted_coefficient_bound_all (c : ℚ) {h : ℝ} (hh : 0 < h) (h1 : h ≤ 1) :
    ∃ Ch : ℝ, ∀ d : ℕ, ∃ C : Matrix (JIdx d) (JIdx d) ℂ,
      |(Zeta7Common.actualCommonDeterminant d c : ℝ)| =
        (∏ k, ‖adaptedCoeff d c C k‖) *
          Real.sqrt ((weightedGram d discK (gramWeight d)).det.re ^ 7) ∧
      ∀ (i : Fin 6) (k : JIdx d), adaptedCoeff d c C k ≠ 0 →
        Real.log ‖adaptedCoeff d c C k‖ ≤
          d * energyW i - (jump d c k : ℝ) * circleT i + d * omegaU h + Ch := by
  choose Ch hCh using fun i : Fin 6 => coefficient_bound c i hh h1
  refine ⟨∑ i, |Ch i|, fun d => ?_⟩
  obtain ⟨C, hC, hflag, _, hdet⟩ := actualDeterminant_weighted_representation d c 0
    supR_add_one_pos (gramWeight_continuous d).continuousOn fun z _ => gramWeight_pos d z
  rw [← discK_eq] at hC hdet
  refine ⟨C, hdet, fun i k hne => ?_⟩
  have hb := hCh i d k _ (hflag k) (fun b => adapted_block_norm_le d hC k b) hne
  have hle : Ch i ≤ ∑ j, |Ch j| := (le_abs_self _).trans
    (Finset.single_le_sum (fun j _ => abs_nonneg (Ch j)) (Finset.mem_univ i))
  linarith

/-! ### The minimum of the six affine functions -/

/-- `φ(k) = min_i (W_i - k t_i)`. -/
def phiMin (k : ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty fun i : Fin 6 => energyW i - k * circleT i

/-- A Lipschitz constant for `φ`. -/
def tMax : ℝ := ∑ i, |circleT i|

theorem tMax_nonneg : 0 ≤ tMax := Finset.sum_nonneg fun i _ => abs_nonneg _

theorem abs_circleT_le (i : Fin 6) : |circleT i| ≤ tMax :=
  Finset.single_le_sum (fun j _ => abs_nonneg (circleT j)) (Finset.mem_univ i)

theorem inf'_le_inf'_add {ι : Type*} {s : Finset ι} (hs : s.Nonempty) {f g : ι → ℝ} {C : ℝ}
    (h : ∀ i ∈ s, f i ≤ g i + C) : s.inf' hs f ≤ s.inf' hs g + C := by
  obtain ⟨i, hi, hgi⟩ := s.exists_mem_eq_inf' hs g
  calc s.inf' hs f ≤ f i := Finset.inf'_le _ hi
    _ ≤ g i + C := h i hi
    _ = _ := by rw [hgi]

theorem inf'_mul_left {ι : Type*} {s : Finset ι} (hs : s.Nonempty) {c : ℝ} (hc : 0 ≤ c)
    (f : ι → ℝ) : s.inf' hs (fun i => c * f i) = c * s.inf' hs f := by
  apply le_antisymm
  · obtain ⟨i, hi, he⟩ := s.exists_mem_eq_inf' hs f
    rw [he]; exact Finset.inf'_le (fun i => c * f i) hi
  · exact Finset.le_inf' _ _ fun i hi => mul_le_mul_of_nonneg_left (Finset.inf'_le _ hi) hc

theorem phiMin_le_add (a b : ℝ) : phiMin a ≤ phiMin b + tMax * |a - b| := by
  refine inf'_le_inf'_add _ fun i _ => ?_
  have h1 : |(b - a) * circleT i| ≤ tMax * |a - b| := by
    rw [abs_mul, abs_sub_comm, mul_comm]
    exact mul_le_mul_of_nonneg_right (abs_circleT_le i) (abs_nonneg _)
  have h2 := le_abs_self ((b - a) * circleT i)
  nlinarith

/-- `φ` is Lipschitz with constant `T = Σ|t_i|`. -/
theorem abs_phiMin_sub_le (a b : ℝ) : |phiMin a - phiMin b| ≤ tMax * |a - b| := by
  rw [abs_le]
  have h1 := phiMin_le_add a b
  have h2 := phiMin_le_add b a
  rw [abs_sub_comm] at h2
  constructor <;> linarith

theorem phiMin_continuous : Continuous phiMin := by
  rw [Metric.continuous_iff]
  intro b ε hε
  refine ⟨ε / (tMax + 1), div_pos hε (by linarith [tMax_nonneg]), fun a ha => ?_⟩
  rw [Real.dist_eq] at ha ⊢
  have h := abs_phiMin_sub_le a b
  have hT := tMax_nonneg
  calc |phiMin a - phiMin b| ≤ tMax * |a - b| := h
    _ ≤ (tMax + 1) * |a - b| := by nlinarith [abs_nonneg (a - b)]
    _ < (tMax + 1) * (ε / (tMax + 1)) := mul_lt_mul_of_pos_left ha (by linarith)
    _ = ε := by field_simp

/-- `min_i (d W_i - j t_i) = d φ(j/d)`. -/
theorem inf_scaled {d : ℕ} (hd : 0 < d) (j : ℝ) :
    Finset.univ.inf' Finset.univ_nonempty (fun i : Fin 6 => d * energyW i - j * circleT i) =
      d * phiMin (j / d) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  rw [phiMin, ← inf'_mul_left _ hd'.le]
  congr 1
  funext i
  field_simp

/-! ### The Riemann sum -/

/-- **Riemann-sum bound**: `|Σ_{j<7d} d⁻¹ φ(j/d) - ∫_0^7 φ| ≤ 7T/d`. -/
theorem riemann_sum_bound {d : ℕ} (hd : 0 < d) :
    |∑ j ∈ Finset.range (7 * d), (d : ℝ)⁻¹ * phiMin (j / d) - ∫ k in (0 : ℝ)..7, phiMin k| ≤
      7 * tMax / d := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  set a : ℕ → ℝ := fun j => j / d with ha
  have hint : ∀ j < 7 * d, IntervalIntegrable phiMin volume (a j) (a (j + 1)) :=
    fun j _ => phiMin_continuous.intervalIntegrable _ _
  have hsplit := intervalIntegral.sum_integral_adjacent_intervals hint
  have ha0 : a 0 = 0 := by simp [ha]
  have ha7 : a (7 * d) = 7 := by simp only [ha]; push_cast; field_simp
  rw [ha0, ha7] at hsplit
  rw [← hsplit, ← Finset.sum_sub_distrib]
  have hpiece : ∀ j ∈ Finset.range (7 * d),
      |(d : ℝ)⁻¹ * phiMin (j / d) - ∫ k in a j..a (j + 1), phiMin k| ≤ tMax / d ^ 2 := by
    intro j _
    have hlen : a (j + 1) - a j = (d : ℝ)⁻¹ := by
      simp only [ha]; push_cast; field_simp; ring
    have hle : a j ≤ a (j + 1) := by linarith [inv_pos.mpr hd']
    have hconst : (d : ℝ)⁻¹ * phiMin (j / d) = ∫ _ in a j..a (j + 1), phiMin (j / d) := by
      rw [intervalIntegral.integral_const, hlen, smul_eq_mul]
    rw [hconst, ← intervalIntegral.integral_sub intervalIntegrable_const
      (phiMin_continuous.intervalIntegrable _ _)]
    have hb : ∀ k ∈ Ι (a j) (a (j + 1)), ‖phiMin (j / d) - phiMin k‖ ≤ tMax / d := by
      intro k hk
      rw [uIoc_of_le hle] at hk
      rw [Real.norm_eq_abs]
      refine (abs_phiMin_sub_le _ _).trans ?_
      have h1 : |(j : ℝ) / d - k| ≤ (d : ℝ)⁻¹ := by
        rw [abs_le]; simp only [ha] at hk hlen; constructor <;> linarith [hk.1, hk.2]
      calc tMax * |(j : ℝ) / d - k| ≤ tMax * (d : ℝ)⁻¹ :=
            mul_le_mul_of_nonneg_left h1 tMax_nonneg
        _ = tMax / d := by rw [div_eq_mul_inv]
    have h := intervalIntegral.norm_integral_le_of_norm_le_const hb
    rw [Real.norm_eq_abs, hlen, abs_of_pos (inv_pos.mpr hd')] at h
    calc _ ≤ tMax / d * (d : ℝ)⁻¹ := h
      _ = tMax / d ^ 2 := by field_simp
  calc |∑ j ∈ Finset.range (7 * d), ((d : ℝ)⁻¹ * phiMin (j / d) -
          ∫ k in a j..a (j + 1), phiMin k)|
      ≤ ∑ j ∈ Finset.range (7 * d), |(d : ℝ)⁻¹ * phiMin (j / d) -
          ∫ k in a j..a (j + 1), phiMin k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range (7 * d), tMax / d ^ 2 := Finset.sum_le_sum hpiece
    _ = 7 * tMax / d := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; field_simp

/-- **The Riemann-sum limit** `d⁻² Σ_{j<7d} min_i(d W_i - j t_i) → ∫_0^7 φ`. -/
theorem riemann_sum_tendsto :
    Tendsto (fun d : ℕ => ((d : ℝ) ^ 2)⁻¹ * ∑ j ∈ Finset.range (7 * d),
      Finset.univ.inf' Finset.univ_nonempty (fun i : Fin 6 => d * energyW i - j * circleT i))
      atTop (𝓝 (∫ k in (0 : ℝ)..7, phiMin k)) := by
  have hlim : Tendsto (fun d : ℕ => 7 * tMax / (d : ℝ)) atTop (𝓝 0) := by
    simpa using tendsto_const_div_atTop_nhds_zero_nat (7 * tMax)
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hlim ε hε
  refine ⟨max N 1, fun d hdN => ?_⟩
  have hd : 0 < d := lt_of_lt_of_le one_pos (le_of_max_le_right hdN)
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have heq : ((d : ℝ) ^ 2)⁻¹ * ∑ j ∈ Finset.range (7 * d),
      Finset.univ.inf' Finset.univ_nonempty (fun i : Fin 6 => d * energyW i - j * circleT i) =
      ∑ j ∈ Finset.range (7 * d), (d : ℝ)⁻¹ * phiMin (j / d) := by
    simp_rw [inf_scaled hd, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    field_simp
  rw [heq, Real.dist_eq]
  have h1 := riemann_sum_bound hd
  have h2 := hN d (le_of_max_le_left hdN)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by have := tMax_nonneg; positivity)] at h2
  linarith

/-! ### (46) for every degree -/

/-- Replacing `λ_k` by `k` costs at most `176 T`. -/
theorem jump_min_le (d : ℕ) (c : ℚ) (k : JIdx d) :
    Finset.univ.inf' Finset.univ_nonempty
        (fun i : Fin 6 => d * energyW i - (jump d c k : ℝ) * circleT i) ≤
      Finset.univ.inf' Finset.univ_nonempty
        (fun i : Fin 6 => d * energyW i - (k.val : ℝ) * circleT i) + 176 * tMax := by
  refine inf'_le_inf'_add _ fun i _ => ?_
  obtain ⟨h1, h2⟩ := jump_bounds d c k
  have h1' : (k.val : ℝ) ≤ jump d c k := by exact_mod_cast h1
  have h2' : (jump d c k : ℝ) ≤ k.val + 176 := by exact_mod_cast h2
  have hT := abs_circleT_le i
  have h3 : -(((jump d c k : ℝ) - k.val) * circleT i) ≤ ((jump d c k : ℝ) - k.val) * |circleT i| := by
    rw [← mul_neg]
    exact mul_le_mul_of_nonneg_left (neg_le_abs _) (by linarith)
  nlinarith [abs_nonneg (circleT i)]

theorem sum_jidx_eq {d : ℕ} (g : ℕ → ℝ) : ∑ k : JIdx d, g k.val = ∑ j ∈ Finset.range (7 * d), g j := by
  rw [Fin.sum_univ_eq_sum_range (fun j => g j), card_blockIndex]

/-- **(46)**, with `λ_j` replaced by `j`: for every `d > 0`,
`log|D_d| ≤ (7/2) log det G_d + d² Σ_j d⁻¹ φ(j/d) + 7d² ω(h) + 7d(176T + C_h)`. -/
theorem log_det_le (c : ℚ) {h : ℝ} (hh : 0 < h) (h1 : h ≤ 1) :
    ∃ Ch : ℝ, ∀ d : ℕ, 0 < d →
      Real.log |(Zeta7Common.actualCommonDeterminant d c : ℝ)| ≤
        7 / 2 * Real.log (weightedGram d discK (gramWeight d)).det.re +
          (d : ℝ) ^ 2 * ∑ j ∈ Finset.range (7 * d), (d : ℝ)⁻¹ * phiMin (j / d) +
          7 * (d : ℝ) ^ 2 * omegaU h + 7 * d * (176 * tMax + Ch) := by
  obtain ⟨Ch, hCh⟩ := adapted_coefficient_bound_all c hh h1
  refine ⟨Ch, fun d hd => ?_⟩
  obtain ⟨C, hdet, hbound⟩ := hCh d
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hD : (Zeta7Common.actualCommonDeterminant d c : ℝ) ≠ 0 := by
    exact_mod_cast Zeta7Common.actualCommonDeterminant_ne_zero d c
  have hG := gram_det_re_pos d
  have hsqrt : 0 < Real.sqrt ((weightedGram d discK (gramWeight d)).det.re ^ 7) :=
    Real.sqrt_pos.mpr (pow_pos hG 7)
  have hprod : (∏ k, ‖adaptedCoeff d c C k‖) ≠ 0 := by
    intro h0
    rw [h0, zero_mul, abs_eq_zero] at hdet
    exact hD hdet
  have hne : ∀ k, adaptedCoeff d c C k ≠ 0 := by
    intro k hk
    apply hprod
    exact Finset.prod_eq_zero (Finset.mem_univ k) (by rw [hk, norm_zero])
  have hlog : Real.log |(Zeta7Common.actualCommonDeterminant d c : ℝ)| =
      ∑ k, Real.log ‖adaptedCoeff d c C k‖ +
        7 / 2 * Real.log (weightedGram d discK (gramWeight d)).det.re := by
    rw [hdet, Real.log_mul hprod hsqrt.ne', Real.log_prod fun k _ => norm_ne_zero_iff.mpr (hne k),
      Real.log_sqrt (pow_pos hG 7).le, Real.log_pow]
    push_cast; ring
  -- each coefficient: the minimum over the six circles
  have hk : ∀ k : JIdx d, Real.log ‖adaptedCoeff d c C k‖ ≤
      d * phiMin ((k.val : ℝ) / d) + 176 * tMax + d * omegaU h + Ch := by
    intro k
    have hmin : Real.log ‖adaptedCoeff d c C k‖ - (d * omegaU h + Ch) ≤
        Finset.univ.inf' Finset.univ_nonempty
          (fun i : Fin 6 => d * energyW i - (jump d c k : ℝ) * circleT i) :=
      Finset.le_inf' _ _ fun i _ => by linarith [hbound i k (hne k)]
    have := jump_min_le d c k
    rw [inf_scaled hd ((k.val : ℕ) : ℝ)] at this
    linarith
  have hsum := Finset.sum_le_sum fun k (_ : k ∈ Finset.univ) => hk k
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    sum_jidx_eq (fun j => (d : ℝ) * phiMin ((j : ℝ) / d))] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, card_blockIndex,
    nsmul_eq_mul] at hsum
  have hsc : ∑ j ∈ Finset.range (7 * d), (d : ℝ) * phiMin ((j : ℝ) / d) =
      (d : ℝ) ^ 2 * ∑ j ∈ Finset.range (7 * d), (d : ℝ)⁻¹ * phiMin (j / d) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    field_simp
  rw [hlog]
  push_cast at hsum
  nlinarith [hsum, hsc]

/-- **C30**: for every rational `c` and every `ε > 0`, eventually
`log |D_d| ≤ (∫_0^7 φ - (7/2) I + ε) d²` for the unchanged determinant. -/
theorem c30 (c : ℚ) {ε : ℝ} (hε : 0 < ε) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀,
      Real.log |(Zeta7Common.actualCommonDeterminant d c : ℝ)| ≤
        ((∫ k in (0 : ℝ)..7, phiMin k) - 7 / 2 * energyI + ε) * (d : ℝ) ^ 2 := by
  -- choose `h` with `7 ω(h) ≤ ε/3`
  have hω := (omegaU_tendsto.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ε / 21))).and
    (Ioo_mem_nhdsGT (one_pos : (0 : ℝ) < 1))
  obtain ⟨h, hωh, hh0, hh1⟩ := hω.exists
  obtain ⟨Ch, hCh⟩ := log_det_le c hh0 hh1.le
  set A : ℝ := |7 * tMax + 7 * (176 * tMax + Ch)| with hA
  have hG := (gram_log_limsup (by positivity : (0 : ℝ) < 2 * ε / 21)).and
    ((eventually_ge_atTop 1).and (eventually_ge_atTop ⌈3 * A / ε⌉₊))
  obtain ⟨d₀, hd₀⟩ := eventually_atTop.mp hG
  refine ⟨d₀, fun d hd => ?_⟩
  obtain ⟨hlogG, hd1, hdA⟩ := hd₀ d hd
  have hdpos : 0 < d := hd1
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  have hmain := hCh d hdpos
  have hR := riemann_sum_bound hdpos
  have hR' : ∑ j ∈ Finset.range (7 * d), (d : ℝ)⁻¹ * phiMin (j / d) ≤
      (∫ k in (0 : ℝ)..7, phiMin k) + 7 * tMax / d := by
    linarith [le_abs_self (∑ j ∈ Finset.range (7 * d), (d : ℝ)⁻¹ * phiMin (j / d) -
      ∫ k in (0 : ℝ)..7, phiMin k)]
  have hω0 : 0 ≤ omegaU h := omegaU_nonneg hh0.le
  have hdA' : 3 * A / ε ≤ d := (Nat.le_ceil _).trans (by exact_mod_cast hdA)
  have hlin : 7 * tMax * d + 7 * d * (176 * tMax + Ch) ≤ ε / 3 * (d : ℝ) ^ 2 := by
    have h1 : 7 * tMax * d + 7 * d * (176 * tMax + Ch) ≤ A * d := by
      have : 7 * tMax * d + 7 * d * (176 * tMax + Ch) =
          (7 * tMax + 7 * (176 * tMax + Ch)) * d := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)
    have h2 : A ≤ ε / 3 * d := by
      rw [div_le_iff₀ hε] at hdA'; linarith
    nlinarith
  have hsq : (d : ℝ) ^ 2 * (7 * tMax / d) = 7 * tMax * d := by field_simp
  have hRd := mul_le_mul_of_nonneg_left hR' (sq_nonneg (d : ℝ))
  rw [mul_add, hsq] at hRd
  have hωd : 7 * (d : ℝ) ^ 2 * omegaU h ≤ ε / 3 * (d : ℝ) ^ 2 := by
    nlinarith [sq_nonneg (d : ℝ)]
  nlinarith [hmain, hlogG, hRd, hωd, hlin]

end Zeta7Arch

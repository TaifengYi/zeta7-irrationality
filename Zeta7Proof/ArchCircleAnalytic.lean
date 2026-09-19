import Zeta7Proof.ArchSublevel
import Zeta7Proof.ArchPulledSource

/-! C1, step 2: the actual coordinate on a circle is nowhere flat.

`xFun q = x(q)` is the actual coordinate `q ∏_{7∤m} (1-q^m)^{-4}` evaluated on the unit disc, and
`circFun r θ = x(r e^{iθ})`. We prove:

* `xFun` is not constant along any punctured neighbourhood of a point of the disc (identity
  theorem, together with `x(0) = 0` and `x(q) = q·(x/q)(q)` with `(x/q)(0) = 1`);
* `circFun r` is real-analytic and smooth in `θ` for `0 ≤ r < 1`;
* at every angle `θ₀` some derivative of order `k ≥ 1` of the real or of the imaginary part of
  `circFun r` is nonzero (`circFun_component_not_flat`). This is the local multiplicity statement
  used for the small-ball estimate; it holds at critical points and at self-intersections of the
  image curve alike, since it concerns only the parametrized map near `θ₀`. -/
noncomputable section
set_option autoImplicit false
namespace Zeta7Arch
open MeasureTheory Set Filter Topology Complex

/-- The actual coordinate `x(q)` on the unit disc. -/
def xFun (q : ℂ) : ℂ := evalQ xC q

theorem xFun_analytic : AnalyticOnNhd ℂ xFun (Metric.ball 0 1) := xC_tempered.analyticOnNhd

theorem xFun_zero : xFun 0 = 0 := by
  rw [xFun, evalQ_zero_point, xC_eq]; simp

theorem uC_tempered' : Tempered uC := xUnit_tempered

theorem xFun_eq_mul {q : ℂ} (hq : ‖q‖ < 1) : xFun q = q * evalQ uC q := by
  rw [xFun, xC_eq, ← pow_one (PowerSeries.X : PowerSeries ℂ),
    evalQ_mul (tempered_X_pow 1) uC_tempered' hq, evalQ_X_pow, pow_one]

/-- `x` is not constant along any punctured neighbourhood of a point of the disc. -/
theorem xFun_not_frequently_const {q₀ : ℂ} (hq₀ : q₀ ∈ Metric.ball (0 : ℂ) 1) (c : ℂ) :
    ¬ (∃ᶠ q in 𝓝[≠] q₀, xFun q = c) := by
  intro hfreq
  have hU : IsPreconnected (Metric.ball (0 : ℂ) 1) := (convex_ball 0 1).isPreconnected
  have heq := xFun_analytic.eqOn_of_preconnected_of_frequently_eq analyticOnNhd_const hU hq₀ hfreq
  have h0mem : (0 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := Metric.mem_ball_self one_pos
  have hc : c = 0 := by
    have h := heq h0mem
    rw [xFun_zero] at h
    exact h.symm
  have hcont : ContinuousAt (evalQ uC) 0 :=
    (uC_tempered'.analyticOnNhd 0 h0mem).continuousAt
  have h1 : evalQ uC 0 = 1 := by rw [evalQ_zero_point, uC_constant]
  have hev : ∀ᶠ q in 𝓝 (0 : ℂ), evalQ uC q ≠ 0 :=
    hcont.eventually_ne (by rw [h1]; exact one_ne_zero)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hev
  set ε : ℝ := min (δ / 2) (1 / 2) with hε
  have hε0 : 0 < ε := by positivity
  have hεδ : ε < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hε1 : ε < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hnorm : ‖(ε : ℂ)‖ = ε := by rw [Complex.norm_real, Real.norm_of_nonneg hε0.le]
  have hdist : dist (ε : ℂ) 0 < δ := by rw [dist_zero_right, hnorm]; exact hεδ
  have hmem : (ε : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
    rw [Metric.mem_ball, dist_zero_right, hnorm]; exact hε1
  have hx := heq hmem
  simp only at hx
  rw [hc, xFun_eq_mul (by rw [hnorm]; exact hε1)] at hx
  exact mul_ne_zero (by exact_mod_cast hε0.ne') (hball hdist) hx

/-! ### The coordinate on a circle -/

/-- The point `r e^{iθ}`. -/
def circlePt (r θ : ℝ) : ℂ := (r : ℂ) * exp (θ * I)

/-- `x(r e^{iθ})`. -/
def circFun (r θ : ℝ) : ℂ := xFun (circlePt r θ)

theorem norm_circlePt {r : ℝ} (hr : 0 ≤ r) (θ : ℝ) : ‖circlePt r θ‖ = r := by
  rw [circlePt, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
    Real.norm_of_nonneg hr]

theorem circlePt_mem {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (θ : ℝ) :
    circlePt r θ ∈ Metric.ball (0 : ℂ) 1 := by
  rw [Metric.mem_ball, dist_zero_right, norm_circlePt hr0]; exact hr1

theorem circlePt_analyticAt (r θ₀ : ℝ) : AnalyticAt ℝ (circlePt r) θ₀ := by
  unfold circlePt
  have h1 : AnalyticAt ℝ (fun θ : ℝ => (θ : ℂ) * I) θ₀ :=
    (Complex.ofRealCLM.analyticAt θ₀).mul analyticAt_const
  have h2 : AnalyticAt ℝ (fun θ : ℝ => exp ((θ : ℂ) * I)) θ₀ :=
    (analyticAt_cexp.restrictScalars (𝕜 := ℝ)).comp h1
  exact analyticAt_const.mul h2

theorem circFun_analyticAt {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (θ₀ : ℝ) :
    AnalyticAt ℝ (circFun r) θ₀ := by
  have hx : AnalyticAt ℂ xFun (circlePt r θ₀) := xFun_analytic _ (circlePt_mem hr0 hr1 θ₀)
  exact (hx.restrictScalars (𝕜 := ℝ)).comp (circlePt_analyticAt r θ₀)

theorem circFun_contDiff {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) : ContDiff ℝ ⊤ (circFun r) :=
  contDiff_iff_contDiffAt.mpr fun θ => (circFun_analyticAt hr0 hr1 θ).contDiffAt

theorem circFun_continuous {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) : Continuous (circFun r) :=
  (circFun_contDiff hr0 hr1).continuous

/-! ### Derivatives through continuous linear maps and constant shifts -/

theorem iteratedDeriv_clm_comp {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (φ : E →L[ℝ] F) {g : ℝ → E}
    (hg : ∀ j, Differentiable ℝ (iteratedDeriv j g)) (k : ℕ) :
    iteratedDeriv k (fun t => φ (g t)) = fun t => φ (iteratedDeriv k g t) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ, ih, iteratedDeriv_succ]
    funext t
    exact (φ.hasFDerivAt.comp_hasDerivAt t ((hg k).differentiableAt.hasDerivAt)).deriv

theorem iteratedDeriv_sub_const {g : ℝ → ℝ} (a : ℝ) (k : ℕ) (hk : 1 ≤ k) :
    iteratedDeriv k (fun t => g t - a) = iteratedDeriv k g := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [iteratedDeriv_succ', iteratedDeriv_succ']
  congr 1
  funext t
  exact deriv_sub_const a

theorem differentiable_iteratedDeriv_of_contDiff {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {g : ℝ → E} (hg : ContDiff ℝ ⊤ g) (j : ℕ) :
    Differentiable ℝ (iteratedDeriv j g) :=
  hg.differentiable_iteratedDeriv j (WithTop.coe_lt_top _)

/-! ### Nowhere flat -/

/-- `circFun r` is not locally constant at any angle. -/
theorem circFun_not_eventually_const {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (θ₀ : ℝ) :
    ¬ (∀ᶠ θ in 𝓝 θ₀, circFun r θ = circFun r θ₀) := by
  intro hev
  -- the circle map is locally injective and continuous
  have hcont : Continuous (circlePt r) := by
    unfold circlePt; fun_prop
  have hinj : ∀ᶠ θ in 𝓝[≠] θ₀, circlePt r θ ∈ ({circlePt r θ₀}ᶜ : Set ℂ) := by
    have hball : ∀ᶠ θ in 𝓝[≠] θ₀, θ ∈ Metric.ball θ₀ 1 ∩ {θ₀}ᶜ := by
      filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds θ₀ one_pos),
        self_mem_nhdsWithin] with θ h1 h2
      exact ⟨h1, h2⟩
    filter_upwards [hball] with θ hθ
    intro heq
    have hne : θ ≠ θ₀ := hθ.2
    have hd : |θ - θ₀| < 1 := by simpa [Real.dist_eq] using hθ.1
    have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
    have hexp : exp (θ * I) = exp (θ₀ * I) := by
      have h := heq
      simp only [mem_singleton_iff, circlePt] at h
      exact mul_left_cancel₀ hr' h
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexp
    have hre : θ = θ₀ + n * (2 * Real.pi) := by
      have h := congrArg Complex.im hn
      simp at h
      linarith
    have hn0 : n = 0 := by
      by_contra hn0
      have h1 : (1 : ℝ) ≤ |(n : ℝ)| := by
        have : 1 ≤ |n| := Int.one_le_abs hn0
        exact_mod_cast this
      have h2 : |θ - θ₀| = |(n : ℝ)| * (2 * Real.pi) := by
        rw [hre, add_sub_cancel_left, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
      have hpi : (1 : ℝ) < 2 * Real.pi := by linarith [Real.pi_gt_three]
      nlinarith
    rw [hn0] at hre
    simp at hre
    exact hne hre
  have htend : Tendsto (circlePt r) (𝓝[≠] θ₀) (𝓝[≠] (circlePt r θ₀)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) hinj
  have hfreq : ∃ᶠ θ in 𝓝[≠] θ₀, xFun (circlePt r θ) = circFun r θ₀ :=
    (hev.filter_mono nhdsWithin_le_nhds).frequently
  exact xFun_not_frequently_const (circlePt_mem hr0.le hr1 θ₀) _
    (htend.frequently hfreq)

/-- Some derivative of order `≥ 1` of `circFun r` is nonzero at every angle. -/
theorem circFun_not_flat {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (θ₀ : ℝ) :
    ∃ k : ℕ, 1 ≤ k ∧ iteratedDeriv k (circFun r) θ₀ ≠ 0 := by
  by_contra hall
  push Not at hall
  set G : ℝ → ℂ := fun θ => circFun r θ - circFun r θ₀ with hG
  have hGa : AnalyticAt ℝ G θ₀ := (circFun_analyticAt hr0.le hr1 θ₀).sub analyticAt_const
  have hGd : ∀ i, iteratedDeriv i G θ₀ = 0 := by
    intro i
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp [hG]
    · obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
      rw [iteratedDeriv_succ']
      have hder : deriv G = deriv (circFun r) := by
        funext t; exact deriv_sub_const _
      rw [hder, ← iteratedDeriv_succ']
      exact hall (m + 1) (by omega)
  have htop : analyticOrderAt G θ₀ = ⊤ := by
    by_contra hne
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hne
    have hle := (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (n := m + 1) hGa).mpr
      (fun i _ => hGd i)
    rw [← hm] at hle
    exact absurd (by exact_mod_cast hle : m + 1 ≤ m) (by omega)
  have hev := analyticOrderAt_eq_top.mp htop
  exact circFun_not_eventually_const hr0 hr1 θ₀
    (hev.mono fun θ h => sub_eq_zero.mp h)

/-- **Local multiplicity.** At every angle, some derivative of order `k ≥ 1` of the real part or
of the imaginary part of `θ ↦ x(r e^{iθ})` is nonzero. -/
theorem circFun_component_not_flat {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (θ₀ : ℝ) :
    ∃ k : ℕ, 1 ≤ k ∧ ∃ φ : ℂ →L[ℝ] ℝ, (∀ w, |φ w| ≤ ‖w‖) ∧
      iteratedDeriv k (fun θ => φ (circFun r θ)) θ₀ ≠ 0 := by
  obtain ⟨k, hk, hne⟩ := circFun_not_flat hr0 hr1 θ₀
  have hsmooth := differentiable_iteratedDeriv_of_contDiff (circFun_contDiff hr0.le hr1)
  refine ⟨k, hk, ?_⟩
  by_cases hre : (iteratedDeriv k (circFun r) θ₀).re = 0
  · refine ⟨Complex.imCLM, fun w => Complex.abs_im_le_norm w, ?_⟩
    rw [iteratedDeriv_clm_comp Complex.imCLM hsmooth k]
    simp only [Complex.imCLM_apply]
    intro him
    exact hne (Complex.ext hre him)
  · refine ⟨Complex.reCLM, fun w => Complex.abs_re_le_norm w, ?_⟩
    rw [iteratedDeriv_clm_comp Complex.reCLM hsmooth k]
    simp only [Complex.reCLM_apply]
    exact hre

end Zeta7Arch

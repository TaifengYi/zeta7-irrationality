import Mathlib

/-! Uniqueness of the Weierstrass function from its invariants.

If two period pairs have the same invariants `g₂` and `g₃`, they span the same lattice.

* `hP_ode`: with `h = ℘ - 1/z²` (Mathlib's `℘[L - 0]`), the differential equation
  `℘'' = 6℘² - g₂/2` (obtained by differentiating `℘'² = 4℘³ - g₂℘ - g₃`) gives
  `z² h'' - 12 h - 6 z² h² + (g₂/2) z² = 0` on a neighbourhood of `0`.
* `iteratedDeriv_diff_eq_zero`: for two lattices with equal `g₂, g₃`, the difference
  `F = h_L - h_{L'}` satisfies `z² F'' = 12 F + 6 z² (h_L + h_{L'}) F`; by the Leibniz rule every
  Taylor coefficient satisfies `(n(n-1) - 12) F⁽ⁿ⁾(0) = 0` once the lower ones vanish, and the
  exceptional `n = 4` coefficient is `5! (G₆ - G₆') = 0`.
* `weierstrassP_eq_of_g`: hence `℘_L = ℘_{L'}` off both lattices (identity theorem on the
  connected complement of a countable set).
* `lattice_eq_of_g`: comparing the double poles, `L.lattice = L'.lattice`. -/
noncomputable section
set_option autoImplicit false
namespace Zeta7Valence
open Filter Topology PeriodPair

variable (L : PeriodPair)

/-- `h = ℘ - 1/z²`. -/
abbrev hP : ℂ → ℂ := L.weierstrassPExcept 0

theorem hP_analyticAt : AnalyticAt ℂ (hP L) 0 := L.analyticAt_weierstrassPExcept 0

theorem zero_mem_lattice : (0 : ℂ) ∈ L.lattice := L.lattice.zero_mem

theorem hP_eq (z : ℂ) : hP L z = L.weierstrassP z - (z ^ 2)⁻¹ := by
  have h := L.weierstrassPExcept_def ⟨0, zero_mem_lattice L⟩ z
  show L.weierstrassPExcept 0 z = _
  simp only [sub_zero] at h
  rw [h]
  simp
  ring

theorem hP_fun : hP L = fun w => L.weierstrassP w - (w ^ 2)⁻¹ := funext (hP_eq L)

theorem dP_eq (z : ℂ) : L.derivWeierstrassP z = L.derivWeierstrassPExcept 0 z - 2 / z ^ 3 := by
  have h := L.derivWeierstrassPExcept_def ⟨0, zero_mem_lattice L⟩ z
  simp only [sub_zero] at h
  rw [h]; ring

/-- A punctured neighbourhood of `0` free of lattice points. -/
theorem eventually_notMem : ∀ᶠ z in 𝓝[≠] (0 : ℂ), z ∉ L.lattice := by
  have h := L.compl_lattice_sdiff_singleton_mem_nhds 0
  filter_upwards [nhdsWithin_le_nhds h, self_mem_nhdsWithin] with z hz hz0
  intro hl
  exact hz ⟨hl, hz0⟩

/-- `℘'` does not vanish near `0`. -/
theorem eventually_dP_ne : ∀ᶠ z in 𝓝[≠] (0 : ℂ), L.derivWeierstrassP z ≠ 0 := by
  have hcont : ContinuousAt (fun z => z ^ 3 * L.derivWeierstrassPExcept 0 z - 2) 0 :=
    ((continuous_pow 3).continuousAt.mul
      (L.analyticAt_derivWeierstrassPExcept 0).continuousAt).sub continuousAt_const
  have h0 : (fun z : ℂ => z ^ 3 * L.derivWeierstrassPExcept 0 z - 2) 0 ≠ 0 := by simp
  have hev := hcont.eventually_ne h0
  filter_upwards [nhdsWithin_le_nhds hev, self_mem_nhdsWithin] with z hz hz0
  intro hd
  apply hz
  have hz3 : z ^ 3 ≠ 0 := pow_ne_zero 3 hz0
  rw [dP_eq] at hd
  have e : z ^ 3 * (L.derivWeierstrassPExcept 0 z - 2 / z ^ 3) =
      z ^ 3 * L.derivWeierstrassPExcept 0 z - 2 := by rw [mul_sub, mul_div_cancel₀ _ hz3]
  show z ^ 3 * L.derivWeierstrassPExcept 0 z - 2 = 0
  rw [← e, hd, mul_zero]

theorem hasDerivAt_P {z : ℂ} (hz : z ∉ L.lattice) :
    HasDerivAt L.weierstrassP (L.derivWeierstrassP z) z := by
  have := ((L.analyticOnNhd_weierstrassP z hz).differentiableAt).hasDerivAt
  rwa [deriv_weierstrassP] at this

/-- `℘'' = 6 ℘² - g₂/2` off the lattice where `℘' ≠ 0`. -/
theorem second_order {z : ℂ} (hz : z ∉ L.lattice) (hd : L.derivWeierstrassP z ≠ 0) :
    deriv L.derivWeierstrassP z = 6 * L.weierstrassP z ^ 2 - L.g₂ / 2 := by
  have hU : (L.lattice : Set ℂ)ᶜ ∈ 𝓝 z := L.isClosed_lattice.isOpen_compl.mem_nhds hz
  have heq : (fun w => L.derivWeierstrassP w ^ 2) =ᶠ[𝓝 z]
      fun w => 4 * L.weierstrassP w ^ 3 - L.g₂ * L.weierstrassP w - L.g₃ := by
    filter_upwards [hU] with w hw
    exact L.derivWeierstrassP_sq w hw
  have hdP : DifferentiableAt ℂ L.derivWeierstrassP z :=
    (L.analyticOnNhd_derivWeierstrassP z hz).differentiableAt
  have hP := hasDerivAt_P L hz
  have h1 := hdP.hasDerivAt.pow 2
  have h2 := (((hP.pow 3).const_mul 4).sub (hP.const_mul L.g₂)).sub_const L.g₃
  have h3 := h1.unique (h2.congr_of_eventuallyEq heq)
  norm_num at h3
  have : L.derivWeierstrassP z * (2 * deriv L.derivWeierstrassP z -
      (12 * L.weierstrassP z ^ 2 - L.g₂)) = 0 := by linear_combination h3
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h hd
  · linear_combination h / 2

theorem hasDerivAt_inv_sq {w : ℂ} (hw : w ≠ 0) :
    HasDerivAt (fun v : ℂ => (v ^ 2)⁻¹) (-(2 * (w ^ 3)⁻¹)) w := by
  refine ((hasDerivAt_pow 2 w).inv (pow_ne_zero 2 hw)).congr_deriv ?_
  field_simp
  ring

theorem hasDerivAt_two_inv_cube {w : ℂ} (hw : w ≠ 0) :
    HasDerivAt (fun v : ℂ => 2 * (v ^ 3)⁻¹) (-(6 * (w ^ 4)⁻¹)) w := by
  refine (((hasDerivAt_pow 3 w).inv (pow_ne_zero 3 hw)).const_mul 2).congr_deriv ?_
  field_simp
  ring

/-- The equation of `h` near `0`, off `0`. -/
theorem hP_ode_punctured : ∀ᶠ z in 𝓝[≠] (0 : ℂ),
    z ^ 2 * deriv (deriv (hP L)) z - 12 * hP L z - 6 * z ^ 2 * hP L z ^ 2 + L.g₂ / 2 * z ^ 2 = 0 := by
  have hopen : IsOpen ((L.lattice : Set ℂ)ᶜ ∩ {0}ᶜ) :=
    L.isClosed_lattice.isOpen_compl.inter isOpen_compl_singleton
  filter_upwards [eventually_notMem L, eventually_dP_ne L, self_mem_nhdsWithin] with z hz hd hz0
  have hz0' : z ≠ 0 := hz0
  have hmem : z ∈ (L.lattice : Set ℂ)ᶜ ∩ {0}ᶜ := ⟨hz, hz0'⟩
  have hd1 : ∀ w ∈ (L.lattice : Set ℂ)ᶜ ∩ {0}ᶜ,
      deriv (hP L) w = L.derivWeierstrassP w + 2 * (w ^ 3)⁻¹ := by
    intro w hw
    rw [hP_fun]
    exact ((hasDerivAt_P L hw.1).sub (hasDerivAt_inv_sq hw.2)).deriv.trans (by ring)
  have hd1ev : deriv (hP L) =ᶠ[𝓝 z] fun w => L.derivWeierstrassP w + 2 * (w ^ 3)⁻¹ :=
    Filter.eventually_of_mem (hopen.mem_nhds hmem) hd1
  have hdd : deriv (deriv (hP L)) z = deriv L.derivWeierstrassP z - 6 * (z ^ 4)⁻¹ := by
    rw [hd1ev.deriv_eq]
    have hdP : HasDerivAt L.derivWeierstrassP (deriv L.derivWeierstrassP z) z :=
      ((L.analyticOnNhd_derivWeierstrassP z hz).differentiableAt).hasDerivAt
    exact (hdP.add (hasDerivAt_two_inv_cube hz0')).deriv.trans (by ring)
  rw [hdd, second_order L hz hd, hP_eq L z]
  field_simp
  ring

/-- **The equation of `h` on a neighbourhood of `0`.** -/
theorem hP_ode : ∀ᶠ z in 𝓝 (0 : ℂ),
    z ^ 2 * deriv (deriv (hP L)) z - 12 * hP L z - 6 * z ^ 2 * hP L z ^ 2 + L.g₂ / 2 * z ^ 2 = 0 := by
  have h := hP_ode_punctured L
  rw [eventually_nhdsWithin_iff] at h
  filter_upwards [h] with z hz
  by_cases hz0 : z = 0
  · subst hz0; simp [hP]
  · exact hz hz0


/-! ### The Taylor recurrence -/

/-- The Taylor coefficients `h⁽ⁿ⁾(0)`. -/
abbrev tc (n : ℕ) : ℂ := iteratedDeriv n (hP L) 0

theorem iteratedDeriv_sq_mul {G : ℂ → ℂ} (hG : AnalyticAt ℂ G 0) (n : ℕ) :
    iteratedDeriv n (fun z => z ^ 2 * G z) 0 = (n.choose 2 : ℂ) * 2 * iteratedDeriv (n - 2) G 0 := by
  have hf : ContDiffAt ℂ n (fun z : ℂ => z ^ 2) 0 := (contDiff_id.pow 2).contDiffAt
  rw [iteratedDeriv_fun_mul hf hG.contDiffAt]
  rw [Finset.sum_eq_single 2]
  · simp [iteratedDeriv_fun_pow_zero]
  · intro b _ hb
    rw [iteratedDeriv_fun_pow_zero, if_neg hb]
    ring
  · intro h
    simp only [Finset.mem_range, not_lt] at h
    rw [Nat.choose_eq_zero_of_lt (by omega)]
    simp

theorem iteratedDeriv_dd (k : ℕ) :
    iteratedDeriv k (deriv (deriv (hP L))) 0 = tc L (k + 2) := by
  rw [tc, iteratedDeriv_succ', iteratedDeriv_succ']

theorem hP_mul_analytic : AnalyticAt ℂ (fun z => hP L z * hP L z) 0 :=
  (hP_analyticAt L).mul (hP_analyticAt L)

theorem dd_analytic : AnalyticAt ℂ (deriv (deriv (hP L))) 0 :=
  (hP_analyticAt L).deriv.deriv

theorem idsum4 {A B C D : ℂ → ℂ} (hA : AnalyticAt ℂ A 0) (hB : AnalyticAt ℂ B 0)
    (hC : AnalyticAt ℂ C 0) (hD : AnalyticAt ℂ D 0) (n : ℕ) :
    iteratedDeriv n (fun z => A z - B z - C z + D z) 0 =
      iteratedDeriv n A 0 - iteratedDeriv n B 0 - iteratedDeriv n C 0 + iteratedDeriv n D 0 := by
  have e : (fun z => A z - B z - C z + D z) = ((A - B) - C) + D := by funext z; simp
  rw [e, iteratedDeriv_add ((hA.sub hB).sub hC).contDiffAt hD.contDiffAt,
    iteratedDeriv_sub (hA.sub hB).contDiffAt hC.contDiffAt,
    iteratedDeriv_sub hA.contDiffAt hB.contDiffAt]

/-- **The recurrence** for the Taylor coefficients of `h = ℘ - 1/z²`. -/
theorem tc_rec (n : ℕ) :
    ((n.choose 2 : ℂ) * 2) * iteratedDeriv (n - 2) (deriv (deriv (hP L))) 0 - 12 * tc L n -
      6 * ((n.choose 2 : ℂ) * 2 * ∑ i ∈ Finset.range (n - 2 + 1),
        ((n - 2).choose i : ℂ) * tc L i * tc L (n - 2 - i)) +
      L.g₂ / 2 * ((n.choose 2 : ℂ) * 2 * (if n - 2 = 0 then 1 else 0)) = 0 := by
  have hode0 : (fun z => z ^ 2 * deriv (deriv (hP L)) z - 12 * hP L z - 6 * z ^ 2 * hP L z ^ 2 +
      L.g₂ / 2 * z ^ 2) =ᶠ[𝓝 0] fun _ => (0 : ℂ) := hP_ode L
  have hode := hode0.iteratedDeriv_eq n
  rw [iteratedDeriv_const] at hode
  have hfun : (fun z => z ^ 2 * deriv (deriv (hP L)) z - 12 * hP L z - 6 * z ^ 2 * hP L z ^ 2 +
      L.g₂ / 2 * z ^ 2) = fun z => z ^ 2 * deriv (deriv (hP L)) z - 12 * hP L z -
      6 * (z ^ 2 * (hP L z * hP L z)) + L.g₂ / 2 * (z ^ 2 * (fun _ => (1 : ℂ)) z) := by
    funext z; ring
  rw [hfun] at hode
  have a1 : AnalyticAt ℂ (fun z => z ^ 2 * deriv (deriv (hP L)) z) 0 :=
    (analyticAt_id.pow 2).mul (dd_analytic L)
  have a2 : AnalyticAt ℂ (fun z => 12 * hP L z) 0 := analyticAt_const.mul (hP_analyticAt L)
  have a3 : AnalyticAt ℂ (fun z => 6 * (z ^ 2 * (hP L z * hP L z))) 0 :=
    analyticAt_const.mul ((analyticAt_id.pow 2).mul (hP_mul_analytic L))
  have a4 : AnalyticAt ℂ (fun z => L.g₂ / 2 * (z ^ 2 * (fun _ => (1 : ℂ)) z)) 0 :=
    analyticAt_const.mul ((analyticAt_id.pow 2).mul analyticAt_const)
  have h4 := idsum4 a1 a2 a3 a4 n
  simp only at h4
  rw [h4] at hode
  rw [iteratedDeriv_const_mul_field, iteratedDeriv_const_mul_field, iteratedDeriv_const_mul_field,
    iteratedDeriv_sq_mul (dd_analytic L), iteratedDeriv_sq_mul (hP_mul_analytic L),
    iteratedDeriv_sq_mul analyticAt_const,
    iteratedDeriv_fun_mul (hP_analyticAt L).contDiffAt (hP_analyticAt L).contDiffAt,
    iteratedDeriv_const] at hode
  simpa using hode

theorem choose_two_mul_ne (n : ℕ) (hn : n ≠ 4) : ((n.choose 2 : ℂ) * 2) - 12 ≠ 0 := by
  intro h
  have h6 : ((n.choose 2 : ℕ) : ℂ) = 6 := by linear_combination h / 2
  have h6' : n.choose 2 = 6 := by exact_mod_cast h6
  rcases Nat.lt_or_ge n 5 with h5 | h5
  · interval_cases n <;> simp_all [Nat.choose]
  · have : Nat.choose 5 2 ≤ n.choose 2 := Nat.choose_le_choose 2 h5
    rw [h6'] at this
    simp [Nat.choose] at this

theorem tc_four : tc L 4 = 120 * L.G 6 := by
  rw [tc, hP, L.iteratedDeriv_weierstrassPExcept_self 0]
  simp [Nat.factorial]

variable (L₂ : PeriodPair)

/-- **Equal invariants give equal Taylor coefficients.** -/
theorem tc_eq (hg2 : L.g₂ = L₂.g₂) (hg3 : L.g₃ = L₂.g₃) : ∀ n, tc L n = tc L₂ n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h4 : n = 4
    · subst h4
      rw [tc_four, tc_four]
      have : L.G 6 = L₂.G 6 := by
        have := hg3; unfold PeriodPair.g₃ at this; linear_combination this / 140
      rw [this]
    · have r := tc_rec L n
      have r2 := tc_rec L₂ n
      rcases Nat.lt_or_ge n 2 with hn | hn
      · have hc : n.choose 2 = 0 := Nat.choose_eq_zero_of_lt hn
        simp only [hc, Nat.cast_zero, zero_mul, zero_sub, zero_add, mul_zero, sub_zero] at r r2
        linear_combination (r2 - r) / 12
      · have hk : n - 2 + 2 = n := by omega
        rw [iteratedDeriv_dd, hk] at r r2
        have hsum : ∑ i ∈ Finset.range (n - 2 + 1), ((n - 2).choose i : ℂ) * tc L i * tc L (n - 2 - i) =
            ∑ i ∈ Finset.range (n - 2 + 1), ((n - 2).choose i : ℂ) * tc L₂ i * tc L₂ (n - 2 - i) := by
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [Finset.mem_range] at hi
          rw [ih i (by omega), ih (n - 2 - i) (by omega)]
        rw [hsum, hg2] at r
        have hne := choose_two_mul_ne n h4
        have : ((n.choose 2 : ℂ) * 2 - 12) * (tc L n - tc L₂ n) = 0 := by linear_combination r - r2
        rcases mul_eq_zero.mp this with h | h
        · exact absurd h hne
        · linear_combination h

/-- The difference `h_L - h_{L₂}` vanishes near `0`. -/
theorem hP_diff_eventually (hg2 : L.g₂ = L₂.g₂) (hg3 : L.g₃ = L₂.g₃) :
    ∀ᶠ z in 𝓝 (0 : ℂ), hP L z = hP L₂ z := by
  have hF : AnalyticAt ℂ (fun z => hP L z - hP L₂ z) 0 := (hP_analyticAt L).sub (hP_analyticAt L₂)
  have hall : ∀ n : ℕ, iteratedDeriv n (fun z => hP L z - hP L₂ z) 0 = 0 := by
    intro n
    rw [iteratedDeriv_fun_sub (hP_analyticAt L).contDiffAt (hP_analyticAt L₂).contDiffAt]
    exact sub_eq_zero.mpr (tc_eq L L₂ hg2 hg3 n)
  have htop : analyticOrderAt (fun z => hP L z - hP L₂ z) 0 = ⊤ := by
    by_contra h
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp h
    have := (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hF (n := m + 1)).mpr
      fun i _ => hall i
    rw [← hm] at this
    norm_cast at this
    omega
  filter_upwards [analyticOrderAt_eq_top.mp htop] with z hz
  exact sub_eq_zero.mp hz

theorem weierstrassP_eventually (hg2 : L.g₂ = L₂.g₂) (hg3 : L.g₃ = L₂.g₃) :
    ∀ᶠ z in 𝓝 (0 : ℂ), L.weierstrassP z = L₂.weierstrassP z := by
  filter_upwards [hP_diff_eventually L L₂ hg2 hg3] with z hz
  have h1 := hP_eq L z
  have h2 := hP_eq L₂ z
  rw [hz] at h1
  linear_combination h2 - h1

/-- **`℘_L = ℘_{L₂}` off both lattices.** -/
theorem weierstrassP_eqOn (hg2 : L.g₂ = L₂.g₂) (hg3 : L.g₃ = L₂.g₃) :
    Set.EqOn L.weierstrassP L₂.weierstrassP ((L.lattice : Set ℂ) ∪ L₂.lattice)ᶜ := by
  set U : Set ℂ := ((L.lattice : Set ℂ) ∪ L₂.lattice)ᶜ with hU
  have hA : AnalyticOnNhd ℂ L.weierstrassP U := fun z hz =>
    L.analyticOnNhd_weierstrassP z fun h => hz (Or.inl h)
  have hA2 : AnalyticOnNhd ℂ L₂.weierstrassP U := fun z hz =>
    L₂.analyticOnNhd_weierstrassP z fun h => hz (Or.inr h)
  have hcount : ((L.lattice : Set ℂ) ∪ L₂.lattice).Countable :=
    Set.Countable.union (countable_of_Lindelof_of_discrete (X := L.lattice))
      (countable_of_Lindelof_of_discrete (X := L₂.lattice))
  have hconn : IsPreconnected U :=
    (Set.Countable.isConnected_compl_of_one_lt_rank (by simp) hcount).isPreconnected
  have hE := weierstrassP_eventually L L₂ hg2 hg3
  have hN : ∀ᶠ z in 𝓝 (0 : ℂ),
      (z ∈ (L.lattice : Set ℂ) → z = 0) ∧ (z ∈ (L₂.lattice : Set ℂ) → z = 0) := by
    filter_upwards [L.compl_lattice_sdiff_singleton_mem_nhds 0,
      L₂.compl_lattice_sdiff_singleton_mem_nhds 0] with z h1 h2
    exact ⟨fun h => by by_contra hz; exact h1 ⟨h, hz⟩, fun h => by by_contra hz; exact h2 ⟨h, hz⟩⟩
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp (hE.and hN)
  set z₀ : ℂ := ((ε / 2 : ℝ) : ℂ) with hz₀
  have hz₀0 : z₀ ≠ 0 := by
    rw [hz₀]; exact_mod_cast (by positivity : (ε / 2 : ℝ) ≠ 0)
  have hz₀ball : z₀ ∈ Metric.ball (0 : ℂ) ε := by
    rw [Metric.mem_ball, dist_zero_right, hz₀, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
    linarith
  have hz₀U : z₀ ∈ U := by
    rintro (h | h)
    · exact hz₀0 ((hball z₀ hz₀ball).2.1 h)
    · exact hz₀0 ((hball z₀ hz₀ball).2.2 h)
  refine hA.eqOn_of_preconnected_of_eventuallyEq hA2 hconn hz₀U ?_
  filter_upwards [Metric.isOpen_ball.mem_nhds hz₀ball] with z hz
  exact (hball z hz).1

theorem lattice_subset_of_g (hg2 : L.g₂ = L₂.g₂) (hg3 : L.g₃ = L₂.g₃) :
    (L.lattice : Set ℂ) ⊆ L₂.lattice := by
  intro l hl
  by_contra hl2
  have heq := weierstrassP_eqOn L L₂ hg2 hg3
  have hev : L.weierstrassP =ᶠ[𝓝[≠] l] L₂.weierstrassP := by
    have h1 : ((L.lattice : Set ℂ) \ {l})ᶜ ∈ 𝓝 l := L.compl_lattice_sdiff_singleton_mem_nhds l
    have h2 : (L₂.lattice : Set ℂ)ᶜ ∈ 𝓝 l := L₂.isClosed_lattice.isOpen_compl.mem_nhds hl2
    filter_upwards [nhdsWithin_le_nhds h1, nhdsWithin_le_nhds h2, self_mem_nhdsWithin]
      with z hz1 hz2 hz3
    refine heq ?_
    rintro (h | h)
    · exact hz1 ⟨h, hz3⟩
    · exact hz2 h
  have ho := L.order_weierstrassP l hl
  rw [meromorphicOrderAt_congr hev] at ho
  have hnn := (L₂.analyticOnNhd_weierstrassP l hl2).meromorphicOrderAt_nonneg
  rw [ho] at hnn
  exact absurd hnn (by decide)

/-- **Equal invariants give equal lattices.** -/
theorem lattice_eq_of_g (hg2 : L.g₂ = L₂.g₂) (hg3 : L.g₃ = L₂.g₃) :
    (L.lattice : Set ℂ) = L₂.lattice :=
  Set.Subset.antisymm (lattice_subset_of_g L L₂ hg2 hg3) (lattice_subset_of_g L₂ L hg2.symm hg3.symm)

end Zeta7Valence

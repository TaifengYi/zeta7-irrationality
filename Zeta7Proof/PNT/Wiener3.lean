import Zeta7Proof.PNT.Wiener2

/- Ported from PrimeNumberTheoremAnd (https://github.com/AlexKontorovich/PrimeNumberTheoremAnd),
commit a5040887e6bb24f7c201db8568e7755c138b3878, file `PrimeNumberTheoremAnd/Wiener.lean`, source lines 1047-1789.
Apache License 2.0 (see reference/pnt_audit_20260916/LICENSE). Adapted to the pinned Mathlib;
declarations live in the namespace `Zeta7PNT`. -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open Real BigOperators ArithmeticFunction MeasureTheory Filter Set LSeries Asymptotics SchwartzMap
open Complex hiding log
open scoped Topology ContDiff

namespace Zeta7PNT

variable {n : ℕ} {A a b c d u x y t σ' : ℝ} {ψ Ψ : ℝ → ℂ} {F G : ℂ → ℂ} {f : ℕ → ℂ} {𝕜 : Type} [RCLike 𝕜]

/-%%
\begin{lemma}[Smooth Urysohn lemma]\label{smooth-ury}\lean{smooth_urysohn}\leanok  If $I$ is a closed interval contained in an open interval $J$, then there exists a smooth function $\Psi: \R \to \R$ with $1_I \leq \Psi \leq 1_J$.
\end{lemma}
%%-/

lemma smooth_urysohn (a b c d : ℝ) (h1 : a < b) (h3 : c < d) : ∃ Ψ : ℝ → ℝ,
    (ContDiff ℝ ∞ Ψ) ∧ (HasCompactSupport Ψ) ∧
      Set.indicator (Set.Icc b c) 1 ≤ Ψ ∧ Ψ ≤ Set.indicator (Set.Ioo a d) 1 := by

  obtain ⟨ψ, l1, l2, l3, l4, -⟩ := smooth_urysohn_support_Ioo h1 h3
  refine ⟨ψ, l1, l2, l3, l4⟩

/-%%
\begin{proof}  \leanok
A standard analysis lemma, which can be proven by convolving $1_K$ with a smooth approximation to the identity for some interval $K$ between $I$ and $J$. Note that we have ``SmoothBumpFunction''s on smooth manifolds in Mathlib, so this shouldn't be too hard...
\end{proof}
%%-/

noncomputable def exists_trunc : trunc := by
  choose ψ h1 h2 h3 h4 using smooth_urysohn (-2) (-1) (1) (2) (by linarith) (by linarith)
  exact ⟨⟨ψ, h1.of_le (by norm_cast), h2⟩, h3, h4⟩

lemma one_div_sub_one (n : ℕ) : 1 / (↑(n - 1) : ℝ) ≤ 2 / n := by
  match n with
  | 0 => simp
  | 1 => simp
  | n + 2 => { norm_cast ; rw [div_le_div_iff₀] <;> simp [mul_add] <;> linarith }

lemma quadratic_pos (a b c x : ℝ) (ha : 0 < a) (hΔ : discrim a b c < 0) : 0 < a * x ^ 2 + b * x + c := by
  have l1 : a * x ^ 2 + b * x + c = a * (x + b / (2 * a)) ^ 2 - discrim a b c / (4 * a) := by
    unfold discrim; field_simp_ring
  have l2 : 0 < - discrim a b c := by linarith
  rw [l1, sub_eq_add_neg, ← neg_div] ; positivity

noncomputable def pp (a x : ℝ) : ℝ := a ^ 2 * (x + 1) ^ 2 + (1 - a) * (1 + a)

noncomputable def pp' (a x : ℝ) : ℝ := a ^ 2 * (2 * (x + 1))

lemma pp_pos {a : ℝ} (ha : a ∈ Ioo (-1) 1) (x : ℝ) : 0 < pp a x := by
  simp [pp]
  have : 0 < 1 - a := by linarith [ha.2]
  have : 0 < 1 + a := by linarith [ha.1]
  positivity

lemma pp_deriv (a x : ℝ) : HasDerivAt (pp a) (pp' a x) x := by
  unfold pp pp'
  simpa using hasDerivAt_id x |>.add_const 1 |>.pow 2 |>.const_mul _

lemma pp_deriv_eq (a : ℝ) : deriv (pp a) = pp' a := by
  ext x ; exact pp_deriv a x |>.deriv

lemma pp'_deriv (a x : ℝ) : HasDerivAt (pp' a) (a ^ 2 * 2) x := by
  unfold pp'
  exact ((hasDerivAt_id x).add_const 1 |>.const_mul 2 |>.const_mul (a ^ 2)).congr_deriv (by ring)

lemma pp'_deriv_eq (a : ℝ) : deriv (pp' a) = fun _ => a ^ 2 * 2 := by
  ext x ; exact pp'_deriv a x |>.deriv

noncomputable def hh (a t : ℝ) : ℝ := (t * (1 + (a * log t) ^ 2))⁻¹

noncomputable def hh' (a t : ℝ) : ℝ := - pp a (log t) * hh a t ^ 2

lemma hh_nonneg (a : ℝ) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ hh a t := by dsimp only [hh] ; positivity

lemma hh_le (a t : ℝ) (ht : 0 ≤ t) : |hh a t| ≤ t⁻¹ := by
  by_cases h0 : t = 0
  · simp [hh, h0]
  replace ht : 0 < t := lt_of_le_of_ne ht (Ne.symm h0)
  unfold hh
  rw [abs_of_nonneg (by positivity)]
  apply inv_anti₀ ht
  nlinarith [sq_nonneg (a * log t)]

lemma hh_deriv (a : ℝ) {t : ℝ} (ht : t ≠ 0) : HasDerivAt (hh a) (hh' a t) t := by
  have e1 : t * (1 + (a * log t) ^ 2) ≠ 0 := mul_ne_zero ht (_root_.ne_of_lt (by positivity)).symm
  have l5 : HasDerivAt (fun t : ℝ => log t) t⁻¹ t := Real.hasDerivAt_log ht
  have l4 : HasDerivAt (fun t : ℝ => a * log t) (a * t⁻¹) t := l5.const_mul _
  have l3 : HasDerivAt (fun t : ℝ => (a * log t) ^ 2) (2 * a ^ 2 * t⁻¹ * log t) t := by
    refine (l4.pow 2).congr_deriv ?_
    ring
  have l2 : HasDerivAt (fun t : ℝ => 1 + (a * log t) ^ 2) (2 * a ^ 2 * t⁻¹ * log t) t := l3.const_add _
  have l1 : HasDerivAt (fun t : ℝ => t * (1 + (a * log t) ^ 2))
      (1 + 2 * a ^ 2 * log t + a ^ 2 * log t ^ 2) t := by
    refine ((hasDerivAt_id t).mul l2).congr_deriv ?_
    simp only [id]
    field_simp_ring
  refine (l1.inv e1).congr_deriv ?_
  unfold hh' hh pp
  field_simp_ring

lemma hh_continuous (a : ℝ) : ContinuousOn (hh a) (Ioi 0) :=
  fun t (ht : 0 < t) => (hh_deriv a ht.ne.symm).continuousAt.continuousWithinAt

lemma hh'_nonpos {a x : ℝ} (ha : a ∈ Ioo (-1) 1) : hh' a x ≤ 0 := by
  have := pp_pos ha (log x)
  simp only [hh', neg_mul, Left.neg_nonpos_iff, ge_iff_le]
  positivity

lemma hh_antitone {a : ℝ} (ha : a ∈ Ioo (-1) 1) : AntitoneOn (hh a) (Ioi 0) := by
  have l1 x (hx : x ∈ interior (Ioi 0)) : HasDerivWithinAt (hh a) (hh' a x) (interior (Ioi 0)) x := by
    have : x ≠ 0 := by contrapose! hx ; simp [hx]
    exact (hh_deriv a this).hasDerivWithinAt
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioi _) (hh_continuous _) l1 (fun x _ => hh'_nonpos ha)

noncomputable def gg (x i : ℝ) : ℝ := 1 / i * (1 + (1 / (2 * π) * log (i / x)) ^ 2)⁻¹

lemma gg_of_hh {x : ℝ} (hx : x ≠ 0) (i : ℝ) : gg x i = x⁻¹ * hh (1 / (2 * π)) (i / x) := by
  unfold gg hh
  by_cases hi : i = 0
  · simp [hi]
  · have h1 : 1 + (1 / (2 * π) * log (i / x)) ^ 2 ≠ 0 := by positivity
    field_simp

lemma gg_l1 {x : ℝ} (hx : 0 < x) (n : ℕ) : |gg x n| ≤ 1 / n := by
  simp only [gg_of_hh hx.ne.symm, one_div, mul_inv_rev, abs_mul]
  apply mul_le_mul le_rfl (hh_le _ _ (by positivity)) (by positivity) (by positivity) |>.trans (le_of_eq ?_)
  rw [abs_inv, abs_of_pos hx]
  by_cases hn : (n : ℝ) = 0
  · simp [hn]
  · field_simp

lemma gg_le_one (i : ℕ) : gg x i ≤ 1 := by
  by_cases hi : i = 0 <;> simp [gg, hi]
  have l1 : 1 ≤ (i : ℝ) := by simp ; omega
  have l2 : 1 ≤ 1 + (π⁻¹ * 2⁻¹ * Real.log (↑i / x)) ^ 2 := by simp ; positivity
  rw [← mul_inv] ; apply inv_le_one_of_one_le₀ ; simpa using mul_le_mul l1 l2 zero_le_one (by simp)

lemma one_div_two_pi_mem_Ioo : 1 / (2 * π) ∈ Ioo (-1) 1 := by
  constructor
  · trans 0 ; linarith ; positivity
  · rw [div_lt_iff₀ (by positivity)]
    convert_to (config := {postTransparency := .all}) 1 * 1 < 2 * π ; simp ; simp
    apply mul_lt_mul one_lt_two ?_ zero_lt_one zero_le_two
    trans 2 ; exact one_le_two ; exact two_le_pi

lemma sum_telescopic (a : ℕ → ℝ) (n : ℕ) : ∑ i ∈ Finset.range n, (a (i + 1) - a i) = a n - a 0 :=
  Finset.sum_range_sub a n

/-- Abel summation sign lemma. This replaces the source's `cancel_aux` chain by a direct
induction: removing the last value of `g` keeps the weights antitone and nonnegative. -/
lemma abel_nonpos (d : ℕ → ℝ) (hD : ∀ k, ∑ j ∈ Finset.range k, d j ≤ 0) :
    ∀ (n : ℕ) (g : ℕ → ℝ), Antitone g → 0 ≤ g → ∑ i ∈ Finset.range n, d i * g i ≤ 0 := by
  intro n
  induction n with
  | zero => intros; simp
  | succ n ih =>
    intro g hg hg0
    have hc : 0 ≤ g n := hg0 n
    let g' : ℕ → ℝ := fun i => max (g i - g n) 0
    have hg' : Antitone g' := fun i j hij => max_le_max (by linarith [hg hij]) le_rfl
    have hg'0 : 0 ≤ g' := fun i => le_max_right _ _
    have e : ∀ i ∈ Finset.range n, d i * g i = d i * g' i + g n * d i := by
      intro i hi
      have hi' : g n ≤ g i := hg (by simp only [Finset.mem_range] at hi; omega)
      simp only [g']
      rw [max_eq_left (by linarith)]
      ring
    rw [Finset.sum_range_succ, Finset.sum_congr rfl e, Finset.sum_add_distrib, ← Finset.mul_sum]
    have h1 := ih g' hg' hg'0
    have h2 := hD (n + 1)
    rw [Finset.sum_range_succ] at h2
    have h3 := mul_nonpos_of_nonneg_of_nonpos hc h2
    rw [mul_add] at h3
    linarith

lemma cancel_general {C : ℝ} {f g : ℕ → ℝ} (hg : 0 ≤ g)
    (hf' : ∀ n, cumsum f n ≤ C * n) (hg' : Antitone g) (n : ℕ) :
    cumsum (f * g) n ≤ C * cumsum g n := by
  have h := abel_nonpos (fun i => f i - C) (fun k => by
      have := hf' k
      simp only [cumsum] at this
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      linarith) n g hg' hg
  have e : ∑ i ∈ Finset.range n, (f i - C) * g i =
      ∑ i ∈ Finset.range n, f i * g i - C * ∑ i ∈ Finset.range n, g i := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp only [cumsum, Pi.mul_apply]
  linarith

lemma cancel_main {C : ℝ} {f g : ℕ → ℝ} (_hf : 0 ≤ f) (hg : 0 ≤ g)
    (hf' : ∀ n, cumsum f n ≤ C * n) (hg' : Antitone g) (n : ℕ) (_hn : 2 ≤ n) :
    cumsum (f * g) n ≤ C * cumsum g n :=
  cancel_general hg hf' hg' n

lemma cancel_main' {C : ℝ} {f g : ℕ → ℝ} (_hf : 0 ≤ f) (_hf0 : f 0 = 0) (hg : 0 ≤ g)
    (hf' : ∀ n, cumsum f n ≤ C * n) (hg' : Antitone g) (n : ℕ) :
    cumsum (f * g) n ≤ C * cumsum g n :=
  cancel_general hg hf' hg' n

theorem sum_le_integral {x₀ : ℝ} {f : ℝ → ℝ} {n : ℕ} (hf : AntitoneOn f (Ioc x₀ (x₀ + n)))
    (hfi : IntegrableOn f (Icc x₀ (x₀ +  n))) :
    (∑ i ∈ Finset.range n, f (x₀ + ↑(i + 1))) ≤ ∫ x in x₀..x₀ + n, f x := by

  cases' n with n <;> simp at hf ⊢
  have : Finset.range (n + 1) = {0} ∪ Finset.Ico 1 (n + 1) := by
    ext i ; by_cases hi : i = 0 <;> simp [hi] ; omega
  simp [this, Finset.sum_union]

  have l4 : IntervalIntegrable f volume x₀ (x₀ + 1) := by
    apply IntegrableOn.intervalIntegrable
    simp only [le_add_iff_nonneg_right, zero_le_one, uIcc_of_le]
    apply hfi.mono_set
    apply Icc_subset_Icc ; linarith ; simp
  have l5 x (hx : x ∈ Ioc x₀ (x₀ + 1)) : (fun x ↦ f (x₀ + 1)) x ≤ f x := by
    rcases hx with ⟨hx1, hx2⟩
    refine hf ⟨hx1, by linarith⟩ ⟨by linarith, by linarith⟩ hx2
  have l6 : ∫ x in x₀..x₀ + 1, f (x₀ + 1) = f (x₀ + 1) := by simp

  have l1 : f (x₀ + 1) ≤ ∫ x in x₀..x₀ + 1, f x := by
    rw [← l6, intervalIntegral.integral_of_le (by linarith),
      intervalIntegral.integral_of_le (by linarith)]
    refine setIntegral_mono_on ?_ l4.1 measurableSet_Ioc l5
    exact integrableOn_const (by simp)

  have l2 : AntitoneOn (fun x ↦ f (x₀ + x)) (Icc 1 ↑(n + 1)) := by
    intro u ⟨hu1, _⟩ v ⟨_, hv2⟩ huv ; push_cast at hv2
    refine hf ⟨?_, ?_⟩ ⟨?_, ?_⟩ ?_ <;> linarith

  have l3 := @AntitoneOn.sum_le_integral_Ico 1 (n + 1) (fun x => f (x₀ + x)) (by simp) (by simpa using l2)

  simp at l3
  convert (config := {postTransparency := .all}) _root_.add_le_add l1 l3

  have := @intervalIntegral.integral_comp_mul_add ℝ _ _ 1 (n + 1) 1 f one_ne_zero x₀
  rw [intervalIntegral.integral_add_adjacent_intervals]
  · apply IntegrableOn.intervalIntegrable
    simp only [le_add_iff_nonneg_right, zero_le_one, uIcc_of_le]
    apply hfi.mono_set
    apply Icc_subset_Icc ; linarith ; simp
  · apply IntegrableOn.intervalIntegrable
    simp only [add_le_add_iff_left, le_add_iff_nonneg_left, Nat.cast_nonneg, uIcc_of_le]
    apply hfi.mono_set
    apply Icc_subset_Icc ; linarith ; simp

lemma hh_integrable_aux (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (IntegrableOn (fun t ↦ a * hh b (t / c)) (Ici 0)) ∧
    (∫ (t : ℝ) in Ioi 0, a * hh b (t / c) = a * c / b * π) := by

  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  simp only [hh]

  let g (x : ℝ) := (a * c / b) * Real.arctan (b * log (x / c))
  let g₀ (x : ℝ) := if x = 0 then ((a * c / b) * (- (π / 2))) else g x
  let g' (x : ℝ) := a * (x / c * (1 + (b * Real.log (x / c)) ^ 2))⁻¹

  have l3 (x) (hx : 0 < x) : HasDerivAt Real.log x⁻¹ x := by apply Real.hasDerivAt_log (by linarith)
  have l4 (x) : HasDerivAt (fun t => t / c) (1 / c) x := (hasDerivAt_id x).div_const c
  have l2 (x) (hx : 0 < x) : HasDerivAt (fun t => log (t / c)) x⁻¹ x := by
    have := @HasDerivAt.comp _ _ _ _ _ _ (fun t => t / c) _ _ _  (l3 (x / c) (by positivity)) (l4 x)
    refine this.congr_deriv ?_
    field_simp
  have l5 (x) (hx : 0 < x) := (l2 x hx).const_mul b
  have l1 (x) (hx : 0 < x) := (l5 x hx).arctan
  have l6 (x) (hx : 0 < x) : HasDerivAt g (g' x) x := by
    refine ((l1 x hx).const_mul (a * c / b)).congr_deriv ?_
    show a * c / b * (1 / (1 + (b * Real.log (x / c)) ^ 2) * (b * x⁻¹)) =
      a * (x / c * (1 + (b * Real.log (x / c)) ^ 2))⁻¹
    have h1 : 1 + (b * Real.log (x / c)) ^ 2 ≠ 0 := by positivity
    field_simp
  have key (x) (hx : 0 < x) : HasDerivAt g₀ (g' x) x := by
    apply (l6 x hx).congr_of_eventuallyEq
    apply eventually_of_mem <| Ioi_mem_nhds hx
    intro y (hy : 0 < y)
    simp [g₀, hy.ne.symm]

  have k1 : Tendsto g₀ atTop (𝓝 ((a * c / b) * (π / 2))) := by
    have : g =ᶠ[atTop] g₀ := by
      apply eventually_of_mem (Ioi_mem_atTop 0)
      intro y (hy : 0 < y)
      simp [g₀, hy.ne.symm]
    apply Tendsto.congr' this
    apply Tendsto.const_mul
    apply (tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp
    apply Tendsto.const_mul_atTop hb
    apply tendsto_log_atTop.comp
    apply Tendsto.atTop_div_const hc
    apply tendsto_id

  have k2 : Tendsto g₀ (𝓝[>] 0) (𝓝 (g₀ 0)) := by
    have : g =ᶠ[𝓝[>] 0] g₀ := by
      apply eventually_of_mem self_mem_nhdsWithin
      intro x (hx : 0 < x) ; simp [g₀, hx.ne.symm]
    simp only [g₀]
    apply Tendsto.congr' this
    apply Tendsto.const_mul
    apply (tendsto_arctan_atBot.mono_right nhdsWithin_le_nhds).comp
    apply Tendsto.const_mul_atBot hb
    apply tendsto_log_nhdsGT_zero.comp
    rw [Metric.tendsto_nhdsWithin_nhdsWithin]
    intro ε hε
    refine ⟨c * ε, by positivity, fun x hx1 hx2 => ⟨?_, ?_⟩⟩
    · simp at hx1 ⊢ ; positivity
    · simp [abs_eq_self.mpr hc.le] at hx2 ⊢ ; rwa [div_lt_iff₀ hc, mul_comm]

  have k3 : ContinuousWithinAt g₀ (Ici 0) 0 := by
    rw [Metric.continuousWithinAt_iff]
    rw [Metric.tendsto_nhdsWithin_nhds] at k2
    peel k2 with ε hε δ hδ x h
    intro (hx : 0 ≤ x)
    have := le_iff_lt_or_eq.mp hx
    cases this with
    | inl hx => exact h hx
    | inr hx => simp [g₀, hx.symm, hε]

  have k4 : ∀ x ∈ Ioi 0, 0 ≤ g' x := by
    intro x (hx : 0 < x) ; simp [g'] ; positivity

  constructor
  · convert_to (config := {postTransparency := .all}) IntegrableOn g' _
    exact integrableOn_Ioi_deriv_of_nonneg k3 key k4 k1
  · have := integral_Ioi_of_hasDerivAt_of_nonneg k3 key k4 k1
    simp only [mul_inv_rev, inv_div, mul_neg, ↓reduceIte, sub_neg_eq_add, g', g₀] at this ⊢
    convert (config := {postTransparency := .all}) this using 1 ; field_simp ; ring

lemma hh_integrable (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    IntegrableOn (fun t ↦ a * hh b (t / c)) (Ici 0) :=
  hh_integrable_aux ha hb hc |>.1

lemma hh_integral (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    ∫ (t : ℝ) in Ioi 0, a * hh b (t / c) = a * c / b * π :=
  hh_integrable_aux ha hb hc |>.2

lemma hh_integral' : ∫ t in Ioi 0, hh (1 / (2 * π)) t = 2 * π ^ 2 := by
  have := hh_integral (a := 1) (b := 1 / (2 * π)) (c := 1) (by positivity) (by positivity) (by positivity)
  convert (config := {postTransparency := .all}) this using 1 <;> simp ; ring

lemma bound_sum_log {C : ℝ} (hf0 : f 0 = 0) (hf : chebyWith C f) {x : ℝ} (hx : 1 ≤ x) :
    ∑' i, ‖f i‖ / i * (1 + (1 / (2 * π) * log (i / x)) ^ 2)⁻¹ ≤ C * (1 + ∫ t in Ioi 0, hh (1 / (2 * π)) t) := by

  let ggg (i : ℕ) : ℝ := if i = 0 then 1 else gg x i

  have l0 : x ≠ 0 := by linarith
  have l1 i : 0 ≤ ggg i := by by_cases hi : i = 0 <;> simp [ggg, hi, gg] ; positivity
  have l2 : Antitone ggg := by
    intro i j hij ; by_cases hi : i = 0 <;> by_cases hj : j = 0 <;> simp [ggg, hi, hj]
    · exact gg_le_one _
    · omega
    · simp only [gg_of_hh l0]
      gcongr
      apply hh_antitone one_div_two_pi_mem_Ioo
      · simp ; positivity
      · simp ; positivity
      · gcongr
  have l3 : 0 ≤ C := by simpa [cumsum, hf0] using hf 1

  have l4 : 0 ≤ ∫ (t : ℝ) in Ioi 0, hh (π⁻¹ * 2⁻¹) t :=
    setIntegral_nonneg measurableSet_Ioi (fun x hx => hh_nonneg _ (LT.lt.le hx))

  have l5 {n : ℕ} : AntitoneOn (fun t ↦ x⁻¹ * hh (1 / (2 * π)) (t / x)) (Ioc 0 n) := by
    intro u ⟨hu1, _⟩ v ⟨hv1, _⟩ huv
    simp only
    apply mul_le_mul le_rfl ?_ (hh_nonneg _ (by positivity)) (by positivity)
    apply hh_antitone one_div_two_pi_mem_Ioo (by simp ; positivity) (by simp ; positivity)
    apply (div_le_div_iff_of_pos_right (by positivity)).mpr huv

  have l6 {n : ℕ} : IntegrableOn (fun t ↦ x⁻¹ * hh (π⁻¹ * 2⁻¹) (t / x)) (Icc 0 n) volume := by
    apply IntegrableOn.mono_set (hh_integrable (by positivity) (by positivity) (by positivity)) Icc_subset_Ici_self

  apply Real.tsum_le_of_sum_range_le (fun n => by positivity) ; intro n
  convert_to (config := {postTransparency := .all}) ∑ i ∈ Finset.range n, ‖f i‖ * ggg i ≤ _
  · congr ; ext i
    by_cases hi : i = 0
    · simp [hi, hf0]
    · simp only [ggg, gg, if_neg hi]; ring

  apply cancel_main' (fun _ => norm_nonneg _) (by simp [hf0]) l1 hf l2 n |>.trans
  gcongr ; simp [ggg, cumsum, gg_of_hh l0]

  by_cases hn : n = 0 ; simp [hn] ; positivity
  replace hn : 0 < n := by omega
  have : Finset.range n = {0} ∪ Finset.Ico 1 n := by
    ext i ; simp ; by_cases hi : i = 0 <;> simp [hi, hn] ; omega
  simp [this, Finset.sum_union]
  convert_to (config := {postTransparency := .all}) ∑ x_1 ∈ Finset.Ico 1 n, x⁻¹ * hh (π⁻¹ * 2⁻¹) (↑x_1 / x) ≤ _
  · apply Finset.sum_congr rfl (fun i hi => ?_)
    simp at hi
    have : i ≠ 0 := by omega
    simp [this]
  simp_rw [Finset.sum_Ico_eq_sum_range, add_comm 1]
  have := @sum_le_integral 0 (fun t => x⁻¹ * hh (π⁻¹ * 2⁻¹) (t / x)) (n - 1) (by simpa using l5) (by simpa using l6)
  simp only [zero_add] at this
  apply this.trans
  rw [@intervalIntegral.integral_comp_div ℝ _ _ 0 ↑(n - 1) x (fun t => x⁻¹ * hh (π⁻¹ * 2⁻¹) (t)) l0]
  simp [← mul_assoc, mul_inv_cancel₀ l0]
  have : (0 : ℝ) ≤ ↑(n - 1) / x := by positivity
  rw [intervalIntegral.intervalIntegral_eq_integral_uIoc]
  simp [this]
  apply integral_mono_measure
  · apply Measure.restrict_mono Ioc_subset_Ioi_self le_rfl
  · apply eventually_of_mem (self_mem_ae_restrict measurableSet_Ioi)
    intro x (hx : 0 < x)
    apply hh_nonneg _ hx.le
  · have := (@hh_integrable 1 (1 / (2 * π)) 1 (by positivity) (by positivity) (by positivity))
    have h3 := this.mono_set Ioi_subset_Ici_self
    simp only [one_mul, div_one, one_div, mul_inv_rev] at h3
    exact h3

lemma bound_sum_log0 {C : ℝ} (hf : chebyWith C f) {x : ℝ} (hx : 1 ≤ x) :
    ∑' i, ‖f i‖ / i * (1 + (1 / (2 * π) * log (i / x)) ^ 2)⁻¹ ≤ C * (1 + ∫ t in Ioi 0, hh (1 / (2 * π)) t) := by

  let f0 i := if i = 0 then 0 else f i
  have l1 : chebyWith C f0 := by
    intro n ; refine Finset.sum_le_sum (fun i _ => ?_) |>.trans (hf n)
    by_cases hi : i = 0 <;> simp [hi, f0]
  have l2 i : ‖f i‖ / i = ‖f0 i‖ / i := by by_cases hi : i = 0 <;> simp [hi, f0]
  simp_rw [l2] ; apply bound_sum_log rfl l1 hx

lemma bound_sum_log' {C : ℝ} (hf : chebyWith C f) {x : ℝ} (hx : 1 ≤ x) :
    ∑' i, ‖f i‖ / i * (1 + (1 / (2 * π) * log (i / x)) ^ 2)⁻¹ ≤ C * (1 + 2 * π ^ 2) := by
  simpa only [hh_integral'] using bound_sum_log0 hf hx

lemma summable_fourier (x : ℝ) (hx : 0 < x) (ψ : W21) (hcheby : cheby f) :
    Summable fun i ↦ ‖f i / ↑i * 𝓕 ψ (1 / (2 * π) * Real.log (↑i / x))‖ := by
  have l5 : Summable fun i : ℕ ↦ ‖f i‖ / i * (1 + (1 / (2 * π) * Real.log (i / x)) ^ 2)⁻¹ := by
    have := limiting_fourier_lim1_aux hcheby hx 1 zero_le_one
    simp only [one_div] at this ⊢
    exact this
  have l6 i : ‖f i / i * 𝓕 ψ (1 / (2 * π) * Real.log (i / x))‖ ≤
      W21.norm ψ * (‖f i‖ / i * (1 + (1 / (2 * π) * log (i / x)) ^ 2)⁻¹) := by
    convert (config := {postTransparency := .all}) mul_le_mul_of_nonneg_left (decay_bounds_key ψ (1 / (2 * π) * log (i / x))) (norm_nonneg (f i / i)) using 1
    · simp
    · change _ = _ * (W21.norm ψ * _) ; simp [W21.norm] ; ring
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) l6 (l5.mul_left _)

lemma bound_I1 (x : ℝ) (hx : 0 < x) (ψ : W21) (hcheby : cheby f) :
    ‖∑' n, f n / n * 𝓕 ψ (1 / (2 * π) * log (n / x))‖ ≤
    W21.norm ψ • ∑' i, ‖f i‖ / i * (1 + (1 / (2 * π) * log (i / x)) ^ 2)⁻¹ := by

  have l5 : Summable fun i : ℕ ↦ ‖f i‖ / i * (1 + (1 / (2 * π) * Real.log (i / x)) ^ 2)⁻¹ := by
    have := limiting_fourier_lim1_aux hcheby hx 1 zero_le_one
    simp only [one_div] at this ⊢
    exact this
  have l6 i : ‖f i / i * 𝓕 ψ (1 / (2 * π) * Real.log (i / x))‖ ≤
      W21.norm ψ * (‖f i‖ / i * (1 + (1 / (2 * π) * log (i / x)) ^ 2)⁻¹) := by
    convert (config := {postTransparency := .all}) mul_le_mul_of_nonneg_left (decay_bounds_key ψ (1 / (2 * π) * log (i / x))) (norm_nonneg (f i / i)) using 1
    · simp
    · change _ = _ * (W21.norm ψ * _) ; simp [W21.norm] ; ring
  have l1 : Summable fun i ↦ ‖f i / ↑i * 𝓕 ψ (1 / (2 * π) * Real.log (↑i / x))‖ := by
    exact summable_fourier x hx ψ hcheby
  apply (norm_tsum_le_tsum_norm l1).trans
  have := Summable.tsum_mono l1 (l5.mul_left (W21.norm ψ)) l6
  rw [tsum_mul_left] at this
  simpa [smul_eq_mul] using this

lemma bound_I1' {C : ℝ} (x : ℝ) (hx : 1 ≤ x) (ψ : W21) (hcheby : chebyWith C f) :
    ‖∑' n, f n / n * 𝓕 ψ (1 / (2 * π) * log (n / x))‖ ≤ W21.norm ψ * C * (1 + 2 * π ^ 2) := by

  apply bound_I1 x (by linarith) ψ ⟨_, hcheby⟩ |>.trans
  rw [smul_eq_mul, mul_assoc]
  apply mul_le_mul le_rfl (bound_sum_log' hcheby hx) ?_ W21.norm_nonneg
  apply tsum_nonneg (fun i => by positivity)

lemma bound_I2 (x : ℝ) (ψ : W21) :
    ‖∫ u in Set.Ici (-log x), 𝓕 ψ (u / (2 * π))‖ ≤ W21.norm ψ * (2 * π ^ 2) := by

  have key a : ‖𝓕 ψ (a / (2 * π))‖ ≤ W21.norm ψ * (1 + (a / (2 * π)) ^ 2)⁻¹ := decay_bounds_key ψ _
  have twopi : 0 ≤ 2 * π := by simp [pi_nonneg]
  have l3 : Integrable (fun a ↦ (1 + (a / (2 * π)) ^ 2)⁻¹) := integrable_inv_one_add_sq.comp_div (by norm_num [pi_ne_zero])
  have l2 : IntegrableOn (fun i ↦ W21.norm ψ * (1 + (i / (2 * π)) ^ 2)⁻¹) (Ici (-Real.log x)) := by
    exact (l3.const_mul _).integrableOn
  have l1 : IntegrableOn (fun i ↦ ‖𝓕 ψ (i / (2 * π))‖) (Ici (-Real.log x)) := by
    refine ((l3.const_mul (W21.norm ψ)).mono' ?_ ?_).integrableOn
    · apply Continuous.aestronglyMeasurable ; continuity
    · simp only [norm_norm, key] ; simp
  have l5 : 0 ≤ᵐ[volume] fun a ↦ (1 + (a / (2 * π)) ^ 2)⁻¹ := by apply Eventually.of_forall ; intro x ; positivity
  refine (norm_integral_le_integral_norm _).trans <| (setIntegral_mono l1 l2 key).trans ?_
  rw [integral_const_mul] ; gcongr ; apply W21.norm_nonneg
  refine (setIntegral_le_integral l3 l5).trans ?_
  rw [Measure.integral_comp_div (fun x => (1 + x ^ 2)⁻¹) (2 * π)]
  simp [abs_eq_self.mpr twopi] ; ring_nf ; rfl

lemma bound_main {C : ℝ} (A : ℂ) (x : ℝ) (hx : 1 ≤ x) (ψ : W21)
    (hcheby : chebyWith C f) :
    ‖∑' n, f n / n * 𝓕 ψ (1 / (2 * π) * log (n / x)) -
      A * ∫ u in Set.Ici (-log x), 𝓕 ψ (u / (2 * π))‖ ≤
      W21.norm ψ * (C * (1 + 2 * π ^ 2) + ‖A‖ * (2 * π ^ 2)) := by

  have l1 := bound_I1' x hx ψ hcheby
  have l2 := mul_le_mul (le_refl ‖A‖) (bound_I2 x ψ) (by positivity) (by positivity)
  apply norm_sub_le _ _ |>.trans ; rw [norm_mul]
  convert (config := {postTransparency := .all}) _root_.add_le_add l1 l2 using 1 ; ring

/-%%
\begin{lemma}[Limiting identity for Schwartz functions]\label{schwarz-id}\lean{limiting_cor_schwartz}\leanok  The previous corollary also holds for functions $\psi$ that are assumed to be in the Schwartz class, as opposed to being $C^2$ and compactly supported.
\end{lemma}
%%-/

lemma limiting_cor_W21 (ψ : W21) (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hcheby : cheby f) (hG: ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re}) :
    Tendsto (fun x : ℝ ↦ ∑' n, f n / n * 𝓕 ψ (1 / (2 * π) * log (n / x)) -
      A * ∫ u in Set.Ici (-log x), 𝓕 ψ (u / (2 * π))) atTop (𝓝 0) := by

  -- Shorter notation for clarity
  let S1 x (ψ : ℝ → ℂ) := ∑' (n : ℕ), f n / ↑n * 𝓕 ψ (1 / (2 * π) * Real.log (↑n / x))
  let S2 x (ψ : ℝ → ℂ) := ↑A * ∫ (u : ℝ) in Ici (-Real.log x), 𝓕 ψ (u / (2 * π))
  let S x ψ := S1 x ψ - S2 x ψ ; change Tendsto (fun x ↦ S x ψ) atTop (𝓝 0)

  -- Build the truncation
  obtain g := exists_trunc
  let Ψ R := g.scale R * ψ
  have key R : Tendsto (fun x ↦ S x (Ψ R)) atTop (𝓝 0) := limiting_cor (Ψ R) hf hcheby hG hG'

  -- Choose the truncation radius
  obtain ⟨C, hcheby⟩ := hcheby
  have hC : 0 ≤ C := by
    have : ‖f 0‖ ≤ C := by simpa [cumsum] using hcheby 1
    have : 0 ≤ ‖f 0‖ := by positivity
    linarith
  have key2 : Tendsto (fun R ↦ W21.norm (ψ - Ψ R)) atTop (𝓝 0) := W21_approximation ψ g
  simp_rw [Metric.tendsto_nhds] at key key2 ⊢ ; intro ε hε
  let M := C * (1 + 2 * π ^ 2) + ‖(A : ℂ)‖ * (2 * π ^ 2)
  obtain ⟨R, hRψ⟩ := (key2 ((ε / 2) / (1 + M)) (by positivity)).exists
  simp only [dist_zero_right, Real.norm_eq_abs, abs_eq_self.mpr W21.norm_nonneg] at hRψ key

  -- Apply the compact support case
  filter_upwards [eventually_ge_atTop 1, key R (ε / 2) (by positivity)] with x hx key

  -- Control the tail term
  have key3 : ‖S x (ψ - Ψ R)‖ < ε / 2 := by
    have : ‖S x _‖ ≤ _ * M := @bound_main f C A x hx (ψ - Ψ R) hcheby
    apply this.trans_lt
    apply (mul_le_mul (d := 1 + M) le_rfl (by simp) (by positivity) W21.norm_nonneg).trans_lt
    have : 0 < 1 + M := by positivity
    exact (lt_div_iff₀ this).mp hRψ

  -- Conclude the proof
  have S1_sub_1 x : 𝓕 (⇑ψ - ⇑(Ψ R)) x = 𝓕 ψ x - 𝓕 (Ψ R) x := by
    have l1 : AEStronglyMeasurable (fun x_1 : ℝ ↦ cexp (-(2 * ↑π * (↑x_1 * ↑x) * I))) volume := by
      refine (Continuous.mul ?_ continuous_const).neg.cexp.aestronglyMeasurable
      apply continuous_const.mul <| contDiff_ofReal.continuous.mul continuous_const
    simp only [fourierIntegral_eq', neg_mul, RCLike.inner_apply', conj_trivial, ofReal_neg,
      ofReal_mul, ofReal_ofNat, Pi.sub_apply, smul_eq_mul, mul_sub]
    apply integral_sub
    · exact ψ.hf.bdd_mul l1 (c := 1) (Eventually.of_forall fun y => by simp [Complex.norm_exp])
    · exact (Ψ R : W21).hf.bdd_mul l1 (c := 1) (Eventually.of_forall fun y => by simp [Complex.norm_exp])

  have S1_sub : S1 x (ψ - Ψ R) = S1 x ψ - S1 x (Ψ R) := by
    simp [S1, S1_sub_1, mul_sub] ; apply Summable.tsum_sub
    · have := summable_fourier x (by positivity) ψ ⟨_, hcheby⟩
      rw [summable_norm_iff] at this
      simp only [one_div, mul_inv_rev] at this
      exact this
    · have := summable_fourier x (by positivity) (Ψ R) ⟨_, hcheby⟩
      rw [summable_norm_iff] at this
      simp only [one_div, mul_inv_rev] at this
      exact this

  have S2_sub : S2 x (ψ - Ψ R) = S2 x ψ - S2 x (Ψ R) := by
    simp [S2, S1_sub_1] ; rw [integral_sub] ; ring
    · exact ψ.integrable_fourier (by positivity) |>.restrict
    · exact (Ψ R : W21).integrable_fourier (by positivity) |>.restrict

  have S_sub : S x (ψ - Ψ R) = S x ψ - S x (Ψ R) := by simp [S, S1_sub, S2_sub] ; ring
  simpa [S_sub, Ψ] using norm_add_le _ _ |>.trans_lt (_root_.add_lt_add key3 key)

lemma limiting_cor_schwartz (ψ : 𝓢(ℝ, ℂ)) (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hcheby : cheby f) (hG: ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re}) :
    Tendsto (fun x : ℝ ↦ ∑' n, f n / n * 𝓕 ψ (1 / (2 * π) * log (n / x)) -
      A * ∫ u in Set.Ici (-log x), 𝓕 ψ (u / (2 * π))) atTop (𝓝 0) :=
  limiting_cor_W21 ψ hf hcheby hG hG'

/-%%
\begin{proof}
\uses{limiting-cor, smooth-ury}\leanok
For any $R>1$, one can use a smooth cutoff function (provided by Lemma \ref{smooth-ury} to write $\psi = \psi_{\leq R} + \psi_{>R}$, where $\psi_{\leq R}$ is $C^2$ (in fact smooth) and compactly supported (on $[-R,R]$), and $\psi_{>R}$ obeys bounds of the form
$$ |\psi_{>R}(t)|, |\psi''_{>R}(t)| \ll R^{-1} / (1 + |t|^2) $$
where the implied constants depend on $\psi$.  By Lemma \ref{decay} we then have
$$ \hat \psi_{>R}(u) \ll R^{-1} / (1+|u|^2).$$
Using this and \eqref{cheby} one can show that
$$ \sum_{n=1}^\infty \frac{f(n)}{n} \hat \psi_{>R}( \frac{1}{2\pi} \log \frac{n}{x} ), A \int_{-\infty}^\infty \hat \psi_{>R} (\frac{u}{2\pi})\ du \ll R^{-1} $$
(with implied constants also depending on $A$), while from Lemma \ref{limiting-cor} one has
$$ \sum_{n=1}^\infty \frac{f(n)}{n} \hat \psi_{\leq R}( \frac{1}{2\pi} \log \frac{n}{x} ) = A \int_{-\infty}^\infty \hat \psi_{\leq R} (\frac{u}{2\pi})\ du + o(1).$$
Combining the two estimates and letting $R$ be large, we obtain the claim.
\end{proof}
%%-/

/-%%
\begin{lemma}[Bijectivity of Fourier transform]\label{bij}\lean{fourier_surjection_on_schwartz}\leanok  The Fourier transform is a bijection on the Schwartz class. [Note: only surjectivity is actually used.]
\end{lemma}
%%-/

-- just the surjectivity is stated here, as this is all that is needed for the current application, but perhaps one should state and prove bijectivity instead

lemma fourier_surjection_on_schwartz (f : 𝓢(ℝ, ℂ)) : ∃ g : 𝓢(ℝ, ℂ), 𝓕 g = f := by
  refine ⟨FourierTransformInv.fourierInv f, ?_⟩
  show FourierTransform.fourier (⇑(FourierTransformInv.fourierInv f : 𝓢(ℝ, ℂ))) = ⇑f
  rw [← SchwartzMap.fourier_coe]
  exact congrArg (fun φ : 𝓢(ℝ, ℂ) => (φ : ℝ → ℂ)) (FourierInvPair.fourier_fourierInv_eq f)


/-%%
\begin{proof}
  \leanok
 This is a standard result in Fourier analysis.
It can be proved here by appealing to Mellin inversion, Theorem \ref{MellinInversion}.
In particular, given $f$ in the Schwartz class, let $F : \R_+ \to \C : x \mapsto f(\log x)$ be a function in the ``Mellin space''; then the Mellin transform of $F$ on the imaginary axis $s=it$ is the Fourier transform of $f$.  The Mellin inversion theorem gives Fourier inversion.
\end{proof}
%%-/

noncomputable def toSchwartz (f : ℝ → ℂ) (h1 : ContDiff ℝ ∞ f) (h2 : HasCompactSupport f) : 𝓢(ℝ, ℂ) where
  toFun := f
  smooth' := h1
  decay' k n := by
    have l1 : Continuous (fun x => ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖) := by
      have : ContDiff ℝ ∞ (iteratedFDeriv ℝ n f) := h1.iteratedFDeriv_right (mod_cast le_top)
      exact Continuous.mul (by continuity) this.continuous.norm
    have l2 : HasCompactSupport (fun x ↦ ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖) := (h2.iteratedFDeriv _).norm.mul_left
    simpa using l1.bounded_above_of_compact_support l2

@[simp] lemma toSchwartz_apply (f : ℝ → ℂ) {h1 h2 x} : SchwartzMap.mk f h1 h2 x = f x := rfl

@[simp] lemma toSchwartz_apply' (f : ℝ → ℂ) {h1 h2} (x : ℝ) : toSchwartz f h1 h2 x = f x := rfl

lemma comp_exp_support0 {Ψ : ℝ → ℂ} (hplus : closure (Function.support Ψ) ⊆ Ioi 0) :
    ∀ᶠ x in 𝓝 0, Ψ x = 0 :=
  notMem_tsupport_iff_eventuallyEq.mp (fun h => lt_irrefl 0 <| mem_Ioi.mp (hplus h))

lemma comp_exp_support1 {Ψ : ℝ → ℂ} (hplus : closure (Function.support Ψ) ⊆ Ioi 0) :
    ∀ᶠ x in atBot, Ψ (exp x) = 0 :=
  Real.tendsto_exp_atBot <| comp_exp_support0 hplus

lemma comp_exp_support2 {Ψ : ℝ → ℂ} (hsupp : HasCompactSupport Ψ) :
    ∀ᶠ (x : ℝ) in atTop, (Ψ ∘ rexp) x = 0 := by
  simp only [hasCompactSupport_iff_eventuallyEq, coclosedCompact_eq_cocompact, cocompact_eq_atBot_atTop] at hsupp
  exact Real.tendsto_exp_atTop hsupp.2

theorem comp_exp_support {Ψ : ℝ → ℂ} (hsupp : HasCompactSupport Ψ) (hplus : closure (Function.support Ψ) ⊆ Ioi 0) :
    HasCompactSupport (Ψ ∘ rexp) := by
  simp only [hasCompactSupport_iff_eventuallyEq, coclosedCompact_eq_cocompact, cocompact_eq_atBot_atTop]
  exact ⟨comp_exp_support1 hplus, comp_exp_support2 hsupp⟩

lemma wiener_ikehara_smooth_aux (l0 : Continuous Ψ) (hsupp : HasCompactSupport Ψ)
    (hplus : closure (Function.support Ψ) ⊆ Ioi 0) (x : ℝ) (hx : 0 < x) :
    ∫ (u : ℝ) in Ioi (-Real.log x), ↑(rexp u) * Ψ (rexp u) = ∫ (y : ℝ) in Ioi (1 / x), Ψ y := by

  have l1 : ContinuousOn rexp (Ici (-Real.log x)) := by fun_prop
  have l2 : Tendsto rexp atTop atTop := Real.tendsto_exp_atTop
  have l3 t (_ : t ∈ Ioi (-log x)) : HasDerivWithinAt rexp (rexp t) (Ioi t) t :=
    (Real.hasDerivAt_exp t).hasDerivWithinAt
  have l4 : ContinuousOn Ψ (rexp '' Ioi (-Real.log x)) := by fun_prop
  have l5 : IntegrableOn Ψ (rexp '' Ici (-Real.log x)) volume :=
    (l0.integrable_of_hasCompactSupport hsupp).integrableOn
  have l6 : IntegrableOn (fun x ↦ rexp x • (Ψ ∘ rexp) x) (Ici (-Real.log x)) volume := by
    refine (Continuous.integrable_of_hasCompactSupport (by continuity) ?_).integrableOn
    change HasCompactSupport (rexp • (Ψ ∘ rexp))
    exact (comp_exp_support hsupp hplus).smul_left
  have := MeasureTheory.integral_comp_smul_deriv_Ioi l1 l2 l3 l4 l5 l6
  simpa [Real.exp_neg, Real.exp_log hx] using this

theorem wiener_ikehara_smooth_sub (h1 : Integrable Ψ) (hplus : closure (Function.support Ψ) ⊆ Ioi 0) :
    Tendsto (fun x ↦ (↑A * ∫ (y : ℝ) in Ioi x⁻¹, Ψ y) - ↑A * ∫ (y : ℝ) in Ioi 0, Ψ y) atTop (𝓝 0) := by

  obtain ⟨ε, hε, hh⟩ := Metric.eventually_nhds_iff.mp <| comp_exp_support0 hplus
  apply tendsto_nhds_of_eventually_eq ; filter_upwards [eventually_gt_atTop ε⁻¹] with x hxε

  have l1 : Integrable (indicator (Ioi x⁻¹) (fun x : ℝ => Ψ x)) := h1.indicator measurableSet_Ioi
  have l2 : Integrable (indicator (Ioi 0) (fun x : ℝ => Ψ x)) := h1.indicator measurableSet_Ioi

  simp_rw [← MeasureTheory.integral_indicator measurableSet_Ioi, ← mul_sub, ← integral_sub l1 l2]
  simp ; right ; apply MeasureTheory.integral_eq_zero_of_ae ; apply Eventually.of_forall ; intro t ; simp

  have hε' : 0 < ε⁻¹ := by positivity
  have hx : 0 < x := by linarith
  have hx' : 0 < x⁻¹ := by positivity
  have hεx : x⁻¹ < ε := by apply (inv_lt_comm₀ hε hx).mp hxε

  have l3 : Ioi 0 = Ioc 0 x⁻¹ ∪ Ioi x⁻¹ := by
    ext t ; simp ; constructor <;> intro h
    · simp [h, le_or_gt]
    · cases h <;> linarith
  have l4 : Disjoint (Ioc 0 x⁻¹) (Ioi x⁻¹) := by simp
  have l5 := Set.indicator_union_of_disjoint l4 Ψ
  rw [l3, l5] ; ring_nf
  by_cases ht : t ∈ Ioc 0 x⁻¹ <;> simp [ht]
  apply hh ; simp at ht ⊢
  have : |t| ≤ x⁻¹ := by rw [abs_le] ; constructor <;> linarith
  linarith

/-%%
\begin{corollary}[Smoothed Wiener-Ikehara]\label{WienerIkeharaSmooth}\lean{wiener_ikehara_smooth}\leanok
  If $\Psi: (0,\infty) \to \C$ is smooth and compactly supported away from the origin, then,
$$ \sum_{n=1}^\infty f(n) \Psi( \frac{n}{x} ) = A x \int_0^\infty \Psi(y)\ dy + o(x)$$
as $x \to \infty$.
\end{corollary}
%%-/

lemma wiener_ikehara_smooth (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ')) (hcheby : cheby f)
    (hG: ContinuousOn G {s | 1 ≤ s.re}) (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re})
    (hsmooth: ContDiff ℝ ∞ Ψ) (hsupp: HasCompactSupport Ψ) (hplus: closure (Function.support Ψ) ⊆ Set.Ioi 0) :
    Tendsto (fun x : ℝ ↦ (∑' n, f n * Ψ (n / x)) / x - A * ∫ y in Set.Ioi 0, Ψ y) atTop (nhds 0) := by

  let h (x : ℝ) : ℂ := rexp (2 * π * x) * Ψ (exp (2 * π * x))
  have h1 : ContDiff ℝ ∞ h := by
    have : ContDiff ℝ ∞ (fun x : ℝ => (rexp (2 * π * x))) := (contDiff_const.mul contDiff_id).exp
    exact (contDiff_ofReal.comp this).mul (hsmooth.comp this)
  have h2 : HasCompactSupport h := by
    have : 2 * π ≠ 0 := by simp [pi_ne_zero]
    show HasCompactSupport ((fun x : ℝ => ((rexp (2 * π * x) : ℝ) : ℂ)) *
      (fun x : ℝ => Ψ (rexp (2 * π * x))))
    apply HasCompactSupport.mul_left
    have h3 := (comp_exp_support hsupp hplus).comp_smul this
    simpa [Function.comp_def, smul_eq_mul] using h3
  obtain ⟨g, hg⟩ := fourier_surjection_on_schwartz (toSchwartz h h1 h2)

  have e2 : ∀ u : ℝ, 2 * π * (u / (2 * π)) = u := fun u => by
    have : π ≠ 0 := pi_ne_zero
    field_simp
  have l1 {y} (hy : 0 < y) : y * Ψ y = 𝓕 g (1 / (2 * π) * Real.log y) := by
    rw [hg, toSchwartz_apply']
    simp only [h]
    rw [show 2 * π * (1 / (2 * π) * Real.log y) = Real.log y by field_simp,
      Real.exp_log hy]

  have key := limiting_cor_schwartz g hf hcheby hG hG'

  have l2 : ∀ᶠ x in atTop, ∑' (n : ℕ), f n / ↑n * 𝓕 (⇑g) (1 / (2 * π) * Real.log (↑n / x)) =
      ∑' (n : ℕ), f n * Ψ (↑n / x) / x := by
    filter_upwards [eventually_gt_atTop 0] with x hx
    congr ; ext n
    by_cases hn : n = 0 ; simp [hn, (comp_exp_support0 hplus).self_of_nhds]
    rw [← l1 (by positivity)]
    have : (n : ℂ) ≠ 0 := by simpa using hn
    have : (x : ℂ) ≠ 0 := by simpa using hx.ne.symm
    field_simp
    push_cast
    field_simp_ring

  have l3 : ∀ᶠ x in atTop, ↑A * ∫ (u : ℝ) in Ici (-Real.log x), 𝓕 (⇑g) (u / (2 * π)) =
      ↑A * ∫ (y : ℝ) in Ioi x⁻¹, Ψ y := by
    filter_upwards [eventually_gt_atTop 0] with x hx
    congr 1
    simp only [hg, toSchwartz_apply', h, e2]
    rw [MeasureTheory.integral_Ici_eq_integral_Ioi, ← one_div]
    exact wiener_ikehara_smooth_aux hsmooth.continuous hsupp hplus x hx

  have l4 : Tendsto (fun x => (↑A * ∫ (y : ℝ) in Ioi x⁻¹, Ψ y) - ↑A * ∫ (y : ℝ) in Ioi 0, Ψ y) atTop (𝓝 0) := by
    exact wiener_ikehara_smooth_sub (hsmooth.continuous.integrable_of_hasCompactSupport hsupp) hplus

  simpa [tsum_div_const] using (key.congr' <| EventuallyEq.sub l2 l3) |>.add l4

/-%%
\begin{proof}
\uses{bij,schwarz-id}\leanok
 By Lemma \ref{bij}, we can write
$$ y \Psi(y) = \hat \psi( \frac{1}{2\pi} \log y )$$
for all $y>0$ and some Schwartz function $\psi$.  Making this substitution, the claim is then equivalent after standard manipulations to
$$ \sum_{n=1}^\infty \frac{f(n)}{n} \hat \psi( \frac{1}{2\pi} \log \frac{n}{x} ) = A \int_{-\infty}^\infty \hat \psi(\frac{u}{2\pi})\ du + o(1)$$
and the claim follows from Lemma \ref{schwarz-id}.
\end{proof}
%%-/

lemma wiener_ikehara_smooth' (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ')) (hcheby : cheby f)
    (hG: ContinuousOn G {s | 1 ≤ s.re}) (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re})
    (hsmooth: ContDiff ℝ ∞ Ψ) (hsupp: HasCompactSupport Ψ) (hplus: closure (Function.support Ψ) ⊆ Set.Ioi 0) :
    Tendsto (fun x : ℝ ↦ (∑' n, f n * Ψ (n / x)) / x) atTop (nhds (A * ∫ y in Set.Ioi 0, Ψ y)) :=
  tendsto_sub_nhds_zero_iff.mp <| wiener_ikehara_smooth hf hcheby hG hG' hsmooth hsupp hplus

local instance {E : Type*} : Coe (E → ℝ) (E → ℂ) := ⟨fun f n => f n⟩

@[norm_cast]
theorem set_integral_ofReal {f : ℝ → ℝ} {s : Set ℝ} : ∫ x in s, (f x : ℂ) = ∫ x in s, f x :=
  integral_ofReal

lemma wiener_ikehara_smooth_real {f : ℕ → ℝ} {Ψ : ℝ → ℝ} (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hcheby : cheby f) (hG: ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re})
    (hsmooth: ContDiff ℝ ∞ Ψ) (hsupp: HasCompactSupport Ψ) (hplus: closure (Function.support Ψ) ⊆ Set.Ioi 0) :
    Tendsto (fun x : ℝ ↦ (∑' n, f n * Ψ (n / x)) / x) atTop (nhds (A * ∫ y in Set.Ioi 0, Ψ y)) := by

  let Ψ' := ofReal ∘ Ψ
  have l1 : ContDiff ℝ ∞ Ψ' := contDiff_ofReal.comp hsmooth
  have l2 : HasCompactSupport Ψ' := hsupp.comp_left rfl
  have l3 : closure (Function.support Ψ') ⊆ Ioi 0 := by rwa [Function.support_comp_eq] ; simp
  have key := (continuous_re.tendsto _).comp (@wiener_ikehara_smooth' A Ψ G f hf hcheby hG hG' l1 l2 l3)
  simp at key ; norm_cast at key


end Zeta7PNT

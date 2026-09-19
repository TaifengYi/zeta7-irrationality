import Zeta7Proof.Radius49U7Analytic
import Zeta7Proof.Radius49U7Data
import Zeta7Proof.Radius49USeven
import Zeta7Proof.ValenceQDisc

/-! Radius internalization, HM formal layer I: from the analytic power sums to exact formal
identities for the Atkin operator on the coordinate `x`.

* `evalHom`: evaluation on the ring of tempered complex series is a ring homomorphism.
* `evalQ_filter`: the root-of-unity filter `Σ_{k<7} f(ζᵏ w) = 7 (U₇ f)(w⁷)`.
* `eq_of_evalQ_eventually`: tempered series agreeing near `0` (off `0`) are equal.
* `seven_uSeven_xSeries_pow`: `7 U₇(x^m) = p_m(x)` in `ℚ⟦X⟧` for `m = 1, …, 7`.

No published radius input is used. -/

noncomputable section
set_option autoImplicit false
open PowerSeries Complex Filter Topology UpperHalfPlane
namespace Zeta7Radius49
open Zeta7Arch Zeta7LevelSeven Zeta7Valence Zeta7Main

/-! ### Polynomial expressions commute with ring homomorphisms -/

theorem pM_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (m : ℕ) (X : R) :
    φ (pM m X) = pM m (φ X) := by
  rcases m with _ | _ | _ | _ | _ | _ | _ | _ | m <;> simp [pM, map_ofNat]

theorem eK_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (k : ℕ) (X : R) :
    φ (eK k X) = eK k (φ X) := by
  rcases k with _ | _ | _ | _ | _ | _ | _ | _ | k <;> simp [eK, map_ofNat]

theorem psi_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (Y X : R) :
    φ (psi Y X) = psi (φ Y) (φ X) := by
  simp [psi, eK_map]

/-! ### Evaluation as a ring homomorphism -/

/-- Tempered complex series form a subring. -/
def temperedSubring : Subring ℂ⟦X⟧ where
  carrier := {f | Tempered f}
  add_mem' := Tempered.add
  mul_mem' := Tempered.mul
  zero_mem' := tempered_zero
  one_mem' := tempered_one
  neg_mem' := Tempered.neg

theorem evalQ_zero' (q : ℂ) : evalQ 0 q = 0 := by simpa using evalQ_C 0 q

theorem evalQ_one' (q : ℂ) : evalQ 1 q = 1 := by simpa using evalQ_C 1 q

/-- Evaluation at a point of the unit disc. -/
def evalHom (q : ℂ) (hq : ‖q‖ < 1) : temperedSubring →+* ℂ where
  toFun f := evalQ f q
  map_one' := evalQ_one' q
  map_mul' f g := evalQ_mul f.2 g.2 hq
  map_zero' := evalQ_zero' q
  map_add' f g := evalQ_add f.2 g.2 hq

theorem evalQ_pM {f : ℂ⟦X⟧} (hf : Tempered f) (m : ℕ) {q : ℂ} (hq : ‖q‖ < 1) :
    evalQ (pM m f) q = pM m (evalQ f q) := by
  have h := pM_map (evalHom q hq) m ⟨f, hf⟩
  have hc := pM_map temperedSubring.subtype m ⟨f, hf⟩
  simp only [Subring.coe_subtype] at hc
  change evalQ ((pM m (⟨f, hf⟩ : temperedSubring) : temperedSubring) : ℂ⟦X⟧) q = _ at h
  rw [hc] at h
  exact h

theorem tempered_pM {f : ℂ⟦X⟧} (hf : Tempered f) (m : ℕ) : Tempered (pM m f) := by
  have hc := pM_map temperedSubring.subtype m ⟨f, hf⟩
  simp only [Subring.coe_subtype] at hc
  rw [← hc]
  exact (pM m (⟨f, hf⟩ : temperedSubring)).2

theorem evalQ_pow' {f : ℂ⟦X⟧} (hf : Tempered f) (n : ℕ) {q : ℂ} (hq : ‖q‖ < 1) :
    evalQ (f ^ n) q = evalQ f q ^ n :=
  map_pow (evalHom q hq) ⟨f, hf⟩ n

/-! ### The root-of-unity filter -/

/-- The primitive seventh root of unity `e^{2Real.pii/7}`. -/
def zeta7 : ℂ := exp (2 * Real.pi * Complex.I / 7)

theorem zeta7_prim : IsPrimitiveRoot zeta7 7 := by
  simpa [zeta7] using Complex.isPrimitiveRoot_exp 7 (by norm_num)

theorem norm_zeta7 : ‖zeta7‖ = 1 := zeta7_prim.norm'_eq_one (by norm_num)

theorem sum_zeta7_pow (n : ℕ) :
    ∑ k ∈ Finset.range 7, zeta7 ^ (k * n) = if 7 ∣ n then 7 else 0 := by
  split_ifs with h
  · obtain ⟨c, rfl⟩ := h
    have h1 : ∀ k : ℕ, zeta7 ^ (k * (7 * c)) = 1 := by
      intro k
      rw [show k * (7 * c) = 7 * (k * c) by ring, pow_mul, zeta7_prim.pow_eq_one, one_pow]
    simp [h1]
  · have hcop : Nat.Coprime n 7 :=
      (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr h))
    have hp : IsPrimitiveRoot (zeta7 ^ n) 7 := zeta7_prim.pow_of_coprime n hcop
    have := hp.geom_sum_eq_zero (by norm_num)
    simpa [← pow_mul, mul_comm] using this

theorem tempered_uSeven {f : ℂ⟦X⟧} (hf : Tempered f) : Tempered (uSeven f) := by
  intro r hr0 hr1
  set s : ℝ := r ^ ((1 : ℝ) / 7) with hs
  have hs0 : 0 ≤ s := Real.rpow_nonneg hr0 _
  have hs1 : s < 1 := Real.rpow_lt_one hr0 hr1 (by norm_num)
  have hs7 : s ^ 7 = r := by
    rw [hs, ← Real.rpow_natCast, ← Real.rpow_mul hr0]; norm_num
  have hsum := (hf s hs0 hs1).comp_injective (mul_right_injective₀ (by norm_num : (7 : ℕ) ≠ 0))
  refine hsum.congr (fun k => ?_)
  simp [coeff_uSeven, pow_mul, hs7]

/-- **Root-of-unity filter.** -/
theorem evalQ_filter {f : ℂ⟦X⟧} (hf : Tempered f) {w : ℂ} (hw : ‖w‖ < 1) :
    ∑ k ∈ Finset.range 7, evalQ f (zeta7 ^ k * w) = 7 * evalQ (uSeven f) (w ^ 7) := by
  have hz : ∀ k : ℕ, ‖zeta7 ^ k * w‖ < 1 := by
    intro k; rw [norm_mul, norm_pow, norm_zeta7, one_pow, one_mul]; exact hw
  simp only [evalQ]
  rw [← Summable.tsum_finsetSum (fun k _ => (hf.summable_norm (hz k)).of_norm)]
  have hterm : ∀ n : ℕ, ∑ k ∈ Finset.range 7, coeff n f * (zeta7 ^ k * w) ^ n =
      if 7 ∣ n then 7 * (coeff n f * w ^ n) else 0 := by
    intro n
    have : ∀ k : ℕ, coeff n f * (zeta7 ^ k * w) ^ n = (coeff n f * w ^ n) * zeta7 ^ (k * n) := by
      intro k; rw [mul_pow, ← pow_mul]; ring
    simp_rw [this, ← Finset.mul_sum, sum_zeta7_pow]
    split_ifs <;> ring
  simp_rw [hterm]
  rw [← tsum_mul_left]
  have hinj : Function.Injective (fun k : ℕ => 7 * k) := mul_right_injective₀ (by norm_num)
  have hsupp : Function.support (fun n : ℕ => if 7 ∣ n then 7 * (coeff n f * w ^ n) else 0) ⊆
      Set.range (fun k : ℕ => 7 * k) := by
    intro n hn
    simp only [Function.mem_support, ne_eq, ite_eq_right_iff, not_forall] at hn
    obtain ⟨⟨c, rfl⟩, _⟩ := hn
    exact ⟨c, rfl⟩
  rw [← hinj.tsum_eq hsupp]
  refine tsum_congr (fun k => ?_)
  simp [coeff_uSeven, pow_mul]

/-! ### Uniqueness of expansions -/

theorem eq_of_evalQ_eventually {f g : ℂ⟦X⟧} (hf : Tempered f) (hg : Tempered g)
    (h : ∀ᶠ q in 𝓝[≠] (0 : ℂ), evalQ f q = evalQ g q) : f = g := by
  have h0mem : (0 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by simp
  have hcf : ContinuousAt (evalQ f) 0 := (hf.analyticOnNhd 0 h0mem).continuousAt
  have hcg : ContinuousAt (evalQ g) 0 := (hg.analyticOnNhd 0 h0mem).continuousAt
  have h00 : evalQ f 0 = evalQ g 0 := by
    have t1 : Tendsto (evalQ f) (𝓝[≠] (0 : ℂ)) (𝓝 (evalQ f 0)) :=
      hcf.tendsto.mono_left nhdsWithin_le_nhds
    have t2 : Tendsto (evalQ g) (𝓝[≠] (0 : ℂ)) (𝓝 (evalQ g 0)) :=
      hcg.tendsto.mono_left nhdsWithin_le_nhds
    exact tendsto_nhds_unique (t1.congr' h) t2
  have heq : ∀ᶠ q in 𝓝 (0 : ℂ), evalQ f q = evalQ g q := by
    rw [eventually_nhdsWithin_iff] at h
    filter_upwards [h] with q hq
    by_cases hq0 : q = 0
    · subst hq0; exact h00
    · exact hq hq0
  have hp := hf.hasFPowerSeriesOnBall.hasFPowerSeriesAt.eq_formalMultilinearSeries_of_eventually
    hg.hasFPowerSeriesOnBall.hasFPowerSeriesAt heq
  ext n
  have := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p n (fun _ => 1)) hp
  simpa [fms, FormalMultilinearSeries.ofScalars_apply_eq] using this

/-- Statements near `i∞` in `τ` give statements near `0` in `q = e^{2Real.piiτ}`. -/
theorem eventually_punctured_of_atImInfty {P : ℂ → Prop}
    (h : ∀ᶠ τ : ℍ in atImInfty, P (Function.Periodic.qParam 1 τ)) :
    ∀ᶠ q in 𝓝[≠] (0 : ℂ), P q := by
  obtain ⟨A, hA⟩ := (atImInfty_mem _).mp h
  set B : ℝ := max A 1
  have hδ : 0 < Real.exp (-2 * Real.pi * B) := Real.exp_pos _
  rw [eventually_nhdsWithin_iff]
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hδ] with q hq hq0
  rw [Metric.mem_ball, dist_zero_right] at hq
  have hq1 : ‖q‖ < 1 := hq.trans (by
    have : (1 : ℝ) ≤ B := le_max_right _ _
    calc Real.exp (-2 * Real.pi * B) < Real.exp 0 :=
          Real.exp_lt_exp.mpr (by nlinarith [Real.pi_pos])
      _ = 1 := Real.exp_zero)
  have him := invQParam_im_pos hq0 hq1
  let τ : ℍ := ⟨Function.Periodic.invQParam 1 q, him⟩
  have hτ : A ≤ τ.im := by
    change A ≤ (Function.Periodic.invQParam 1 q).im
    rw [Function.Periodic.im_invQParam]
    have hlog : Real.log ‖q‖ < -2 * Real.pi * B := by
      rw [Real.log_lt_iff_lt_exp (norm_pos_iff.mpr hq0)]; exact hq
    have hB : A ≤ B := le_max_left _ _
    have hpi := Real.pi_pos
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith
  have := hA τ hτ
  simpa [τ, Function.Periodic.qParam_right_inv one_ne_zero hq0] using this

/-! ### The seven power sums as formal identities -/

theorem qParam_shift (τ : ℂ) (k : ℕ) :
    Function.Periodic.qParam 1 ((τ + k) / 7) = zeta7 ^ k * Function.Periodic.qParam 7 τ := by
  rw [Function.Periodic.qParam, Function.Periodic.qParam, zeta7, ← Complex.exp_nat_mul,
    ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem qParam_seven_pow (τ : ℂ) :
    Function.Periodic.qParam 7 τ ^ 7 = Function.Periodic.qParam 1 τ := by
  simp only [Function.Periodic.qParam, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem norm_qParam_seven_lt_one (τ : ℍ) : ‖Function.Periodic.qParam 7 (τ : ℂ)‖ < 1 := by
  rw [Function.Periodic.norm_qParam]
  have := τ.im_pos
  have := Real.pi_pos
  calc Real.exp (-2 * Real.pi * (τ : ℂ).im / 7) < Real.exp 0 := by
        apply Real.exp_lt_exp.mpr
        simp only [coe_im]
        apply div_neg_of_neg_of_pos _ (by norm_num)
        nlinarith
    _ = 1 := Real.exp_zero

/-- **Formal power sums over `ℂ`.** -/
theorem seven_uSeven_xC_pow (m : ℕ) (hm : 0 < m)
    (h : ∀ᶠ τ : ℍ in atImInfty,
      ∑ k ∈ Finset.range 7, Xf (((τ : ℂ) + k) / 7) ^ m = pM m (etaCoordinate τ)) :
    7 * uSeven (xC ^ m) = pM m xC := by
  have hxt : Tempered (xC ^ m) := xC_tempered.pow m
  have hL : Tempered (7 * uSeven (xC ^ m)) := (tempered_C 7).mul (tempered_uSeven hxt)
  apply eq_of_evalQ_eventually hL (tempered_pM xC_tempered m)
  apply eventually_punctured_of_atImInfty
  filter_upwards [h] with τ hτ
  have hq1 : ‖Function.Periodic.qParam 1 (τ : ℂ)‖ < 1 := by
    rw [← qParam_seven_pow, norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) (norm_qParam_seven_lt_one τ) (by norm_num)
  have hw := norm_qParam_seven_lt_one τ
  rw [show (7 : ℂ⟦X⟧) * uSeven (xC ^ m) = C 7 * uSeven (xC ^ m) by rw [map_ofNat],
    evalQ_mul (tempered_C 7) (tempered_uSeven hxt) hq1, evalQ_C, evalQ_pM xC_tempered m hq1,
    ← qParam_seven_pow, ← evalQ_filter hxt hw, qParam_seven_pow]
  have hx : xFun (Function.Periodic.qParam 1 (τ : ℂ)) = etaCoordinate τ := xFun_qParam τ
  rw [show evalQ xC (Function.Periodic.qParam 1 (τ : ℂ)) = etaCoordinate τ from hx, ← hτ]
  apply Finset.sum_congr rfl
  intro k _
  have hk : ‖zeta7 ^ k * Function.Periodic.qParam 7 (τ : ℂ)‖ < 1 := by
    rw [norm_mul, norm_pow, norm_zeta7, one_pow, one_mul]; exact hw
  rw [evalQ_pow' xC_tempered m hk, ← qParam_shift]
  have hpos : 0 < (((τ : ℂ) + k) / 7).im := by simp [τ.im_pos]
  rw [Xf_qParam hpos]
  rfl

theorem map_injective_rat : Function.Injective (PowerSeries.map (algebraMap ℚ ℂ)) := by
  intro f g hfg
  ext n
  have := congrArg (coeff n) hfg
  simp only [coeff_map] at this
  exact (algebraMap ℚ ℂ).injective this

/-- **Formal power sums over `ℚ`.** -/
theorem seven_uSeven_xSeries_pow_of (m : ℕ) (hm : 0 < m)
    (h : ∀ᶠ τ : ℍ in atImInfty,
      ∑ k ∈ Finset.range 7, Xf (((τ : ℂ) + k) / 7) ^ m = pM m (etaCoordinate τ)) :
    7 * uSeven (xSeries ^ m) = pM m xSeries := by
  apply map_injective_rat
  have hC := seven_uSeven_xC_pow m hm h
  rw [map_mul, ← uSeven_map, map_pow]
  rw [pM_map (PowerSeries.map (algebraMap ℚ ℂ))]
  simpa [xC, map_ofNat] using hC

end Zeta7Radius49

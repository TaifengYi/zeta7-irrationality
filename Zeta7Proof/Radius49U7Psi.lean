import Zeta7Proof.Radius49U7PowerSums
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.RingTheory.Polynomial.Vieta

/-! Radius internalization, HM: the `X₀(49)` correspondence `Ψ(x(q), x(q⁷)) = 0` and the
global recurrence for the weight-zero `U₇` columns.

* `esymm_eq_eK`: seven numbers whose first seven power sums are `p_m(X)` have elementary
  symmetric functions `e_k(X)` (Newton's identities).
* `psi_eventually`: `Ψ(x(τ/7), x(τ)) = 0` near `i∞` (Vieta).
* `vSeven f = f(X⁷)`, `uSeven_vSeven_mul : U₇(V f · g) = f · U₇ g`.
* `psi_xSeries_vSeven : Ψ(x, V x) = 0` in `ℚ⟦X⟧` (the modular equation, proved).
* `uSeven_x_pow_recurrence`: `U₇(x^{m+7}) = Σ_k (-1)^{k-1} e_k(x) U₇(x^{m+7-k})`.

No published radius input is used. -/

noncomputable section
set_option autoImplicit false
open PowerSeries Filter Topology UpperHalfPlane
namespace Zeta7Radius49
open Zeta7Arch Zeta7LevelSeven Zeta7Valence Zeta7Main

/-! ### Newton and Vieta for seven numbers -/

theorem newton_eval (y : Fin 7 → ℂ) (k : ℕ) :
    (k : ℂ) * (Finset.univ.val.map y).esymm k = (-1) ^ (k + 1) *
      ∑ i ∈ Finset.range k, (-1) ^ i * (Finset.univ.val.map y).esymm i *
        ∑ j, y j ^ (k - i) := by
  have h := congrArg (MvPolynomial.aeval y) (MvPolynomial.mul_esymm_eq_sum (Fin 7) ℂ k)
  simp only [map_mul, map_pow, map_neg, map_one, map_sum, map_natCast,
    MvPolynomial.aeval_esymm_eq_multiset_esymm, MvPolynomial.psum, MvPolynomial.aeval_X] at h
  rw [h, Finset.sum_filter, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ]
  simp only [lt_self_iff_false, if_false, add_zero]
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  rw [if_pos (Finset.mem_range.mp hx)]

theorem esymm_zero_map (y : Fin 7 → ℂ) : (Finset.univ.val.map y).esymm 0 = 1 := by
  simp [Multiset.esymm]

/-- **Newton.** -/
theorem esymm_eq_eK (y : Fin 7 → ℂ) (X : ℂ)
    (hp : ∀ m, 1 ≤ m → m ≤ 7 → ∑ j, y j ^ m = pM m X) :
    ∀ k, 1 ≤ k → k ≤ 7 → (Finset.univ.val.map y).esymm k = eK k X := by
  set E := fun k => (Finset.univ.val.map y).esymm k with hE
  have E0 : E 0 = 1 := esymm_zero_map y
  have P : ∀ m, 1 ≤ m → m ≤ 7 → ∑ j, y j ^ m = pM m X := hp
  have step : ∀ k : ℕ, 1 ≤ k → k ≤ 7 → (k : ℂ) * E k = (-1) ^ (k + 1) *
      ∑ i ∈ Finset.range k, (-1) ^ i * E i * pM (k - i) X := by
    intro k hk1 hk7
    rw [show E k = (Finset.univ.val.map y).esymm k from rfl, newton_eval]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [P (k - i) (by have := Finset.mem_range.mp hi; omega) (by omega)]
  have e1 : E 1 = eK 1 X := by
    have h := step 1 le_rfl (by norm_num)
    have hn := newton_1 X
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, E0] at h
    norm_num at h hn
    linear_combination h - hn
  have e2 : E 2 = eK 2 X := by
    have h := step 2 (by norm_num) (by norm_num)
    have hn := newton_2 X
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, E0, e1] at h
    norm_num at h
    apply mul_left_cancel₀ (show (2 : ℂ) ≠ 0 by norm_num)
    linear_combination h - hn
  have e3 : E 3 = eK 3 X := by
    have h := step 3 (by norm_num) (by norm_num)
    have hn := newton_3 X
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, E0, e1, e2] at h
    norm_num at h
    apply mul_left_cancel₀ (show (3 : ℂ) ≠ 0 by norm_num)
    linear_combination h - hn
  have e4 : E 4 = eK 4 X := by
    have h := step 4 (by norm_num) (by norm_num)
    have hn := newton_4 X
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, E0, e1, e2, e3] at h
    norm_num at h
    apply mul_left_cancel₀ (show (4 : ℂ) ≠ 0 by norm_num)
    linear_combination h - hn
  have e5 : E 5 = eK 5 X := by
    have h := step 5 (by norm_num) (by norm_num)
    have hn := newton_5 X
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, E0, e1, e2, e3, e4] at h
    norm_num at h
    apply mul_left_cancel₀ (show (5 : ℂ) ≠ 0 by norm_num)
    linear_combination h - hn
  have e6 : E 6 = eK 6 X := by
    have h := step 6 (by norm_num) (by norm_num)
    have hn := newton_6 X
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, E0, e1, e2, e3, e4, e5] at h
    norm_num at h
    apply mul_left_cancel₀ (show (6 : ℂ) ≠ 0 by norm_num)
    linear_combination h - hn
  have e7 : E 7 = eK 7 X := by
    have h := step 7 (by norm_num) (by norm_num)
    have hn := newton_7 X
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, E0, e1, e2, e3, e4, e5, e6] at h
    norm_num at h
    apply mul_left_cancel₀ (show (7 : ℂ) ≠ 0 by norm_num)
    linear_combination h - hn
  intro k hk1 hk7
  interval_cases k
  exacts [e1, e2, e3, e4, e5, e6, e7]

/-- **Vieta.** A root of the product is a root of `Ψ`. -/
theorem psi_root (y : Fin 7 → ℂ) (X : ℂ)
    (hp : ∀ m, 1 ≤ m → m ≤ 7 → ∑ j, y j ^ m = pM m X) : psi (y 0) X = 0 := by
  have hE := esymm_eq_eK y X hp
  have hv := Multiset.prod_X_sub_X_eq_sum_esymm (Finset.univ.val.map y)
  have hcard : Multiset.card (Finset.univ.val.map y) = 7 := by simp
  have hev := congrArg (Polynomial.eval (y 0)) hv
  rw [Polynomial.eval_multiset_prod, hcard] at hev
  have hzero : (Multiset.map (Polynomial.eval (y 0))
      (Multiset.map (fun t => Polynomial.X - Polynomial.C t) (Finset.univ.val.map y))).prod = 0 := by
    apply Multiset.prod_eq_zero
    rw [Multiset.map_map, Multiset.map_map]
    exact Multiset.mem_map.mpr ⟨0, Finset.mem_univ_val _, by simp⟩
  rw [hzero] at hev
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_neg, Polynomial.eval_one, esymm_zero_map,
    hE 1 (by norm_num) (by norm_num), hE 2 (by norm_num) (by norm_num),
    hE 3 (by norm_num) (by norm_num), hE 4 (by norm_num) (by norm_num),
    hE 5 (by norm_num) (by norm_num), hE 6 (by norm_num) (by norm_num),
    hE 7 (by norm_num) (by norm_num)] at hev
  rw [psi]
  norm_num at hev
  linear_combination -hev

/-- **The correspondence, analytically.** `Ψ(x(τ/7), x(τ)) = 0` near `i∞`. -/
theorem psi_eventually : ∀ᶠ τ : ℍ in atImInfty,
    psi (Xf ((τ : ℂ) / 7)) (etaCoordinate τ) = 0 := by
  filter_upwards [powerSum_1, powerSum_2, powerSum_3, powerSum_4, powerSum_5, powerSum_6,
    powerSum_7] with τ h1 h2 h3 h4 h5 h6 h7
  have hp : ∀ m, 1 ≤ m → m ≤ 7 →
      ∑ j : Fin 7, Xf (((τ : ℂ) + ((j : ℕ) : ℂ)) / 7) ^ m = pM m (etaCoordinate τ) := by
    intro m hm1 hm7
    rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => Xf (((τ : ℂ) + (k : ℂ)) / 7) ^ m)]
    interval_cases m
    exacts [h1, h2, h3, h4, h5, h6, h7]
  have := psi_root (fun j : Fin 7 => Xf (((τ : ℂ) + ((j : ℕ) : ℂ)) / 7)) (etaCoordinate τ) hp
  simpa using this

/-! ### The Frobenius `V` and the formal correspondence -/

theorem hasSubst_X_pow_seven {R : Type*} [CommRing R] : HasSubst (X ^ 7 : R⟦X⟧) :=
  HasSubst.X_pow (by norm_num)

/-- `V f = f(X⁷)`, as a ring homomorphism. -/
def vSevenHom (R : Type*) [CommRing R] : R⟦X⟧ →ₐ[R] R⟦X⟧ :=
  substAlgHom (R := R) (hasSubst_X_pow_seven (R := R))

def vSeven {R : Type*} [CommRing R] (f : R⟦X⟧) : R⟦X⟧ := vSevenHom R f

theorem coeff_vSeven {R : Type*} [CommRing R] (f : R⟦X⟧) (n : ℕ) :
    coeff n (vSeven f) = if 7 ∣ n then coeff (n / 7) f else 0 := by
  rw [vSeven, vSevenHom, coe_substAlgHom, coeff_subst_X_pow (by norm_num)]
  simp

theorem vSeven_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (f : R⟦X⟧) :
    (vSeven f).map φ = vSeven (f.map φ) := by
  ext n
  rw [coeff_map, coeff_vSeven, coeff_vSeven]
  split_ifs <;> simp only [coeff_map, map_zero]

/-- `U₇(V f · g) = f · U₇ g`. -/
theorem uSeven_vSeven_mul {R : Type*} [CommRing R] (f g : R⟦X⟧) :
    uSeven (vSeven f * g) = f * uSeven g := by
  ext n
  rw [coeff_uSeven, coeff_mul, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [coeff_vSeven, coeff_uSeven, ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  have himage : (Finset.range (7 * n + 1)).filter (fun a => 7 ∣ a) =
      (Finset.range (n + 1)).image (fun i => 7 * i) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨ha, ⟨c, rfl⟩⟩
      exact ⟨c, by omega, rfl⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨by omega, ⟨c, rfl⟩⟩
  rw [himage, Finset.sum_image (fun a _ b _ h => by omega)]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [Nat.mul_div_cancel_left i (by norm_num), show 7 * n - 7 * i = 7 * (n - i) by omega]

theorem tempered_vSeven {f : ℂ⟦X⟧} (hf : Tempered f) : Tempered (vSeven f) := by
  intro r hr0 hr1
  have hr7 : r ^ 7 < 1 := pow_lt_one₀ hr0 hr1 (by norm_num)
  have hs := hf (r ^ 7) (by positivity) hr7
  have hinj : Function.Injective (fun k : ℕ => 7 * k) := mul_right_injective₀ (by norm_num)
  have hsupp : Function.support (fun n => ‖coeff n (vSeven f)‖ * r ^ n) ⊆
      Set.range (fun k : ℕ => 7 * k) := by
    intro n hn
    simp only [Function.mem_support, coeff_vSeven] at hn
    by_contra hc
    apply hn
    rw [if_neg (fun ⟨c, hc'⟩ => hc ⟨c, hc'.symm⟩)]
    simp
  rw [← hinj.summable_iff (fun n hn => Function.notMem_support.mp (fun h => hn (hsupp h)))]
  refine hs.congr (fun k => ?_)
  simp [coeff_vSeven, pow_mul]

theorem evalQ_vSeven {f : ℂ⟦X⟧} (hf : Tempered f) (q : ℂ) :
    evalQ (vSeven f) q = evalQ f (q ^ 7) := by
  have hinj : Function.Injective (fun k : ℕ => 7 * k) := mul_right_injective₀ (by norm_num)
  have hsupp : Function.support (fun n => coeff n (vSeven f) * q ^ n) ⊆
      Set.range (fun k : ℕ => 7 * k) := by
    intro n hn
    simp only [Function.mem_support, coeff_vSeven] at hn
    by_contra hc
    apply hn
    rw [if_neg (fun ⟨c, hc'⟩ => hc ⟨c, hc'.symm⟩)]
    simp
  rw [evalQ, evalQ, ← hinj.tsum_eq hsupp]
  refine tsum_congr (fun k => ?_)
  simp [coeff_vSeven, pow_mul]

theorem evalQ_psi {f g : ℂ⟦X⟧} (hf : Tempered f) (hg : Tempered g) {q : ℂ} (hq : ‖q‖ < 1) :
    evalQ (psi f g) q = psi (evalQ f q) (evalQ g q) := by
  have h := psi_map (evalHom q hq) ⟨f, hf⟩ ⟨g, hg⟩
  have hc := psi_map temperedSubring.subtype ⟨f, hf⟩ ⟨g, hg⟩
  simp only [Subring.coe_subtype] at hc
  change evalQ ((psi (⟨f, hf⟩ : temperedSubring) ⟨g, hg⟩ : temperedSubring) : ℂ⟦X⟧) q = _ at h
  rw [hc] at h
  exact h

theorem tempered_psi {f g : ℂ⟦X⟧} (hf : Tempered f) (hg : Tempered g) : Tempered (psi f g) := by
  have hc := psi_map temperedSubring.subtype ⟨f, hf⟩ ⟨g, hg⟩
  simp only [Subring.coe_subtype] at hc
  rw [← hc]
  exact (psi (⟨f, hf⟩ : temperedSubring) ⟨g, hg⟩).2

/-- The map `σ ↦ 7σ` of the upper half-plane. -/
def mulSeven (σ : ℍ) : ℍ := ⟨7 * (σ : ℂ), by simp [σ.im_pos]⟩

theorem mulSeven_tendsto : Tendsto mulSeven atImInfty atImInfty := by
  rw [atImInfty, tendsto_comap_iff]
  have : (fun σ : ℍ => (mulSeven σ).im) = fun σ => 7 * σ.im := by
    funext σ
    change (7 * (σ : ℂ)).im = 7 * (σ : ℂ).im
    simp
  change Tendsto (fun σ : ℍ => (mulSeven σ).im) atImInfty atTop
  rw [this]
  exact (tendsto_comap.const_mul_atTop (by norm_num : (0 : ℝ) < 7))

/-- **The modular equation `Ψ(x, V x) = 0`.** -/
theorem psi_xSeries_vSeven : psi xSeries (vSeven xSeries) = 0 := by
  apply map_injective_rat
  rw [psi_map (PowerSeries.map (algebraMap ℚ ℂ)), vSeven_map, map_zero]
  change psi xC (vSeven xC) = 0
  have hv : Tempered (vSeven xC) := tempered_vSeven xC_tempered
  apply eq_of_evalQ_eventually (tempered_psi xC_tempered hv) tempered_zero
  apply eventually_punctured_of_atImInfty
  filter_upwards [mulSeven_tendsto.eventually psi_eventually] with σ hσ
  have hq1 : ‖Function.Periodic.qParam 1 (σ : ℂ)‖ < 1 := by
    rw [← qParam_seven_pow, norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) (norm_qParam_seven_lt_one σ) (by norm_num)
  rw [evalQ_psi xC_tempered hv hq1, evalQ_vSeven xC_tempered, evalQ_zero']
  have h1 : evalQ xC (Function.Periodic.qParam 1 (σ : ℂ)) = etaCoordinate σ := xFun_qParam σ
  have h7 : Function.Periodic.qParam 1 (σ : ℂ) ^ 7 = Function.Periodic.qParam 1 (mulSeven σ : ℂ) := by
    simp only [Function.Periodic.qParam, mulSeven, ← Complex.exp_nat_mul]
    congr 1; push_cast; ring
  have h2 : evalQ xC (Function.Periodic.qParam 1 (σ : ℂ) ^ 7) = etaCoordinate (mulSeven σ) := by
    rw [h7]; exact xFun_qParam (mulSeven σ)
  rw [h1, h2]
  have hs : Xf ((mulSeven σ : ℂ) / 7) = etaCoordinate σ := by
    rw [show ((mulSeven σ : ℂ) / 7) = (σ : ℂ) by simp [mulSeven]]
    exact Xf_eq σ
  rw [← hs]
  exact hσ

/-! ### The global recurrence -/

theorem vSeven_eK {R : Type*} [CommRing R] (k : ℕ) (f : R⟦X⟧) :
    eK k (vSeven f) = vSeven (eK k f) :=
  (eK_map (vSevenHom R).toRingHom k f).symm

/-- `x^7 = Σ_k (-1)^{k-1} e_k(V x) x^{7-k}`. -/
theorem x_pow_seven_eq :
    xSeries ^ 7 = eK 1 (vSeven xSeries) * xSeries ^ 6 - eK 2 (vSeven xSeries) * xSeries ^ 5 +
      eK 3 (vSeven xSeries) * xSeries ^ 4 - eK 4 (vSeven xSeries) * xSeries ^ 3 +
      eK 5 (vSeven xSeries) * xSeries ^ 2 - eK 6 (vSeven xSeries) * xSeries +
      eK 7 (vSeven xSeries) := by
  have h := psi_xSeries_vSeven
  rw [psi] at h
  linear_combination h

/-- **The global recurrence for the weight-zero `U₇` columns.** -/
theorem uSeven_x_pow_recurrence (m : ℕ) :
    uSeven (xSeries ^ (m + 7)) =
      eK 1 xSeries * uSeven (xSeries ^ (m + 6)) - eK 2 xSeries * uSeven (xSeries ^ (m + 5)) +
      eK 3 xSeries * uSeven (xSeries ^ (m + 4)) - eK 4 xSeries * uSeven (xSeries ^ (m + 3)) +
      eK 5 xSeries * uSeven (xSeries ^ (m + 2)) - eK 6 xSeries * uSeven (xSeries ^ (m + 1)) +
      eK 7 xSeries * uSeven (xSeries ^ m) := by
  have hx : xSeries ^ (m + 7) = xSeries ^ 7 * xSeries ^ m := by ring
  rw [hx, x_pow_seven_eq]
  simp only [vSeven_eK]
  have hl : ∀ (f g : ℚ⟦X⟧), uSeven (f - g) = uSeven f - uSeven g := by
    intro f g; ext n; simp [coeff_uSeven]
  have e : ∀ (a : ℚ⟦X⟧) (b : ℕ), vSeven a * xSeries ^ b * xSeries ^ m =
      vSeven a * xSeries ^ (m + b) := by
    intro a b; ring
  simp only [add_mul, sub_mul, e, uSeven_add, hl, uSeven_vSeven_mul]
  have e7 : vSeven (eK 7 xSeries) * xSeries ^ m = vSeven (eK 7 xSeries) * xSeries ^ (m + 0) := by
    simp
  have e6 : vSeven (eK 6 xSeries) * xSeries * xSeries ^ m =
      vSeven (eK 6 xSeries) * xSeries ^ (m + 1) := by ring
  rw [e6, uSeven_vSeven_mul]

end Zeta7Radius49

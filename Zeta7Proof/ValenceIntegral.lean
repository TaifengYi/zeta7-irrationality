import Mathlib

/-! The real integrals in the energy formula (48) and the coprime averaging.

* `integral_posPart`: for `c > 0`, `c² y t < 1` and `B ≥ √(y/t - c²y²)`,
  `∫_{-B}^{B} (y/(v² + c²y²) - t)₊ dv = (2/c)(arccos(c√(yt)) - c√(yt)√(1 - c²yt))`.
* `posPart_eq_zero`: the integrand vanishes identically when `c² y t ≥ 1`.
* `card_coprime_Ico_le`: at most `φ(c)` of any `c` consecutive integers are prime to `c`.
* `average_le`: `Σ_{d ∈ D} ∫_0^1 f(cu + d) du ≤ (φ(c)/c) ∫_{-B}^{B} f` for `f ≥ 0` continuous and a
  finite set `D` of integers prime to `c` with `[d, d + c] ⊆ [-B, B]`. -/
noncomputable section
set_option autoImplicit false
namespace Zeta7Valence
open Real MeasureTheory intervalIntegral Set

/-! ### The explicit integral -/

theorem hasDerivAt_G {c y t : ℝ} (hc : 0 < c) (hy : 0 < y) (v : ℝ) :
    HasDerivAt (fun v => c⁻¹ * arctan (v / (c * y)) - t * v)
      (y / (v ^ 2 + c ^ 2 * y ^ 2) - t) v := by
  have hcy : 0 < c * y := mul_pos hc hy
  have h1 := ((hasDerivAt_id v).div_const (c * y)).arctan.const_mul c⁻¹
  have h2 := (hasDerivAt_id v).const_mul t
  refine (h1.sub h2).congr_deriv ?_
  simp only [id, one_div, mul_one]
  field_simp
  ring

theorem posPart_eq_zero {c y t : ℝ} (hc : 0 < c) (hy : 0 < y) (ht : 0 < t) (h : 1 ≤ c ^ 2 * y * t)
    (v : ℝ) : max 0 (y / (v ^ 2 + c ^ 2 * y ^ 2) - t) = 0 := by
  apply max_eq_left
  have hpos : 0 < v ^ 2 + c ^ 2 * y ^ 2 := by positivity
  rw [sub_nonpos, div_le_iff₀ hpos]
  nlinarith [sq_nonneg v, mul_pos hy ht]

/-- **The explicit integral.** -/
theorem integral_posPart {c y t : ℝ} (hc : 0 < c) (hy : 0 < y) (ht : 0 < t)
    (h : c ^ 2 * y * t < 1) {B : ℝ} (hB : √(y / t - c ^ 2 * y ^ 2) ≤ B) :
    ∫ v in (-B)..B, max 0 (y / (v ^ 2 + c ^ 2 * y ^ 2) - t) =
      2 / c * (arccos (c * √(y * t)) - c * √(y * t) * √(1 - c ^ 2 * y * t)) := by
  set W := y / t - c ^ 2 * y ^ 2 with hW
  have hWpos : 0 < W := by
    rw [hW, sub_pos, lt_div_iff₀ ht]; nlinarith
  set V := √W with hV
  have hV0 : 0 < V := Real.sqrt_pos.mpr hWpos
  have hV2 : V ^ 2 = W := Real.sq_sqrt hWpos.le
  have hVB : V ≤ B := hB
  set g : ℝ → ℝ := fun v => max 0 (y / (v ^ 2 + c ^ 2 * y ^ 2) - t) with hg
  have hgc : Continuous g := by
    refine continuous_const.max ((continuous_const.div ?_ ?_).sub continuous_const)
    · fun_prop
    · intro v; positivity
  have hint : ∀ a b : ℝ, IntervalIntegrable g volume a b := fun a b => hgc.intervalIntegrable a b
  -- outside `[-V, V]` the integrand vanishes, inside it is the rational function minus `t`
  have hout : ∀ v, V ^ 2 ≤ v ^ 2 → g v = 0 := by
    intro v hv
    apply max_eq_left
    have hpos : 0 < v ^ 2 + c ^ 2 * y ^ 2 := by positivity
    rw [sub_nonpos, div_le_iff₀ hpos]
    rw [hV2, hW] at hv
    have : y ≤ t * (v ^ 2 + c ^ 2 * y ^ 2) := by
      have h1 : y / t ≤ v ^ 2 + c ^ 2 * y ^ 2 := by linarith
      rwa [div_le_iff₀ ht, mul_comm] at h1
    linarith
  have hin : ∀ v, v ^ 2 ≤ V ^ 2 → g v = y / (v ^ 2 + c ^ 2 * y ^ 2) - t := by
    intro v hv
    apply max_eq_right
    have hpos : 0 < v ^ 2 + c ^ 2 * y ^ 2 := by positivity
    rw [sub_nonneg, le_div_iff₀ hpos]
    rw [hV2, hW] at hv
    have h1 : v ^ 2 + c ^ 2 * y ^ 2 ≤ y / t := by linarith
    rw [le_div_iff₀ ht] at h1
    linarith
  rw [← integral_add_adjacent_intervals (hint (-B) (-V)) (hint (-V) B),
    ← integral_add_adjacent_intervals (hint (-V) V) (hint V B)]
  have e1 : ∫ v in (-B)..(-V), g v = 0 := by
    rw [integral_congr (g := fun _ => (0 : ℝ)) (fun v hv => ?_)]
    · simp
    · rw [uIcc_of_le (by linarith)] at hv
      exact hout v (by nlinarith [hv.1, hv.2])
  have e3 : ∫ v in V..B, g v = 0 := by
    rw [integral_congr (g := fun _ => (0 : ℝ)) (fun v hv => ?_)]
    · simp
    · rw [uIcc_of_le hVB] at hv
      exact hout v (by nlinarith [hv.1, hv.2])
  have e2 : ∫ v in (-V)..V, g v = 2 / c * arctan (V / (c * y)) - 2 * t * V := by
    rw [integral_congr (g := fun v => y / (v ^ 2 + c ^ 2 * y ^ 2) - t) (fun v hv => ?_)]
    · rw [integral_eq_sub_of_hasDerivAt (fun v _ => hasDerivAt_G hc hy v)
        (((continuous_const.div (by fun_prop) (fun v => by positivity)).sub continuous_const :
          Continuous fun v : ℝ => y / (v ^ 2 + c ^ 2 * y ^ 2) - t).intervalIntegrable _ _)]
      have : -V / (c * y) = -(V / (c * y)) := by ring
      rw [this, arctan_neg]
      ring
    · rw [uIcc_of_le (by linarith)] at hv
      exact hin v (by nlinarith [hv.1, hv.2])
  rw [e1, e2, e3, zero_add, add_zero]
  -- identify with the arccosine
  set a := c * √(y * t) with ha
  have hyt : 0 < y * t := mul_pos hy ht
  have ha0 : 0 < a := mul_pos hc (Real.sqrt_pos.mpr hyt)
  have ha2 : a ^ 2 = c ^ 2 * y * t := by rw [ha, mul_pow, Real.sq_sqrt hyt.le]; ring
  have h1a : 0 < 1 - a ^ 2 := by rw [ha2]; linarith
  have hs : √(1 - c ^ 2 * y * t) = √(1 - a ^ 2) := by rw [ha2]
  rw [hs]
  have harc : arctan (V / (c * y)) = arccos a := by
    rw [arccos_eq_arctan ha0]
    congr 1
    have hl : 0 ≤ V / (c * y) := by positivity
    have hr : 0 ≤ √(1 - a ^ 2) / a := by positivity
    have hsq : (V / (c * y)) ^ 2 = (√(1 - a ^ 2) / a) ^ 2 := by
      rw [div_pow, div_pow, hV2, Real.sq_sqrt h1a.le, ha2, hW]
      field_simp
    exact (pow_left_inj₀ hl hr (by norm_num : (2 : ℕ) ≠ 0)).mp hsq
  have htV : t * V = a * √(1 - a ^ 2) / c := by
    have hl : 0 ≤ t * V := by positivity
    have hr : 0 ≤ a * √(1 - a ^ 2) / c := by positivity
    have hsq : (t * V) ^ 2 = (a * √(1 - a ^ 2) / c) ^ 2 := by
      rw [mul_pow, hV2, div_pow, mul_pow, Real.sq_sqrt h1a.le, ha2, hW]
      field_simp
    exact (pow_left_inj₀ hl hr (by norm_num : (2 : ℕ) ≠ 0)).mp hsq
  rw [harc, show 2 * t * V = 2 * (t * V) by ring, htV]
  field_simp

/-! ### Counting coprime residues -/

theorem card_coprime_Ico_le (c : ℕ) (hc : 0 < c) (a : ℤ) :
    ((Finset.Ico a (a + c)).filter (fun d => IsCoprime d (c : ℤ))).card ≤ Nat.totient c := by
  rw [Nat.totient_eq_card_coprime]
  have hc' : (0 : ℤ) < c := by exact_mod_cast hc
  refine Finset.card_le_card_of_injOn (fun d => (d % c).toNat) ?_ ?_
  · intro d hd
    rw [Finset.mem_coe, Finset.mem_filter] at hd
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
    have h0 : 0 ≤ d % c := Int.emod_nonneg d hc'.ne'
    have hlt : d % c < c := Int.emod_lt_of_pos d hc'
    refine ⟨by show (d % c).toNat < c; omega, ?_⟩
    have hcop : IsCoprime (d % c) (c : ℤ) := by
      rw [Int.emod_def, show d - (c : ℤ) * (d / c) = d + (-(d / c)) * c by ring,
        IsCoprime.add_mul_right_left_iff]
      exact hd.2
    have hcast : ((d % c).toNat : ℤ) = d % c := Int.toNat_of_nonneg h0
    rw [← hcast] at hcop
    exact (Nat.isCoprime_iff_coprime.mp hcop).symm
  · intro d1 h1 d2 h2 heq
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ico] at h1 h2
    have e1 : 0 ≤ d1 % c := Int.emod_nonneg d1 hc'.ne'
    have e2 : 0 ≤ d2 % c := Int.emod_nonneg d2 hc'.ne'
    have heq' : d1 % c = d2 % c := by
      have := congrArg (fun n : ℕ => (n : ℤ)) heq
      simpa [Int.toNat_of_nonneg e1, Int.toNat_of_nonneg e2] using this
    have hdvd : (c : ℤ) ∣ d2 - d1 := (Int.ModEq.dvd heq')
    obtain ⟨k, hk⟩ := hdvd
    have hb1 : d2 - d1 < c := by omega
    have hb2 : d1 - d2 < c := by omega
    have hk1 : k < 1 := by
      by_contra hk1; push Not at hk1
      have : (c : ℤ) * 1 ≤ c * k := mul_le_mul_of_nonneg_left hk1 hc'.le
      linarith
    have hk2 : -1 < k := by
      by_contra hk2; push Not at hk2
      have : (c : ℤ) * k ≤ c * (-1) := mul_le_mul_of_nonneg_left hk2 hc'.le
      linarith
    have hk0 : k = 0 := by omega
    rw [hk0, mul_zero] at hk
    omega

/-! ### Averaging over residues -/

theorem average_le {c : ℕ} (hc : 0 < c) {f : ℝ → ℝ} (hf : Continuous f) (hf0 : ∀ v, 0 ≤ f v)
    {B : ℝ} (hB0 : 0 ≤ B) (D : Finset ℤ) (hD : ∀ d ∈ D, IsCoprime d (c : ℤ) ∧ -B ≤ d ∧ (d : ℝ) + c ≤ B) :
    ∑ d ∈ D, ∫ u in (0 : ℝ)..1, f (c * u + d) ≤ (Nat.totient c / c) * ∫ v in (-B)..B, f v := by
  have hc' : (0 : ℝ) < c := by exact_mod_cast hc
  -- change variables
  have hsub : ∀ d ∈ D, ∫ u in (0 : ℝ)..1, f (c * u + d) =
      (c : ℝ)⁻¹ * ∫ v in Ioc (-B) B, (Ioc (d : ℝ) (d + c)).indicator f v := by
    intro d hd
    rw [intervalIntegral.integral_comp_mul_add f hc'.ne', smul_eq_mul]
    congr 1
    simp only [mul_zero, zero_add, mul_one]
    rw [intervalIntegral.integral_of_le (by linarith), add_comm (c : ℝ)]
    rw [setIntegral_indicator measurableSet_Ioc]
    congr 1
    rw [inter_eq_right.mpr]
    exact Ioc_subset_Ioc (hD d hd).2.1 (hD d hd).2.2
  rw [Finset.sum_congr rfl hsub, ← Finset.mul_sum]
  have hIB : IntegrableOn f (Ioc (-B) B) := hf.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  rw [← integral_finset_sum _ fun d _ => (hIB.indicator measurableSet_Ioc)]
  rw [intervalIntegral.integral_of_le (by linarith : -B ≤ B)]
  have hpt : ∀ v, ∑ d ∈ D, (Ioc (d : ℝ) (d + c)).indicator f v ≤ Nat.totient c * f v := by
    intro v
    simp only [Set.indicator_apply]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    refine mul_le_mul_of_nonneg_right ?_ (hf0 v)
    have hsubset : D.filter (fun d : ℤ => v ∈ Ioc ((d : ℤ) : ℝ) (d + c)) ⊆
        (Finset.Ico (⌈v⌉ - (c : ℤ)) (⌈v⌉ - (c : ℤ) + c)).filter
          (fun d : ℤ => IsCoprime d (c : ℤ)) := by
      intro d hd
      rw [Finset.mem_filter] at hd ⊢
      obtain ⟨hdD, hv1, hv2⟩ := hd
      refine ⟨Finset.mem_Ico.mpr ⟨?_, ?_⟩, (hD d hdD).1⟩
      · have : ⌈v⌉ ≤ d + c := Int.ceil_le.mpr (by push_cast; linarith)
        linarith
      · have : (d : ℝ) < ⌈v⌉ := lt_of_lt_of_le hv1 (Int.le_ceil v)
        have : d < ⌈v⌉ := by exact_mod_cast this
        linarith
    have := (Finset.card_le_card hsubset).trans (card_coprime_Ico_le c hc (⌈v⌉ - c))
    exact_mod_cast this
  have hsumint : IntegrableOn (fun v => ∑ d ∈ D, (Ioc (d : ℝ) (d + c)).indicator f v) (Ioc (-B) B) :=
    integrable_finset_sum _ fun d _ => hIB.indicator measurableSet_Ioc
  have hmono := setIntegral_mono_on hsumint (hIB.const_mul (Nat.totient c : ℝ)) measurableSet_Ioc
    (fun v _ => hpt v)
  rw [MeasureTheory.integral_const_mul] at hmono
  calc (c : ℝ)⁻¹ * ∫ v in Ioc (-B) B, ∑ d ∈ D, (Ioc (d : ℝ) (d + c)).indicator f v
      ≤ (c : ℝ)⁻¹ * (Nat.totient c * ∫ v in Ioc (-B) B, f v) :=
        mul_le_mul_of_nonneg_left hmono (inv_nonneg.mpr hc'.le)
    _ = (Nat.totient c / c) * ∫ v in Ioc (-B) B, f v := by ring

end Zeta7Valence

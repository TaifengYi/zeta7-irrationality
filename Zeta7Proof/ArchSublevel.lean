import Mathlib

/-! C1, step 1: a quantitative sublevel-set bound.

If `u : ℝ → ℝ` is smooth and its `k`-th derivative is bounded below in absolute value by `c > 0`
on `[a, b]`, then

`volume {t ∈ [a,b] | |u t| ≤ ρ} ≤ subConst k * (ρ / c) ^ (1/k)`.

The proof is the classical induction on `k`. For `k = 1` the mean value theorem forces the
sublevel set to have small diameter. For the step, the sublevel set of the `k`-th derivative at
height `λ` has small diameter by the same argument, so it lies in one interval; on the (at most
two) remaining intervals the `k`-th derivative is bounded below by `λ`, and the induction
hypothesis applies. The choice `λ = c (ρ/c)^{1/(k+1)}` balances the two contributions.

Only derivatives of order `≥ 1` occur, so the bound applies to `u - const` with the same
constants. That is what makes the small-ball estimate for the pushforward measure uniform in the
centre. -/
noncomputable section
set_option autoImplicit false
namespace Zeta7Arch
open MeasureTheory Set

/-- The constant of the sublevel bound. -/
def subConst : ℕ → ℝ
  | 0 => 1
  | (k + 1) => 8 + 2 * subConst k

theorem subConst_pos (k : ℕ) : 0 < subConst k := by
  induction k with
  | zero => norm_num [subConst]
  | succ k ih => rw [subConst]; linarith

/-- The mean value theorem forces a sublevel set of a function with a large derivative to have
small diameter. -/
theorem sublevel_dist_le {v : ℝ → ℝ} (hv : Differentiable ℝ v) {a b c lam : ℝ} (hc : 0 < c)
    (hd : ∀ t ∈ Icc a b, c ≤ |deriv v t|)
    {t₀ t : ℝ} (ht₀ : t₀ ∈ Icc a b) (ht : t ∈ Icc a b)
    (h₀ : |v t₀| ≤ lam) (h : |v t| ≤ lam) : |t - t₀| ≤ 2 * lam / c := by
  rcases eq_or_ne t t₀ with rfl | hne
  · have hlam : 0 ≤ lam := le_trans (abs_nonneg _) h
    simp only [sub_self, abs_zero]
    positivity
  set p := min t t₀ with hp
  set q := max t t₀ with hq
  have hpq : p < q := by
    rcases lt_or_gt_of_ne hne with h' | h'
    · rw [hp, hq, min_eq_left h'.le, max_eq_right h'.le]; exact h'
    · rw [hp, hq, min_eq_right h'.le, max_eq_left h'.le]; exact h'
  have hsub : Icc p q ⊆ Icc a b :=
    Icc_subset_Icc (le_min ht.1 ht₀.1) (max_le ht.2 ht₀.2)
  obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope v (deriv v) hpq
    hv.continuous.continuousOn (fun x _ => hv.differentiableAt.hasDerivAt)
  have hcle : c ≤ |deriv v ξ| := hd ξ (hsub (Ioo_subset_Icc_self hξ))
  have hnum : |v q - v p| ≤ 2 * lam := by
    have h1 : |v q| ≤ lam := by
      rcases max_cases t t₀ with ⟨h', _⟩ | ⟨h', _⟩ <;> rw [hq, h'] <;> assumption
    have h2 : |v p| ≤ lam := by
      rcases min_cases t t₀ with ⟨h', _⟩ | ⟨h', _⟩ <;> rw [hp, h'] <;> assumption
    calc |v q - v p| ≤ |v q| + |v p| := abs_sub _ _
      _ ≤ 2 * lam := by linarith
  have hdiff : |t - t₀| = q - p := by
    rcases lt_or_gt_of_ne hne with h' | h'
    · rw [hp, hq, min_eq_left h'.le, max_eq_right h'.le, abs_of_nonpos (by linarith)]; ring
    · rw [hp, hq, min_eq_right h'.le, max_eq_left h'.le, abs_of_nonneg (by linarith)]
  have hqp : 0 < q - p := by linarith
  have habs : c * (q - p) ≤ 2 * lam := by
    have hmul : |deriv v ξ| * (q - p) ≤ 2 * lam := by
      rw [hslope, abs_div, abs_of_pos hqp, div_mul_cancel₀ _ hqp.ne']
      exact hnum
    nlinarith [abs_nonneg (deriv v ξ)]
  rw [hdiff, le_div_iff₀ hc]
  linarith

/-- **Sublevel-set bound.** -/
theorem sublevel_volume_le (k : ℕ) (hk : 1 ≤ k) {u : ℝ → ℝ}
    (hu : ∀ j : ℕ, Differentiable ℝ (iteratedDeriv j u)) :
    ∀ {a b c ρ : ℝ}, 0 < c → 0 < ρ → (∀ t ∈ Icc a b, c ≤ |iteratedDeriv k u t|) →
      volume {t ∈ Icc a b | |u t| ≤ ρ} ≤
        ENNReal.ofReal (subConst k * (ρ / c) ^ ((k : ℝ)⁻¹)) := by
  have hu0 : Differentiable ℝ u := by simpa using hu 0
  induction k, hk using Nat.le_induction with
  | base =>
    intro a b c ρ hc hρ hd
    simp only [Nat.cast_one, inv_one, Real.rpow_one]
    have hd' : ∀ t ∈ Icc a b, c ≤ |deriv u t| := fun t ht => by
      simpa only [iteratedDeriv_one] using hd t ht
    rcases eq_empty_or_nonempty {t ∈ Icc a b | |u t| ≤ ρ} with he | ⟨t₀, ht₀⟩
    · rw [he]; simp
    · obtain ⟨ht₀I, ht₀u⟩ := ht₀
      have hsub : {t ∈ Icc a b | |u t| ≤ ρ} ⊆ Icc (t₀ - 2 * ρ / c) (t₀ + 2 * ρ / c) := by
        intro t ht
        obtain ⟨htI, htu⟩ := ht
        have hdist := sublevel_dist_le hu0 hc hd' ht₀I htI ht₀u htu
        rw [abs_le] at hdist
        exact ⟨by linarith [hdist.1], by linarith [hdist.2]⟩
      calc volume {t ∈ Icc a b | |u t| ≤ ρ}
          ≤ volume (Icc (t₀ - 2 * ρ / c) (t₀ + 2 * ρ / c)) := measure_mono hsub
        _ = ENNReal.ofReal (4 * (ρ / c)) := by
            rw [Real.volume_Icc]
            congr 1
            field_simp
            ring
        _ ≤ ENNReal.ofReal (subConst 1 * (ρ / c)) := by
            apply ENNReal.ofReal_le_ofReal
            have hsc : subConst 1 = 10 := by norm_num [subConst]
            have : 0 < ρ / c := div_pos hρ hc
            rw [hsc]
            linarith
  | succ k hk ih =>
    intro a b c ρ hc hρ hd
    push_cast
    set s : ℝ := ρ / c with hs
    have hs0 : 0 < s := div_pos hρ hc
    set e : ℝ := ((k : ℝ) + 1)⁻¹ with he
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    have he0 : 0 < e := by rw [he]; positivity
    set lam : ℝ := c * s ^ e with hlam
    have hse : 0 < s ^ e := Real.rpow_pos_of_pos hs0 e
    have hlam0 : 0 < lam := by rw [hlam]; positivity
    have hvd : Differentiable ℝ (iteratedDeriv k u) := hu k
    have hdv : ∀ t ∈ Icc a b, c ≤ |deriv (iteratedDeriv k u) t| := by
      intro t ht
      have h := hd t ht
      rwa [iteratedDeriv_succ] at h
    -- the two algebraic identities
    have key1 : 2 * lam / c = 2 * s ^ e := by rw [hlam]; field_simp
    have hkne : (k : ℝ) ≠ 0 := hk0.ne'
    have hk1ne : (k : ℝ) + 1 ≠ 0 := by positivity
    have key2 : (ρ / lam) ^ ((k : ℝ)⁻¹) = s ^ e := by
      have hρc : ρ = c * s := by rw [hs]; field_simp
      have h1 : ρ / lam = s ^ ((k : ℝ) / ((k : ℝ) + 1)) := by
        rw [hlam, hρc, mul_div_mul_left _ _ hc.ne']
        rw [show ((k : ℝ) / ((k : ℝ) + 1)) = 1 - e by rw [he]; field_simp; ring,
          Real.rpow_sub hs0, Real.rpow_one]
      rw [h1, ← Real.rpow_mul hs0.le]
      congr 1
      rw [he]
      field_simp
    have hCk := subConst_pos k
    rcases eq_empty_or_nonempty {t ∈ Icc a b | |iteratedDeriv k u t| ≤ lam} with hemp | ⟨t₀, ht₀⟩
    · have hd2 : ∀ t ∈ Icc a b, lam ≤ |iteratedDeriv k u t| := by
        intro t ht
        by_contra hlt
        have hmem : t ∈ {t ∈ Icc a b | |iteratedDeriv k u t| ≤ lam} := ⟨ht, (not_le.mp hlt).le⟩
        rw [hemp] at hmem
        exact hmem
      calc volume {t ∈ Icc a b | |u t| ≤ ρ}
          ≤ ENNReal.ofReal (subConst k * (ρ / lam) ^ ((k : ℝ)⁻¹)) := ih hlam0 hρ hd2
        _ ≤ ENNReal.ofReal (subConst (k + 1) * s ^ e) := by
            apply ENNReal.ofReal_le_ofReal
            rw [key2, subConst]
            nlinarith
    · obtain ⟨ht₀I, ht₀v⟩ := ht₀
      set D : ℝ := 2 * lam / c with hD
      have hD0 : 0 < D := by rw [hD]; positivity
      have hmid : ∀ t ∈ Icc a b, |iteratedDeriv k u t| ≤ lam → |t - t₀| ≤ D := fun t ht h =>
        sublevel_dist_le hvd hc hdv ht₀I ht ht₀v h
      have hleft : ∀ t ∈ Icc a (t₀ - 2 * D), lam ≤ |iteratedDeriv k u t| := by
        intro t ht
        by_contra hlt
        have htab : t ∈ Icc a b := ⟨ht.1, by have := ht₀I.2; have := ht.2; linarith⟩
        have h := hmid t htab (not_le.mp hlt).le
        rw [abs_le] at h
        have := ht.2
        linarith [h.1]
      have hright : ∀ t ∈ Icc (t₀ + 2 * D) b, lam ≤ |iteratedDeriv k u t| := by
        intro t ht
        by_contra hlt
        have htab : t ∈ Icc a b := ⟨by have := ht₀I.1; have := ht.1; linarith, ht.2⟩
        have h := hmid t htab (not_le.mp hlt).le
        rw [abs_le] at h
        have := ht.1
        linarith [h.2]
      have hEsub : {t ∈ Icc a b | |u t| ≤ ρ} ⊆
          ({t ∈ Icc a (t₀ - 2 * D) | |u t| ≤ ρ} ∪ Icc (t₀ - 2 * D) (t₀ + 2 * D)) ∪
            {t ∈ Icc (t₀ + 2 * D) b | |u t| ≤ ρ} := by
        intro t ht
        obtain ⟨htI, htu⟩ := ht
        by_cases h1 : t ≤ t₀ - 2 * D
        · exact Or.inl (Or.inl ⟨⟨htI.1, h1⟩, htu⟩)
        · by_cases h2 : t ≤ t₀ + 2 * D
          · exact Or.inl (Or.inr ⟨by linarith, h2⟩)
          · exact Or.inr ⟨⟨by linarith, htI.2⟩, htu⟩
      have hmidvol : volume (Icc (t₀ - 2 * D) (t₀ + 2 * D)) = ENNReal.ofReal (4 * D) := by
        rw [Real.volume_Icc]
        congr 1
        ring
      calc volume {t ∈ Icc a b | |u t| ≤ ρ}
          ≤ volume ({t ∈ Icc a (t₀ - 2 * D) | |u t| ≤ ρ} ∪ Icc (t₀ - 2 * D) (t₀ + 2 * D)) +
              volume {t ∈ Icc (t₀ + 2 * D) b | |u t| ≤ ρ} :=
            le_trans (measure_mono hEsub) (measure_union_le _ _)
        _ ≤ (volume {t ∈ Icc a (t₀ - 2 * D) | |u t| ≤ ρ} +
              volume (Icc (t₀ - 2 * D) (t₀ + 2 * D))) +
              volume {t ∈ Icc (t₀ + 2 * D) b | |u t| ≤ ρ} :=
            add_le_add (measure_union_le _ _) le_rfl
        _ ≤ (ENNReal.ofReal (subConst k * (ρ / lam) ^ ((k : ℝ)⁻¹)) + ENNReal.ofReal (4 * D)) +
              ENNReal.ofReal (subConst k * (ρ / lam) ^ ((k : ℝ)⁻¹)) := by
            gcongr
            · exact ih hlam0 hρ hleft
            · exact le_of_eq hmidvol
            · exact ih hlam0 hρ hright
        _ = ENNReal.ofReal (subConst k * (ρ / lam) ^ ((k : ℝ)⁻¹) + 4 * D +
              subConst k * (ρ / lam) ^ ((k : ℝ)⁻¹)) := by
            rw [← ENNReal.ofReal_add (by positivity) (by positivity),
              ← ENNReal.ofReal_add (by positivity) (by positivity)]
        _ = ENNReal.ofReal (subConst (k + 1) * s ^ e) := by
            congr 1
            rw [key2, key1, subConst]
            ring

end Zeta7Arch

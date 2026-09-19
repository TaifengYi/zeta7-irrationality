import Zeta7Proof.PNT.Wiener4

/-! Consequences of the ported `Zeta7PNT.WeakPNT` used by the auxiliary estimate P8:

* `ψ(n)/n → 1` and `θ(n)/n → 1` along the naturals (Mathlib's Chebyshev functions);
* the Cesàro form `Σ_{k<M} θ(k) = M²/2 + o(M²)`;
* the exact finite identity `Σ_{p≤X} (X-p) log p = Σ_{k<M} θ(k) + (X-M) θ(M)`, `M = ⌊X⌋`;
* hence `Σ_{p≤X} (X-p) log p = X²/2 + o(X²)`. -/
noncomputable section
set_option autoImplicit false

open Filter Topology Real

namespace Zeta7PNT

theorem range_succ_eq_Icc (n : ℕ) : Finset.range (n + 1) = Finset.Icc 0 n := by
  ext i; simp only [Finset.mem_range, Finset.mem_Icc]; omega

theorem psi_nat_eq_cumsum (n : ℕ) :
    Chebyshev.psi n = cumsum (⇑ArithmeticFunction.vonMangoldt) (n + 1) := by
  rw [Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast, cumsum, range_succ_eq_Icc]

theorem psi_nat_tendsto : Tendsto (fun n : ℕ => Chebyshev.psi n / n) atTop (𝓝 1) := by
  have h1 := WeakPNT.comp (tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun n : ℕ => 1 + 1 / (n : ℝ)) atTop (𝓝 (1 + 0)) :=
    tendsto_const_nhds.add tendsto_one_div_atTop_nhds_zero_nat
  rw [add_zero] at h2
  have h3 := h1.mul h2
  rw [mul_one] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hn1 : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  simp only [Function.comp, psi_nat_eq_cumsum]
  push_cast at hn1 ⊢
  field_simp

theorem theta_nat_tendsto : Tendsto (fun n : ℕ => Chebyshev.theta n / n) atTop (𝓝 1) := by
  obtain ⟨C, hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  have hsq : Tendsto (fun n : ℕ => C / Real.sqrt n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have hdiff : Tendsto (fun n : ℕ => (Chebyshev.psi n - Chebyshev.theta n) / n) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsq ?_ ?_
    · filter_upwards [eventually_ge_atTop 1] with n hn
      exact div_nonneg (sub_nonneg.mpr (Chebyshev.theta_le_psi _)) (Nat.cast_nonneg _)
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have hpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have h := hC n
      calc (Chebyshev.psi n - Chebyshev.theta n) / n ≤ C * Real.sqrt n / n :=
            div_le_div_of_nonneg_right h hpos.le
        _ = C / Real.sqrt n := by
            rw [mul_div_assoc, Real.sqrt_div_self', mul_one_div]
  have h := psi_nat_tendsto.sub hdiff
  rw [sub_zero] at h
  refine h.congr' (Eventually.of_forall fun n => ?_)
  simp only
  ring

/-- `|θ(k) - k| ≤ ε k` for all large `k`. -/
theorem theta_eventually {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → |Chebyshev.theta k - k| ≤ ε * k := by
  obtain ⟨K, hK⟩ := Metric.tendsto_atTop.mp theta_nat_tendsto ε hε
  refine ⟨max K 1, fun k hk => ?_⟩
  have hk1 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have h := hK k (le_of_max_le_left hk)
  rw [Real.dist_eq] at h
  have e : Chebyshev.theta k - k = k * (Chebyshev.theta k / k - 1) := by
    field_simp
  rw [e, abs_mul, abs_of_pos hk1, mul_comm]
  exact mul_le_mul_of_nonneg_right h.le hk1.le

theorem sum_range_natCast (M : ℕ) : ∑ k ∈ Finset.range M, (k : ℝ) = M * (M - 1) / 2 := by
  have h := Finset.sum_range_id_mul_two M
  have h' : ((∑ i ∈ Finset.range M, i : ℕ) : ℝ) * 2 = ((M * (M - 1) : ℕ) : ℝ) := by
    exact_mod_cast h
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simp
  push_cast [Nat.cast_sub hM] at h'
  linarith

/-- **Cesàro form**: `|Σ_{k<M} θ(k) - M²/2| ≤ ε M²` for large `M`. -/
theorem theta_cesaro {ε : ℝ} (hε : 0 < ε) :
    ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
      |∑ k ∈ Finset.range M, Chebyshev.theta k - (M : ℝ) ^ 2 / 2| ≤ ε * M ^ 2 := by
  obtain ⟨K, hK⟩ := theta_eventually (half_pos hε)
  set B := ∑ k ∈ Finset.range K, |Chebyshev.theta k - k| with hB
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun _ _ => abs_nonneg _
  obtain ⟨M₁, hM₁⟩ := exists_nat_gt (4 * B / ε + 2 / ε + K + 1)
  refine ⟨M₁, fun M hM => ?_⟩
  have hMK : K ≤ M := by
    have : (K : ℝ) < M := by
      have : (M₁ : ℝ) ≤ M := by exact_mod_cast hM
      have h4 : 0 ≤ 4 * B / ε := by positivity
      have h5 : 0 ≤ 2 / ε := by positivity
      linarith
    exact_mod_cast this.le
  have hMpos : (0 : ℝ) < M := by
    have : (M₁ : ℝ) ≤ M := by exact_mod_cast hM
    have h4 : 0 ≤ 4 * B / ε := by positivity
    have h5 : 0 ≤ 2 / ε := by positivity
    linarith
  -- split the error sum at `K`
  have hsplit : |∑ k ∈ Finset.range M, (Chebyshev.theta k - k)| ≤ B + ε / 2 * (M * (M - 1) / 2) := by
    rw [← Finset.sum_range_add_sum_Ico _ hMK]
    refine (abs_add_le _ _).trans (add_le_add (Finset.abs_sum_le_sum_abs _ _) ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ k ∈ Finset.Ico K M, |Chebyshev.theta k - k|
        ≤ ∑ k ∈ Finset.Ico K M, ε / 2 * k :=
          Finset.sum_le_sum fun k hk => hK k (Finset.mem_Ico.mp hk).1
      _ ≤ ∑ k ∈ Finset.range M, ε / 2 * k := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro k hk; simp only [Finset.mem_Ico] at hk; simp only [Finset.mem_range]; omega
          · intro k _ _; positivity
      _ = ε / 2 * (M * (M - 1) / 2) := by rw [← Finset.mul_sum, sum_range_natCast]
  have e : ∑ k ∈ Finset.range M, Chebyshev.theta k - (M : ℝ) ^ 2 / 2 =
      ∑ k ∈ Finset.range M, (Chebyshev.theta k - k) - M / 2 := by
    rw [Finset.sum_sub_distrib, sum_range_natCast]; ring
  rw [e]
  have hB' : B ≤ ε / 4 * M ^ 2 := by
    have h1 : 4 * B / ε ≤ M := by
      have : (M₁ : ℝ) ≤ M := by exact_mod_cast hM
      have h5 : 0 ≤ 2 / ε := by positivity
      linarith
    have h2 : 4 * B ≤ ε * M := by
      rw [div_le_iff₀ hε] at h1; linarith
    have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by exact_mod_cast hMpos)
    have h3 : ε * M ≤ ε * M ^ 2 := by nlinarith
    nlinarith
  have hM2 : (M : ℝ) / 2 ≤ ε / 4 * M ^ 2 := by
    have h1 : 2 / ε ≤ M := by
      have : (M₁ : ℝ) ≤ M := by exact_mod_cast hM
      have h4 : 0 ≤ 4 * B / ε := by positivity
      linarith
    have h2 : 2 ≤ ε * M := by
      rw [div_le_iff₀ hε] at h1; linarith
    have h3 : (M : ℝ) * 2 ≤ M * (ε * M) := mul_le_mul_of_nonneg_left h2 hMpos.le
    nlinarith
  have hmain : B + ε / 2 * (M * (M - 1) / 2) ≤ ε / 4 * M ^ 2 + ε / 4 * M ^ 2 := by nlinarith
  calc |∑ k ∈ Finset.range M, (Chebyshev.theta k - k) - M / 2|
      ≤ |∑ k ∈ Finset.range M, (Chebyshev.theta k - k)| + |(M : ℝ) / 2| := abs_sub _ _
    _ ≤ (ε / 4 * M ^ 2 + ε / 4 * M ^ 2) + ε / 4 * M ^ 2 := by
        rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ M / 2)]
        linarith
    _ ≤ ε * M ^ 2 := by nlinarith

/-! ### The weighted prime sum `Σ_{p ≤ X} (X - p) log p` -/

/-- `S(X) = Σ_{p ≤ X} (X - p) log p`. -/
def primeWeightSum (X : ℝ) : ℝ :=
  ∑ p ∈ (Finset.range (⌊X⌋₊ + 1)).filter Nat.Prime, (X - p) * Real.log p

theorem theta_nat_eq (k : ℕ) :
    Chebyshev.theta k = ∑ p ∈ (Finset.range (k + 1)).filter Nat.Prime, Real.log p := by
  rw [Chebyshev.theta_eq_sum_Icc, Nat.floor_natCast, range_succ_eq_Icc]

theorem weight_sum_identity (M : ℕ) :
    ∑ p ∈ (Finset.range (M + 1)).filter Nat.Prime, ((M : ℝ) - p) * Real.log p =
      ∑ k ∈ Finset.range M, Chebyshev.theta k := by
  induction M with
  | zero => simp [Finset.sum_filter]
  | succ M ih =>
    rw [Finset.sum_range_succ, ← ih, theta_nat_eq, Finset.sum_filter, Finset.sum_filter,
      Finset.sum_filter, Finset.sum_range_succ _ (M + 1)]
    have hlast : (if Nat.Prime (M + 1) then (((M + 1 : ℕ) : ℝ) - ((M + 1 : ℕ) : ℝ)) *
        Real.log ((M + 1 : ℕ) : ℝ) else 0) = 0 := by
      split_ifs <;> simp
    rw [hlast, add_zero, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    split_ifs <;> push_cast <;> ring

theorem primeWeightSum_eq {X : ℝ} (hX : 0 ≤ X) :
    primeWeightSum X = ∑ k ∈ Finset.range ⌊X⌋₊, Chebyshev.theta k +
      (X - ⌊X⌋₊) * Chebyshev.theta ⌊X⌋₊ := by
  rw [← weight_sum_identity, theta_nat_eq, primeWeightSum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  ring

theorem theta_le_two (x : ℝ) (hx : 0 ≤ x) : Chebyshev.theta x ≤ 2 * x := by
  have h := Chebyshev.theta_le_log4_mul_x hx
  have h4 : Real.log 4 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    have h2 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    have := Real.log_two_lt_d9
    linarith
  nlinarith

/-- **Weighted prime sum asymptotic**: `|S(X) - X²/2| ≤ ε X²` for large `X`. -/
theorem primeWeightSum_asymptotic {ε : ℝ} (hε : 0 < ε) :
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → |primeWeightSum X - X ^ 2 / 2| ≤ ε * X ^ 2 := by
  obtain ⟨M₀, hM₀⟩ := theta_cesaro (half_pos hε)
  refine ⟨M₀ + 1 + 8 / ε, fun X hX => ?_⟩
  have h8 : 0 ≤ 8 / ε := by positivity
  have hX0 : 0 ≤ X := by
    have : (0 : ℝ) ≤ M₀ := Nat.cast_nonneg _
    linarith
  set M := ⌊X⌋₊ with hMdef
  have hMX : (M : ℝ) ≤ X := Nat.floor_le hX0
  have hXM : X < M + 1 := Nat.lt_floor_add_one X
  have hMM0 : M₀ ≤ M := by
    apply Nat.le_floor
    linarith
  have hc := hM₀ M hMM0
  have hth := theta_le_two (M : ℝ) (Nat.cast_nonneg _)
  have hth0 := Chebyshev.theta_nonneg (M : ℝ)
  rw [primeWeightSum_eq hX0]
  have hXε : 8 ≤ ε * X := by
    have : 8 / ε ≤ X := by
      have : (0 : ℝ) ≤ M₀ := Nat.cast_nonneg _
      linarith
    rwa [div_le_iff₀ hε, mul_comm] at this
  have hM2 : (M : ℝ) ^ 2 ≤ X ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) M]
  have t1 : (X - M) * Chebyshev.theta M ≤ 2 * X := by nlinarith
  have t2 : 0 ≤ (X - M) * Chebyshev.theta M := mul_nonneg (by linarith) hth0
  have t3 : X ^ 2 / 2 - (M : ℝ) ^ 2 / 2 ≤ X + 1 := by nlinarith
  have t4 : 0 ≤ X ^ 2 / 2 - (M : ℝ) ^ 2 / 2 := by nlinarith
  rw [abs_le] at hc ⊢
  constructor <;> nlinarith

end Zeta7PNT

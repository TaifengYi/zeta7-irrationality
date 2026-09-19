import Zeta7Proof.AuxiliaryProfileSum
import Zeta7Proof.AuxiliaryProfileError
import Zeta7Proof.AuxiliaryDenominatorBound
import Zeta7Proof.AuxiliarySharpBound
import Zeta7Proof.AuxiliaryEstimateStatement

/-! P8, milestone 5: the auxiliary estimate P for the unchanged `actualCommonDeterminant`.

For `d ≥ 2`, `N = 7d + 176` and a prime `p ≠ 7` in the finite prime support:

* if `p ≥ 11`, `p ∤ c.den` and `N ≤ p²` (a *good* prime), then
  `-v_p(D_d) ≤ sharpThreshold d p N`, which is `0` for `p ≥ N` and `≤ d f(p/d) + 920` always;
* otherwise (an *exceptional* prime: `p < 11`, `p ∣ c.den` or `p² < N`),
  `-v_p(D_d) ≤ 6d (8⌊log_p N⌋ + 2⌊log_p c.den⌋ + 1)`.

Summing, `-Σ_{p≠7} v_p(D_d) log p ≤ Σ_{p≤7d} d f(p/d) log p + 920 θ(N) + E_c(d)` with
`E_c(d) = (⌊√N⌋ + c.den + 13) · 6d · (9 log N + 3 log c.den) = O_c(d^{7/4})`. The first term is
`(12325/168 + o(1)) d²` by the ported prime number theorem, `θ(N) = O(d)` by Chebyshev, and the
exceptional term is `o(d²)`. -/
noncomputable section
set_option autoImplicit false
namespace Zeta7Auxiliary
open Zeta7ProductFormula Zeta7Common Zeta7PNT

/-- Good primes for the sharp local estimate. -/
def goodPrime (c : ℚ) (d p : ℕ) : Prop := 11 ≤ p ∧ ¬ p ∣ c.den ∧ 7 * d + 176 ≤ p ^ 2

theorem sharpThreshold_eq_zero {d p N : ℕ} (h : N ≤ p) : sharpThreshold d p N = 0 := by
  simp [sharpThreshold, Nat.sub_eq_zero_of_le h]

/-- The good-prime part of the per-prime bound. -/
def goodPart (c : ℚ) (d p : ℕ) : ℝ := by
  classical
  exact if goodPrime c d p ∧ p < 7 * d + 176 then
    ((d : ℝ) * profileF ((p : ℝ) / d) + 920) * Real.log p else 0

/-- The exceptional-prime part of the per-prime bound. -/
def badPart (c : ℚ) (d p : ℕ) : ℝ := by
  classical
  exact if goodPrime c d p then 0 else
    ((6 * d * capAll p (7 * d + 176) c : ℕ) : ℝ) * Real.log p

theorem profile_term_nonneg (d p : ℕ) : 0 ≤ ((d : ℝ) * profileF ((p : ℝ) / d) + 920) * Real.log p := by
  have h1 := profileF_nonneg (div_nonneg (Nat.cast_nonneg (α := ℝ) p) (Nat.cast_nonneg (α := ℝ) d))
  have h2 : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  positivity

theorem goodPart_nonneg (c : ℚ) (d p : ℕ) : 0 ≤ goodPart c d p := by
  classical
  unfold goodPart
  split_ifs
  · exact profile_term_nonneg d p
  · exact le_rfl

theorem badPart_nonneg (c : ℚ) (d p : ℕ) : 0 ≤ badPart c d p := by
  classical
  unfold badPart
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg p)

/-- **Per-prime bound** for the unchanged determinant. -/
theorem neg_val_log_le (c : ℚ) (d : ℕ) (hd : 2 ≤ d) (p : ℕ) (hp : p.Prime) :
    -((padicValRat p (actualCommonDeterminant d c) : ℝ) * Real.log p) ≤
      goodPart c d p + badPart c d p := by
  classical
  haveI := Fact.mk hp
  have hlog : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  rw [neg_mul_eq_neg_mul]
  unfold goodPart badPart
  by_cases hg : goodPrime c d p
  · obtain ⟨h11, hden, hN⟩ := hg
    have hs := actualCommonDeterminant_sharp_bound (p := p) h11 c hden d hd hN
    by_cases hpN : p < 7 * d + 176
    · rw [if_pos ⟨⟨h11, hden, hN⟩, hpN⟩, if_pos ⟨h11, hden, hN⟩, add_zero]
      have hsR : -(padicValRat p (actualCommonDeterminant d c) : ℝ) ≤
          (sharpThreshold d p (7 * d + 176) : ℝ) := by exact_mod_cast hs
      have he := sharpThreshold_profile_error p hd
      rw [abs_le] at he
      exact mul_le_mul_of_nonneg_right (by linarith [he.2]) hlog
    · rw [if_neg (fun h => hpN h.2), if_pos ⟨h11, hden, hN⟩, add_zero]
      rw [sharpThreshold_eq_zero (not_lt.mp hpN)] at hs
      have hsR : -(padicValRat p (actualCommonDeterminant d c) : ℝ) ≤ 0 := by exact_mod_cast hs
      nlinarith
  · rw [if_neg (fun h => hg h.1), if_neg hg, zero_add]
    have hs := actualCommonDeterminant_general_bound (p := p) d c
    have hsR : -(padicValRat p (actualCommonDeterminant d c) : ℝ) ≤
        ((6 * d * capAll p (7 * d + 176) c : ℕ) : ℝ) := by exact_mod_cast hs
    exact mul_le_mul_of_nonneg_right hsR hlog

/-! ### The good-prime sum -/

theorem profile_extend (d : ℕ) (hd : 1 ≤ d) :
    ∑ p ∈ (Finset.range (7 * d + 176)).filter Nat.Prime,
      (d : ℝ) * profileF ((p : ℝ) / d) * Real.log p = profileSum d := by
  unfold profileSum
  symm
  apply Finset.sum_subset
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_range] at hp ⊢
    exact ⟨by omega, hp.2⟩
  · intro p hp hpn
    simp only [Finset.mem_filter, Finset.mem_range, not_and] at hp hpn
    have h7 : 7 * d ≤ p := by
      by_contra h
      exact hpn (by omega) hp.2
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd
    have hz : (7 : ℝ) ≤ (p : ℝ) / d := by
      rw [le_div_iff₀ hdR]
      exact_mod_cast h7
    rw [profile_table_zero hz, mul_zero, zero_mul]

theorem goodPart_sum_le (c : ℚ) (d : ℕ) (hd : 1 ≤ d) (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime) :
    ∑ p ∈ s, goodPart c d p ≤
      profileSum d + 920 * Chebyshev.theta ((7 * d + 176 : ℕ) : ℝ) := by
  classical
  have e1 : ∑ p ∈ s, goodPart c d p = ∑ p ∈ s.filter (fun p => goodPrime c d p ∧ p < 7 * d + 176),
      ((d : ℝ) * profileF ((p : ℝ) / d) + 920) * Real.log p := by
    rw [Finset.sum_filter]
    rfl
  rw [e1]
  have hsub : s.filter (fun p => goodPrime c d p ∧ p < 7 * d + 176) ⊆
      (Finset.range (7 * d + 176)).filter Nat.Prime := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_range] at hp ⊢
    exact ⟨hp.2.2, hs p hp.1⟩
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun p _ _ => profile_term_nonneg d p).trans ?_
  have e2 : ∑ p ∈ (Finset.range (7 * d + 176)).filter Nat.Prime,
      ((d : ℝ) * profileF ((p : ℝ) / d) + 920) * Real.log p =
      ∑ p ∈ (Finset.range (7 * d + 176)).filter Nat.Prime,
        (d : ℝ) * profileF ((p : ℝ) / d) * Real.log p +
      920 * ∑ p ∈ (Finset.range (7 * d + 176)).filter Nat.Prime, Real.log p := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun p _ => by ring
  rw [e2, profile_extend d hd]
  have hth : ∑ p ∈ (Finset.range (7 * d + 176)).filter Nat.Prime, Real.log p ≤
      Chebyshev.theta ((7 * d + 176 : ℕ) : ℝ) := by
    rw [theta_nat_eq]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_range] at hp ⊢
      exact ⟨by omega, hp.2⟩
    · intro p _ _; exact Real.log_natCast_nonneg p
  linarith

/-! ### The exceptional-prime sum -/

/-- The exceptional contribution `E_c(d)`. -/
def errE (c : ℚ) (d : ℕ) : ℝ :=
  ((Nat.sqrt (7 * d + 176) : ℝ) + c.den + 13) *
    (6 * d * (9 * Real.log ((7 * d + 176 : ℕ) : ℝ) + 3 * Real.log c.den))

theorem natLog_mul_log_le (p n : ℕ) (hn : n ≠ 0) :
    (Nat.log p n : ℝ) * Real.log p ≤ Real.log n := by
  rcases Nat.eq_zero_or_pos p with rfl | hp0
  · simp [Real.log_natCast_nonneg]
  have hpow : p ^ Nat.log p n ≤ n := Nat.pow_log_le_self p hn
  have hpos : (0 : ℝ) < ((p ^ Nat.log p n : ℕ) : ℝ) := by positivity
  have h := Real.log_le_log hpos (show ((p ^ Nat.log p n : ℕ) : ℝ) ≤ (n : ℝ) by exact_mod_cast hpow)
  rwa [Nat.cast_pow, Real.log_pow] at h

theorem badPart_term_le (c : ℚ) (d p : ℕ) (hp : p.Prime)
    (hpb : p ≤ (7 * d + 176) * c.den) :
    ((6 * d * capAll p (7 * d + 176) c : ℕ) : ℝ) * Real.log p ≤
      6 * d * (9 * Real.log ((7 * d + 176 : ℕ) : ℝ) + 3 * Real.log c.den) := by
  have hN := natLog_mul_log_le p (7 * d + 176) (by omega)
  have hD := natLog_mul_log_le p c.den c.den_nz
  have hlogN : 0 ≤ Real.log ((7 * d + 176 : ℕ) : ℝ) := Real.log_natCast_nonneg _
  have hlogD : 0 ≤ Real.log (c.den : ℝ) := Real.log_natCast_nonneg _
  have hlogp : Real.log p ≤ Real.log ((7 * d + 176 : ℕ) : ℝ) + Real.log c.den := by
    rw [← Real.log_mul (by positivity) (by exact_mod_cast c.den_nz)]
    apply Real.log_le_log (by exact_mod_cast hp.pos)
    exact_mod_cast hpb
  have e : ((6 * d * capAll p (7 * d + 176) c : ℕ) : ℝ) * Real.log p =
      6 * d * (8 * ((Nat.log p (7 * d + 176) : ℝ) * Real.log p) +
        2 * ((Nat.log p c.den : ℝ) * Real.log p) + Real.log p) := by
    simp only [capAll, logE]
    push_cast
    ring
  rw [e]
  have hd0 : (0 : ℝ) ≤ 6 * d := by positivity
  apply mul_le_mul_of_nonneg_left _ hd0
  linarith

theorem badPart_sum_le (c : ℚ) (d : ℕ) (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    ∑ p ∈ s, badPart c d p ≤ errE c d := by
  classical
  set N := 7 * d + 176 with hNdef
  let Bad : Finset ℕ := ((Finset.range (Nat.sqrt N + 1)) ∪ Finset.range 11 ∪
    Finset.range (c.den + 1)).filter (fun p => p.Prime ∧ p ≤ N * c.den)
  have e1 : ∑ p ∈ s, badPart c d p = ∑ p ∈ s.filter (fun p => ¬ goodPrime c d p),
      ((6 * d * capAll p N c : ℕ) : ℝ) * Real.log p := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun p _ => ?_
    unfold badPart
    split_ifs <;> rfl
  rw [e1]
  have hden1 : 1 ≤ c.den := Nat.pos_of_ne_zero c.den_nz
  have hsub : s.filter (fun p => ¬ goodPrime c d p) ⊆ Bad := by
    intro p hp
    simp only [Finset.mem_filter] at hp
    obtain ⟨hps, hng⟩ := hp
    have hpp := hs p hps
    simp only [Bad, Finset.mem_filter, Finset.mem_union, Finset.mem_range]
    unfold goodPrime at hng
    by_cases h11 : 11 ≤ p
    · by_cases hdv : p ∣ c.den
      · have hle : p ≤ c.den := Nat.le_of_dvd (Nat.pos_of_ne_zero c.den_nz) hdv
        refine ⟨Or.inr (by omega), hpp, ?_⟩
        calc p ≤ c.den := hle
          _ ≤ N * c.den := Nat.le_mul_of_pos_left _ (by omega)
      · have hsq : p ^ 2 < N := by
          by_contra h
          exact hng ⟨h11, hdv, not_lt.mp h⟩
        have hps' : p ≤ Nat.sqrt N := Nat.le_sqrt'.mpr (by nlinarith)
        refine ⟨Or.inl (Or.inl (by omega)), hpp, ?_⟩
        calc p ≤ N := by nlinarith
          _ ≤ N * c.den := Nat.le_mul_of_pos_right _ hden1
    · refine ⟨Or.inl (Or.inr (by omega)), hpp, ?_⟩
      calc p ≤ N := by omega
        _ ≤ N * c.den := Nat.le_mul_of_pos_right _ hden1
  have hnn : ∀ p ∈ Bad, p ∉ s.filter (fun p => ¬ goodPrime c d p) →
      0 ≤ ((6 * d * capAll p N c : ℕ) : ℝ) * Real.log p :=
    fun p _ _ => mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg p)
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub hnn).trans ?_
  have hterm : ∀ p ∈ Bad, ((6 * d * capAll p N c : ℕ) : ℝ) * Real.log p ≤
      6 * d * (9 * Real.log (N : ℝ) + 3 * Real.log c.den) := by
    intro p hp
    simp only [Bad, Finset.mem_filter] at hp
    exact badPart_term_le c d p hp.2.1 hp.2.2
  refine (Finset.sum_le_card_nsmul _ _ _ hterm).trans ?_
  rw [nsmul_eq_mul]
  have hcard : (Bad.card : ℝ) ≤ (Nat.sqrt N : ℝ) + c.den + 13 := by
    have h1 : Bad.card ≤ (Nat.sqrt N + 1) + 11 + (c.den + 1) := by
      refine (Finset.card_filter_le _ _).trans ?_
      refine (Finset.card_union_le _ _).trans ?_
      refine Nat.add_le_add ((Finset.card_union_le _ _).trans ?_) (by simp)
      simp
    have h2 : (Bad.card : ℝ) ≤ ((Nat.sqrt N + 1 + 11 + (c.den + 1) : ℕ) : ℝ) := by
      exact_mod_cast h1
    push_cast at h2
    linarith
  have hnonneg : 0 ≤ 6 * (d : ℝ) * (9 * Real.log (N : ℝ) + 3 * Real.log c.den) := by
    have := Real.log_natCast_nonneg N
    have := Real.log_natCast_nonneg c.den
    positivity
  unfold errE
  exact mul_le_mul_of_nonneg_right hcard hnonneg

/-- **Total bound** for the auxiliary sum. -/
theorem auxiliary_total_bound (c : ℚ) (d : ℕ) (hd : 2 ≤ d) :
    -(∑ p ∈ (primeSupport (actualCommonDeterminant d c)).erase 7,
      (padicValRat p (actualCommonDeterminant d c) : ℝ) * Real.log p) ≤
      profileSum d + 920 * Chebyshev.theta ((7 * d + 176 : ℕ) : ℝ) + errE c d := by
  set s := (primeSupport (actualCommonDeterminant d c)).erase 7
  have hs : ∀ p ∈ s, p.Prime := by
    intro p hp
    have := (Finset.mem_erase.mp hp).2
    unfold primeSupport at this
    exact (Finset.mem_filter.mp this).2
  rw [← Finset.sum_neg_distrib]
  calc ∑ p ∈ s, -((padicValRat p (actualCommonDeterminant d c) : ℝ) * Real.log p)
      ≤ ∑ p ∈ s, (goodPart c d p + badPart c d p) :=
        Finset.sum_le_sum fun p hp => neg_val_log_le c d hd p (hs p hp)
    _ = ∑ p ∈ s, goodPart c d p + ∑ p ∈ s, badPart c d p := Finset.sum_add_distrib
    _ ≤ (profileSum d + 920 * Chebyshev.theta ((7 * d + 176 : ℕ) : ℝ)) + errE c d :=
        add_le_add (goodPart_sum_le c d (by omega) s hs) (badPart_sum_le c d s hs)

/-! ### Lower-order terms -/

theorem theta_term_small {ε : ℝ} (hε : 0 < ε) :
    ∃ D : ℕ, ∀ d : ℕ, D ≤ d → 920 * Chebyshev.theta ((7 * d + 176 : ℕ) : ℝ) ≤ ε * (d : ℝ) ^ 2 := by
  obtain ⟨D, hD⟩ := exists_nat_gt (1840 * 183 / ε)
  refine ⟨max D 1, fun d hd => ?_⟩
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (le_of_max_le_right hd)
  have hdD : 1840 * 183 / ε < d := lt_of_lt_of_le hD (by exact_mod_cast le_of_max_le_left hd)
  have hth := theta_le_two (((7 * d + 176 : ℕ) : ℝ)) (Nat.cast_nonneg _)
  have hc : (((7 * d + 176 : ℕ) : ℝ)) = 7 * d + 176 := by push_cast; ring
  rw [hc] at hth ⊢
  have h1 : 1840 * 183 < ε * d := by
    rw [div_lt_iff₀ hε] at hdD; linarith
  have h2 : (7 * (d : ℝ) + 176) ≤ 183 * d := by linarith
  nlinarith [mul_le_mul_of_nonneg_right h1.le (by positivity : (0 : ℝ) ≤ d)]

theorem errE_small (c : ℚ) {ε : ℝ} (hε : 0 < ε) :
    ∃ D : ℕ, ∀ d : ℕ, D ≤ d → errE c d ≤ ε * (d : ℝ) ^ 2 := by
  set K : ℝ := (c.den : ℝ) + 13 with hK
  set L : ℝ := 3 * Real.log c.den with hL
  have hK0 : 0 ≤ K := by positivity
  have hL0 : 0 ≤ L := by have := Real.log_natCast_nonneg c.den; positivity
  set C₁ : ℝ := 36 + L + 36 * K + K * L with hC₁
  have hC₁0 : 0 < C₁ := by positivity
  set U : ℝ := 1098 * C₁ / ε with hU
  have hU0 : 0 < U := by positivity
  obtain ⟨D, hD⟩ := exists_nat_gt (U ^ 4)
  refine ⟨max D 1, fun d hd => ?_⟩
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (le_of_max_le_right hd)
  have hdD : U ^ 4 < d := lt_of_lt_of_le hD (by exact_mod_cast le_of_max_le_left hd)
  set Nr : ℝ := ((7 * d + 176 : ℕ) : ℝ) with hNr
  have hNr' : Nr = 7 * d + 176 := by rw [hNr]; push_cast; ring
  have hNr0 : 0 ≤ Nr := by positivity
  set u : ℝ := Real.sqrt (Real.sqrt Nr) with hu
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  have hu2 : u ^ 2 = Real.sqrt Nr := Real.sq_sqrt (Real.sqrt_nonneg _)
  have hu4 : u ^ 4 = Nr := by
    rw [show u ^ 4 = (u ^ 2) ^ 2 by ring, hu2, Real.sq_sqrt hNr0]
  have hu1 : 1 ≤ u := by
    by_contra h
    push Not at h
    have : u ^ 4 < 1 := pow_lt_one₀ hu0 h (by norm_num)
    rw [hu4] at this
    linarith
  have hupos : 0 < u := by linarith
  have hlog : Real.log Nr ≤ 4 * u := by
    rw [← hu4, Real.log_pow]
    have := Real.log_le_sub_one_of_pos hupos
    push_cast
    linarith
  have hsq : (Nat.sqrt (7 * d + 176) : ℝ) ≤ u ^ 2 := by
    rw [hu2]
    exact Real.nat_sqrt_le_real_sqrt
  have hUu : U ≤ u := by
    by_contra h
    push Not at h
    have : u ^ 4 < U ^ 4 := pow_lt_pow_left₀ h hu0 (by norm_num)
    rw [hu4, hNr'] at this
    linarith
  -- bound the two factors
  have hf1 : (Nat.sqrt (7 * d + 176) : ℝ) + c.den + 13 ≤ u ^ 2 + K := by linarith
  have hf2 : 9 * Real.log Nr + 3 * Real.log c.den ≤ 36 * u + L := by linarith
  have hlogN0 : 0 ≤ Real.log Nr := Real.log_natCast_nonneg _
  have hP : ((Nat.sqrt (7 * d + 176) : ℝ) + c.den + 13) *
      (9 * Real.log Nr + 3 * Real.log c.den) ≤ C₁ * u ^ 3 := by
    have h0 : 0 ≤ (Nat.sqrt (7 * d + 176) : ℝ) + c.den + 13 := by positivity
    have h0' : 0 ≤ 9 * Real.log Nr + 3 * Real.log c.den := by
      have := Real.log_natCast_nonneg c.den; positivity
    calc ((Nat.sqrt (7 * d + 176) : ℝ) + c.den + 13) * (9 * Real.log Nr + 3 * Real.log c.den)
        ≤ (u ^ 2 + K) * (36 * u + L) := mul_le_mul hf1 hf2 h0' (by positivity)
      _ ≤ C₁ * u ^ 3 := by
          have hu3 : u ≤ u ^ 3 := by nlinarith
          have hu3' : u ^ 2 ≤ u ^ 3 := by nlinarith
          have hu3'' : 1 ≤ u ^ 3 := by nlinarith
          rw [hC₁]
          nlinarith [mul_le_mul_of_nonneg_left hu3 hK0, mul_le_mul_of_nonneg_left hu3' hL0,
            mul_le_mul_of_nonneg_left hu3'' (mul_nonneg hK0 hL0)]
  have hE : errE c d ≤ 6 * d * (C₁ * u ^ 3) := by
    unfold errE
    rw [← hNr]
    have h6 : 0 ≤ 6 * (d : ℝ) := by positivity
    calc ((Nat.sqrt (7 * d + 176) : ℝ) + c.den + 13) * (6 * d * (9 * Real.log Nr + 3 * Real.log c.den))
        = 6 * d * (((Nat.sqrt (7 * d + 176) : ℝ) + c.den + 13) *
            (9 * Real.log Nr + 3 * Real.log c.den)) := by ring
      _ ≤ 6 * d * (C₁ * u ^ 3) := mul_le_mul_of_nonneg_left hP h6
  have hNd : Nr ≤ 183 * d := by rw [hNr']; linarith
  -- `6 C₁ d u³ · u ≤ 1098 C₁ d² ≤ ε u d²`
  have hkey : 6 * d * (C₁ * u ^ 3) * u ≤ ε * (d : ℝ) ^ 2 * u := by
    have e : 6 * d * (C₁ * u ^ 3) * u = 6 * C₁ * d * u ^ 4 := by ring
    rw [e, hu4]
    have h1 : 6 * C₁ * d * Nr ≤ 6 * C₁ * d * (183 * d) :=
      mul_le_mul_of_nonneg_left hNd (by positivity)
    have h2 : 1098 * C₁ ≤ ε * u := by
      have : 1098 * C₁ / ε ≤ u := hUu
      rw [div_le_iff₀ hε] at this; linarith
    have h3 : 1098 * C₁ * (d : ℝ) ^ 2 ≤ ε * u * (d : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right h2 (by positivity)
    nlinarith
  have hfin : 6 * d * (C₁ * u ^ 3) ≤ ε * (d : ℝ) ^ 2 := le_of_mul_le_mul_right hkey hupos
  linarith

/-! ### P -/

/-- **P8 / P: the auxiliary estimate** for the unchanged `actualCommonDeterminant`, with leading
constant `12325/168`. -/
theorem actualAuxiliaryEstimate : ActualAuxiliaryEstimate := by
  rw [actualAuxiliaryEstimate_iff]
  intro c ε hε
  obtain ⟨D₁, h₁⟩ := profileSum_asymptotic (ε := ε / 3) (by positivity)
  obtain ⟨D₂, h₂⟩ := theta_term_small (ε := ε / 3) (by positivity)
  obtain ⟨D₃, h₃⟩ := errE_small c (ε := ε / 3) (by positivity)
  refine ⟨max (max D₁ D₂) (max D₃ 2), fun d hd => ?_⟩
  have hd2 : 2 ≤ d := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hd)
  have hT := auxiliary_total_bound c d hd2
  have e1 := h₁ d (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hd))
  have e2 := h₂ d (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hd))
  have e3 := h₃ d (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hd))
  linarith

end Zeta7Auxiliary

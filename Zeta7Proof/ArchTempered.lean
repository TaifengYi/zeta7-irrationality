import Mathlib
import Zeta7Proof.CommonRationalGerms

/-! C1, analytic layer: complex power series that converge absolutely on every disc
`|q| ≤ r < 1`. The class is closed under the operations producing the actual q-pullbacks
(sums, products, `θ = q d/dq`, the ordinary primitive, scalar extension from `ℚ`), and each
member defines a holomorphic function on the open unit disc whose evaluation is additive and
multiplicative. No convergence statement is assumed. -/
noncomputable section
set_option autoImplicit false
namespace Zeta7Arch
open PowerSeries Filter Topology

/-- Absolute convergence of `Σ aₙ qⁿ` for every radius `0 ≤ r < 1`. -/
def Tempered (f : ℂ⟦X⟧) : Prop :=
  ∀ r : ℝ, 0 ≤ r → r < 1 → Summable (fun n => ‖coeff n f‖ * r ^ n)

/-- A rational series is tempered when its complex scalar extension is. -/
def RTempered (f : ℚ⟦X⟧) : Prop := Tempered (f.map (algebraMap ℚ ℂ))

theorem Tempered.of_le {f g : ℂ⟦X⟧} (hg : Tempered g)
    (h : ∀ n, ‖coeff n f‖ ≤ ‖coeff n g‖) : Tempered f := fun r hr0 hr1 =>
  (hg r hr0 hr1).of_nonneg_of_le (fun n => by positivity)
    (fun n => mul_le_mul_of_nonneg_right (h n) (pow_nonneg hr0 n))

theorem tempered_of_poly_bound {f : ℂ⟦X⟧} (B : ℝ) (k : ℕ)
    (h : ∀ n, ‖coeff n f‖ ≤ B * (n : ℝ) ^ k) : Tempered f := by
  intro r hr0 hr1
  have hs : Summable (fun n : ℕ => (n : ℝ) ^ k * r ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one k (by rw [Real.norm_eq_abs, abs_of_nonneg hr0]; exact hr1)
  refine (hs.mul_left B).of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
  calc ‖coeff n f‖ * r ^ n ≤ B * (n : ℝ) ^ k * r ^ n :=
        mul_le_mul_of_nonneg_right (h n) (pow_nonneg hr0 n)
    _ = B * ((n : ℝ) ^ k * r ^ n) := by ring

theorem succ_pow_le (n k : ℕ) : ((n : ℝ) + 1) ^ k ≤ 2 ^ k * (n : ℝ) ^ k + 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have : ((n : ℝ) + 1) ^ k ≤ (2 * n) ^ k := pow_le_pow_left₀ (by positivity) (by linarith) k
    rw [mul_pow] at this
    linarith

theorem tempered_of_bound_succ {f : ℂ⟦X⟧} (B : ℝ) (k : ℕ)
    (h : ∀ n, ‖coeff n f‖ ≤ B * ((n : ℝ) + 1) ^ k) : Tempered f := by
  intro r hr0 hr1
  have hB : 0 ≤ B := le_trans (norm_nonneg _) ((h 0).trans (by simp))
  have hs : Summable (fun n : ℕ => (n : ℝ) ^ k * r ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one k (by rw [Real.norm_eq_abs, abs_of_nonneg hr0]; exact hr1)
  have hg : Summable (fun n : ℕ => r ^ n) := summable_geometric_of_lt_one hr0 hr1
  refine ((hs.mul_left (B * 2 ^ k)).add (hg.mul_left B)).of_nonneg_of_le
    (fun n => by positivity) (fun n => ?_)
  have := succ_pow_le n k
  calc ‖coeff n f‖ * r ^ n ≤ B * ((n : ℝ) + 1) ^ k * r ^ n :=
        mul_le_mul_of_nonneg_right (h n) (pow_nonneg hr0 n)
    _ ≤ B * (2 ^ k * (n : ℝ) ^ k + 1) * r ^ n := by gcongr
    _ = B * 2 ^ k * ((n : ℝ) ^ k * r ^ n) + B * r ^ n := by ring

theorem Tempered.add {f g : ℂ⟦X⟧} (hf : Tempered f) (hg : Tempered g) : Tempered (f + g) := by
  intro r hr0 hr1
  refine ((hf r hr0 hr1).add (hg r hr0 hr1)).of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
  rw [map_add, ← add_mul]
  exact mul_le_mul_of_nonneg_right (norm_add_le _ _) (pow_nonneg hr0 n)

theorem Tempered.neg {f : ℂ⟦X⟧} (hf : Tempered f) : Tempered (-f) :=
  hf.of_le fun n => by simp

theorem Tempered.sub {f g : ℂ⟦X⟧} (hf : Tempered f) (hg : Tempered g) : Tempered (f - g) := by
  rw [sub_eq_add_neg]; exact hf.add hg.neg

theorem tempered_C (a : ℂ) : Tempered (C a) :=
  tempered_of_poly_bound ‖a‖ 0 fun n => by
    rw [coeff_C]; split_ifs <;> simp

theorem tempered_zero : Tempered 0 := by simpa using tempered_C 0
theorem tempered_one : Tempered 1 := by simpa using tempered_C 1

theorem tempered_X_pow (k : ℕ) : Tempered (X ^ k) :=
  tempered_of_poly_bound 1 0 fun n => by
    rw [coeff_X_pow]; split_ifs <;> simp

theorem norm_coeff_mul_le (f g : ℂ⟦X⟧) (r : ℝ) (hr0 : 0 ≤ r) (n : ℕ) :
    ‖coeff n (f * g)‖ * r ^ n ≤ ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
      (‖coeff p.1 f‖ * r ^ p.1) * (‖coeff p.2 g‖ * r ^ p.2) := by
  rw [coeff_mul]
  refine (mul_le_mul_of_nonneg_right (norm_sum_le _ _) (pow_nonneg hr0 n)).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun p hp => ?_
  rw [norm_mul, ← (Finset.HasAntidiagonal.mem_antidiagonal.mp hp), pow_add]
  apply le_of_eq; ring

theorem Tempered.mul {f g : ℂ⟦X⟧} (hf : Tempered f) (hg : Tempered g) : Tempered (f * g) := by
  intro r hr0 hr1
  set a : ℕ → ℝ := fun n => ‖coeff n f‖ * r ^ n with ha
  set b : ℕ → ℝ := fun n => ‖coeff n g‖ * r ^ n with hb
  have ha0 : ∀ n, 0 ≤ a n := fun n => mul_nonneg (norm_nonneg _) (pow_nonneg hr0 n)
  have hb0 : ∀ n, 0 ≤ b n := fun n => mul_nonneg (norm_nonneg _) (pow_nonneg hr0 n)
  have hprod : Summable (fun x : ℕ × ℕ => a x.1 * b x.2) :=
    Summable.mul_of_nonneg (hf r hr0 hr1) (hg r hr0 hr1) ha0 hb0
  have hsum : Summable (fun n => ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, a p.1 * b p.2) :=
    summable_sum_mul_antidiagonal_of_summable_mul hprod
  exact hsum.of_nonneg_of_le (fun n => mul_nonneg (norm_nonneg _) (pow_nonneg hr0 n))
    (fun n => norm_coeff_mul_le f g r hr0 n)

theorem Tempered.pow {f : ℂ⟦X⟧} (hf : Tempered f) (k : ℕ) : Tempered (f ^ k) := by
  induction k with
  | zero => simpa using tempered_one
  | succ k ih => rw [pow_succ]; exact ih.mul hf

theorem Tempered.smul_C {f : ℂ⟦X⟧} (hf : Tempered f) (a : ℂ) : Tempered (C a * f) :=
  (tempered_C a).mul hf

/-- `n rⁿ ≤ Σ k (r/s)^k · sⁿ`-type domination used for `θ`. -/
theorem Tempered.euler {f : ℂ⟦X⟧} (hf : Tempered f) : Tempered (Zeta7Common.euler f) := by
  intro r hr0 hr1
  set s : ℝ := (1 + r) / 2 with hs
  have hs0 : 0 < s := by rw [hs]; linarith
  have hs1 : s < 1 := by rw [hs]; linarith
  have hrs : r ≤ s := by rw [hs]; linarith
  set t : ℝ := r / s with ht
  have ht0 : 0 ≤ t := div_nonneg hr0 hs0.le
  have ht1 : t < 1 := (div_lt_one hs0).mpr (by rw [hs]; linarith)
  have hT : Summable (fun n : ℕ => (n : ℝ) * t ^ n) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one 1
      (by rw [Real.norm_eq_abs, abs_of_nonneg ht0]; exact ht1 : ‖t‖ < 1)
  obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ n : ℕ, (n : ℝ) * t ^ n ≤ B :=
    ⟨∑' n : ℕ, (n : ℝ) * t ^ n, fun n => hT.le_tsum n (fun j _ => by positivity)⟩
  refine ((hf s hs0.le hs1).mul_left B).of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
  rw [Zeta7Common.euler_coeff, norm_mul, Complex.norm_natCast]
  have hrn : r ^ n = t ^ n * s ^ n := by
    rw [ht, div_pow, div_mul_cancel₀ _ (pow_ne_zero _ hs0.ne')]
  rw [hrn]
  calc (n : ℝ) * ‖coeff n f‖ * (t ^ n * s ^ n) = ((n : ℝ) * t ^ n) * (‖coeff n f‖ * s ^ n) := by ring
    _ ≤ B * (‖coeff n f‖ * s ^ n) :=
        mul_le_mul_of_nonneg_right (hB n) (by positivity)

theorem coeff_primitive {K : Type*} [Field K] (f : K⟦X⟧) (n : ℕ) :
    coeff n (Zeta7Common.primitive f) = if n = 0 then 0 else coeff (n - 1) f / (n : K) := by
  simp [Zeta7Common.primitive, coeff_mk]

theorem Tempered.primitive {f : ℂ⟦X⟧} (hf : Tempered f) :
    Tempered (Zeta7Common.primitive f) := by
  intro r hr0 hr1
  have hsh : Summable (fun n : ℕ => ‖coeff n f‖ * r ^ n * r) := (hf r hr0 hr1).mul_right r
  rw [← summable_nat_add_iff 1]
  refine hsh.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
  rw [coeff_primitive, if_neg (Nat.succ_ne_zero n : n + 1 ≠ 0), Nat.add_sub_cancel, norm_div,
    Complex.norm_natCast, pow_succ]
  have hn : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
  have : ‖coeff n f‖ / ((n + 1 : ℕ) : ℝ) ≤ ‖coeff n f‖ :=
    div_le_self (norm_nonneg _) hn
  calc ‖coeff n f‖ / ((n + 1 : ℕ) : ℝ) * (r ^ n * r) ≤ ‖coeff n f‖ * (r ^ n * r) :=
        mul_le_mul_of_nonneg_right this (by positivity)
    _ = ‖coeff n f‖ * r ^ n * r := by ring

/-! ### Rational series -/

theorem coeff_map_rat (f : ℚ⟦X⟧) (n : ℕ) :
    coeff n (f.map (algebraMap ℚ ℂ)) = ((coeff n f : ℚ) : ℂ) := by
  rw [coeff_map]; rfl

theorem RTempered.of_poly_bound {f : ℚ⟦X⟧} (B : ℝ) (k : ℕ)
    (h : ∀ n, |((coeff n f : ℚ) : ℝ)| ≤ B * (n : ℝ) ^ k) : RTempered f :=
  tempered_of_poly_bound B k fun n => by
    rw [coeff_map_rat, Complex.norm_ratCast]
    exact_mod_cast h n

theorem RTempered.add {f g : ℚ⟦X⟧} (hf : RTempered f) (hg : RTempered g) :
    RTempered (f + g) := by
  unfold RTempered at *; rw [map_add]; exact hf.add hg

theorem RTempered.sub {f g : ℚ⟦X⟧} (hf : RTempered f) (hg : RTempered g) :
    RTempered (f - g) := by
  unfold RTempered at *; rw [map_sub]; exact hf.sub hg

theorem RTempered.mul {f g : ℚ⟦X⟧} (hf : RTempered f) (hg : RTempered g) :
    RTempered (f * g) := by
  unfold RTempered at *; rw [map_mul]; exact hf.mul hg

theorem RTempered.pow {f : ℚ⟦X⟧} (hf : RTempered f) (k : ℕ) : RTempered (f ^ k) := by
  unfold RTempered at *; rw [map_pow]; exact hf.pow k

theorem rTempered_C (a : ℚ) : RTempered (C a) := by
  unfold RTempered; rw [map_C]; exact tempered_C _

theorem rTempered_X_pow (k : ℕ) : RTempered (X ^ k) := by
  unfold RTempered; rw [map_pow, map_X]; exact tempered_X_pow k

theorem RTempered.euler {f : ℚ⟦X⟧} (hf : RTempered f) : RTempered (Zeta7Common.euler f) := by
  unfold RTempered at *; rw [Zeta7Common.map_euler]; exact hf.euler

theorem RTempered.primitive {f : ℚ⟦X⟧} (hf : RTempered f) :
    RTempered (Zeta7Common.primitive f) := by
  unfold RTempered at *; rw [Zeta7Common.map_primitive]; exact hf.primitive

/-! ### Holomorphic realization on the unit disc -/

/-- The value `Σ aₙ qⁿ`. -/
def evalQ (f : ℂ⟦X⟧) (q : ℂ) : ℂ := ∑' n, coeff n f * q ^ n

/-- The associated one-variable formal multilinear series. -/
def fms (f : ℂ⟦X⟧) : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ (fun n => coeff n f)

theorem Tempered.summable_norm {f : ℂ⟦X⟧} (hf : Tempered f) {q : ℂ} (hq : ‖q‖ < 1) :
    Summable (fun n => ‖coeff n f * q ^ n‖) := by
  simpa [norm_mul, norm_pow] using hf ‖q‖ (norm_nonneg q) hq

theorem Tempered.one_le_radius {f : ℂ⟦X⟧} (hf : Tempered f) : 1 ≤ (fms f).radius := by
  refine ENNReal.le_of_forall_pos_nnreal_lt fun r _ hr => ?_
  have hr1 : (r : ℝ) < 1 := by exact_mod_cast hr
  refine (fms f).le_radius_of_summable ?_
  simpa [fms, FormalMultilinearSeries.ofScalars_norm] using hf r r.2 hr1

theorem evalQ_eq_sum (f : ℂ⟦X⟧) (q : ℂ) : evalQ f q = (fms f).sum q := by
  rw [fms, ← FormalMultilinearSeries.ofScalarsSum, FormalMultilinearSeries.ofScalars_sum_eq]
  simp [evalQ, smul_eq_mul, mul_comm]

theorem Tempered.hasFPowerSeriesOnBall {f : ℂ⟦X⟧} (hf : Tempered f) :
    HasFPowerSeriesOnBall (evalQ f) (fms f) 0 1 := by
  have hpos : 0 < (fms f).radius := lt_of_lt_of_le zero_lt_one hf.one_le_radius
  have h := (fms f).hasFPowerSeriesOnBall hpos
  have h' := h.mono one_pos hf.one_le_radius
  have he : evalQ f = (fms f).sum := funext fun q => evalQ_eq_sum f q
  rwa [he]

/-- **Holomorphy on the unit disc.** -/
theorem Tempered.analyticOnNhd {f : ℂ⟦X⟧} (hf : Tempered f) :
    AnalyticOnNhd ℂ (evalQ f) (Metric.ball 0 1) := by
  intro q hq
  have h := hf.hasFPowerSeriesOnBall
  have hq' : q ∈ Metric.eball (0 : ℂ) 1 := by
    rw [Metric.mem_eball, edist_dist, ENNReal.ofReal_lt_one]
    simpa using hq
  exact h.analyticAt_of_mem hq'

theorem Tempered.differentiableOn {f : ℂ⟦X⟧} (hf : Tempered f) :
    DifferentiableOn ℂ (evalQ f) (Metric.ball 0 1) :=
  hf.analyticOnNhd.differentiableOn

theorem evalQ_add {f g : ℂ⟦X⟧} (hf : Tempered f) (hg : Tempered g) {q : ℂ} (hq : ‖q‖ < 1) :
    evalQ (f + g) q = evalQ f q + evalQ g q := by
  simp only [evalQ, map_add, add_mul]
  exact (hf.summable_norm hq).of_norm.tsum_add (hg.summable_norm hq).of_norm

theorem evalQ_mul {f g : ℂ⟦X⟧} (hf : Tempered f) (hg : Tempered g) {q : ℂ} (hq : ‖q‖ < 1) :
    evalQ (f * g) q = evalQ f q * evalQ g q := by
  rw [evalQ, evalQ, evalQ,
    tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm (hf.summable_norm hq)
      (hg.summable_norm hq)]
  refine tsum_congr fun n => ?_
  rw [coeff_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [← (Finset.HasAntidiagonal.mem_antidiagonal.mp hp), pow_add]; ring

theorem evalQ_C (a : ℂ) (q : ℂ) : evalQ (C a) q = a := by
  rw [evalQ, tsum_eq_single 0 (fun n hn => by simp [coeff_C, hn])]
  simp

theorem evalQ_X_pow (k : ℕ) (q : ℂ) : evalQ (X ^ k) q = q ^ k := by
  rw [evalQ, tsum_eq_single k (fun n hn => by simp [coeff_X_pow, hn])]
  simp

theorem evalQ_zero_point (f : ℂ⟦X⟧) : evalQ f 0 = constantCoeff f := by
  rw [evalQ, tsum_eq_single 0 (fun n hn => by simp [zero_pow hn])]
  simp

end Zeta7Arch

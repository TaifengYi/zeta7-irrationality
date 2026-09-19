import Zeta7Proof.ArchTempered
import Zeta7Proof.AuxiliaryFourthLayerK
import Zeta7Proof.ActualAEisenstein

/-! C1: the actual seven germs pulled back to the modular disc, and their pole-clearing factor.

For the unchanged rational germs `g_j = rationalGerms c j`, `pulledGerm c j = g_j(x(q))` is the
formal substitution of the actual coordinate `x(q) = q ∏_{7∤m}(1-q^m)^{-4}`. We prove, from the
existing structural identities only:

* `g_0(x(q)) = A(G + c)`, `A·g_1(x) = θ g_0(x)`, `A·g_2(x) = θ g_1(x)`, `g_3(x) = (G+c)θ²G - ½(θG)²`,
  `θ g_4(x) = A x g_3(x)`, `θ g_5(x) = A x g_4(x)` (zero constant terms);
* with the fixed clearing factor `a(q) = A(q)^3`, `a(0) = 1`, every `a·g_j(x(q))` is given by an
  explicit series without inverses;
* `A`, `G`, `x/q`, `x`, and all cleared pullbacks converge absolutely on every disc `|q| ≤ r < 1`,
  hence define holomorphic functions on the open unit disc (`Zeta7Arch.Tempered.analyticOnNhd`).

The factor `A³` is independent of `d`, holomorphic on the whole unit disc and equal to `1` at `0`;
it replaces the paper's polynomial clearing factor for the leading-coefficient argument, where only
these three properties are used. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
namespace Zeta7Arch
open PowerSeries Zeta7Main Zeta7Common Zeta7Auxiliary

/-! ### Coefficient bounds for the actual q-series -/

theorem sum_divisors_filter_le (n : ℕ) (P : ℕ → Prop) [DecidablePred P] (w : ℕ → ℚ)
    (hw : ∀ a ∈ n.divisors, |w a| ≤ n) :
    |∑ a ∈ n.divisors.filter P, w a| ≤ (n : ℚ) * n := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have h1 : ∑ a ∈ n.divisors.filter P, |w a| ≤ (n.divisors.filter P).card • (n : ℚ) :=
    Finset.sum_le_card_nsmul _ _ _ fun a ha => hw a (Finset.mem_filter.mp ha).1
  have h2 : ((n.divisors.filter P).card : ℚ) ≤ n := by
    exact_mod_cast (Finset.card_filter_le _ _).trans (Nat.card_divisors_le_self n)
  rw [nsmul_eq_mul] at h1
  nlinarith [Nat.cast_nonneg (α := ℚ) n]

theorem RTempered.of_bound_succ {f : ℚ⟦X⟧} (B : ℝ) (k : ℕ)
    (h : ∀ n, |((coeff n f : ℚ) : ℝ)| ≤ B * ((n : ℝ) + 1) ^ k) : RTempered f :=
  tempered_of_bound_succ B k fun n => by
    rw [coeff_map_rat, Complex.norm_ratCast]
    exact_mod_cast h n

theorem ASeries_coeff_abs (n : ℕ) : |coeff n ASeries| ≤ 5 * ((n : ℚ) + 1) ^ 2 := by
  rw [ASeries_coeff]
  have hs := sum_divisors_filter_le n (fun a => ¬ 7 ∣ a) (fun a => (a : ℚ)) (fun a ha => by
    rw [abs_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast Nat.divisor_le ha)
  have hn := Nat.cast_nonneg (α := ℚ) n
  split_ifs with h0
  · subst h0; simp
  · calc |0 + 4 * ∑ a ∈ n.divisors.filter (fun a => ¬ 7 ∣ a), (a : ℚ)|
          ≤ 4 * ((n : ℚ) * n) := by rw [zero_add, abs_mul]; norm_num; linarith
      _ ≤ 5 * ((n : ℚ) + 1) ^ 2 := by nlinarith

theorem ASeries_tempered : RTempered ASeries :=
  RTempered.of_bound_succ 5 2 fun n => by exact_mod_cast ASeries_coeff_abs n

theorem GSeries_coeff_abs (n : ℕ) : |coeff n GSeries| ≤ ((n : ℚ) + 1) ^ 2 := by
  rw [GSeries_coeff]
  have hs := sum_divisors_filter_le n (fun a => ¬ 7 ∣ a) (fun a => ((a : ℚ) ^ 3)⁻¹)
    (fun a ha => by
      have ha1 : 1 ≤ a := Nat.pos_of_mem_divisors ha
      have hn1 : 1 ≤ n := Nat.pos_of_ne_zero (Nat.mem_divisors.mp ha).2
      have h1 : (1 : ℚ) ≤ (a : ℚ) ^ 3 := one_le_pow₀ (by exact_mod_cast ha1)
      rw [abs_of_nonneg (by positivity)]
      calc ((a : ℚ) ^ 3)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1
        _ ≤ n := by exact_mod_cast hn1)
  have hn := Nat.cast_nonneg (α := ℚ) n
  nlinarith

theorem GSeries_tempered : RTempered GSeries :=
  RTempered.of_bound_succ 1 2 fun n => by simpa using (by exact_mod_cast GSeries_coeff_abs n :
    |((coeff n GSeries : ℚ) : ℝ)| ≤ ((n : ℝ) + 1) ^ 2)

/-! ### The coordinate `x(q)`: convergence from the logarithmic-derivative recursion -/

theorem sevenSigmaOne_zero : sevenSigmaOne 0 = 0 := by simp [sevenSigmaOne]

theorem sevenSigmaOne_nonneg (n : ℕ) : 0 ≤ sevenSigmaOne n :=
  Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _

theorem sevenSigmaOne_le (n : ℕ) : sevenSigmaOne n ≤ (n : ℚ) ^ 2 := by
  have h := sum_divisors_filter_le n (fun a => ¬ 7 ∣ a) (fun a => (a : ℚ)) (fun a ha => by
    rw [abs_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast Nat.divisor_le ha)
  rw [sq]
  exact (le_abs_self _).trans h

theorem coeff_four_mul (f : ℚ⟦X⟧) (n : ℕ) : coeff n ((4 : ℚ⟦X⟧) * f) = 4 * coeff n f := by
  rw [show (4 : ℚ⟦X⟧) = C (4 : ℚ) from (map_ofNat C 4).symm, coeff_C_mul]

/-- `n uₙ = 4 Σ_{i+j=n} uᵢ σ*(j)`. -/
theorem xUnit_recursion (n : ℕ) :
    (n : ℚ) * coeff n xUnit = 4 * ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
      coeff p.1 xUnit * sevenSigmaOne p.2 := by
  have h := congrArg (coeff n) xUnit_euler
  rw [euler_coeff, mul_assoc, coeff_four_mul, coeff_mul] at h
  rw [h]
  simp [sevenSigmaOneSeries, coeff_mk]

theorem xUnit_coeff_nonneg (n : ℕ) : 0 ≤ coeff n xUnit := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [coeff_zero_eq_constantCoeff, xUnit_constant]; norm_num
    · have hr := xUnit_recursion n
      have hsum : 0 ≤ ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, coeff p.1 xUnit * sevenSigmaOne p.2 := by
        refine Finset.sum_nonneg fun p hp => ?_
        have hpn := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
        rcases Nat.eq_zero_or_pos p.2 with h2 | h2
        · rw [h2, sevenSigmaOne_zero, mul_zero]
        · exact mul_nonneg (ih p.1 (by omega)) (sevenSigmaOne_nonneg _)
      have hnq : (0 : ℚ) < n := by exact_mod_cast hn
      by_contra hneg
      have hneg' := lt_of_not_ge hneg
      nlinarith

theorem sum_antidiagonal_le_mul (a b : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, 0 ≤ b n) (N : ℕ) :
    ∑ n ∈ Finset.range N, ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, a p.1 * b p.2 ≤
      (∑ i ∈ Finset.range N, a i) * (∑ j ∈ Finset.range N, b j) := by
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  rw [Finset.sum_comm' (t' := (Finset.range N ×ˢ Finset.range N).filter
      (fun p : ℕ × ℕ => p.1 + p.2 < N)) (s' := fun p => {p.1 + p.2})]
  · simp only [Finset.sum_singleton]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun p _ _ => mul_nonneg (ha _) (hb _))
  · intro n p
    simp only [Finset.mem_range, Finset.HasAntidiagonal.mem_antidiagonal, Finset.mem_singleton,
      Finset.mem_filter, Finset.mem_product]
    omega

theorem xUnit_summable (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun n => ((coeff n xUnit : ℚ) : ℝ) * r ^ n) := by
  set a : ℕ → ℝ := fun n => ((coeff n xUnit : ℚ) : ℝ) * r ^ n with ha
  set s : ℕ → ℝ := fun n => ((sevenSigmaOne n : ℚ) : ℝ) * r ^ n with hs
  have ha0 : ∀ n, 0 ≤ a n := fun n =>
    mul_nonneg (by exact_mod_cast xUnit_coeff_nonneg n) (pow_nonneg hr0 n)
  have hs0 : ∀ n, 0 ≤ s n := fun n =>
    mul_nonneg (by exact_mod_cast sevenSigmaOne_nonneg n) (pow_nonneg hr0 n)
  have hsum_s : Summable s := by
    have hp : Summable (fun n : ℕ => (n : ℝ) ^ 2 * r ^ n) :=
      summable_pow_mul_geometric_of_norm_lt_one 2
        (by rw [Real.norm_eq_abs, abs_of_nonneg hr0]; exact hr1)
    refine hp.of_nonneg_of_le hs0 fun n => ?_
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast sevenSigmaOne_le n) (pow_nonneg hr0 n)
  set T : ℝ := ∑' n, s n
  have hT0 : 0 ≤ T := tsum_nonneg hs0
  have hsT : ∀ N, ∑ j ∈ Finset.range N, s j ≤ T := fun N =>
    hsum_s.sum_le_tsum _ (fun j _ => hs0 j)
  set P : ℕ → ℝ := fun N => ∑ n ∈ Finset.range N, a n
  have hP0 : ∀ N, 0 ≤ P N := fun N => Finset.sum_nonneg fun n _ => ha0 n
  -- the weighted recursion
  have hrec : ∀ n : ℕ, (n : ℝ) * a n =
      4 * ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, a p.1 * s p.2 := by
    intro n
    have h := congrArg (fun x : ℚ => (x : ℝ) * r ^ n) (xUnit_recursion n)
    simp only [Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat, Rat.cast_sum] at h
    rw [ha]
    simp only
    rw [← mul_assoc, h, mul_assoc, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [← Finset.HasAntidiagonal.mem_antidiagonal.mp hp, pow_add]
    simp only [hs]
    ring
  have hweight : ∀ N, ∑ n ∈ Finset.range N, (n : ℝ) * a n ≤ 4 * T * P N := by
    intro N
    calc ∑ n ∈ Finset.range N, (n : ℝ) * a n
        = 4 * ∑ n ∈ Finset.range N, ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, a p.1 * s p.2 := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun n _ => hrec n
      _ ≤ 4 * (P N * ∑ j ∈ Finset.range N, s j) := by
          gcongr; exact sum_antidiagonal_le_mul a s ha0 hs0 N
      _ ≤ 4 * (P N * T) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hsT N) (hP0 N)) (by norm_num)
      _ = 4 * T * P N := by ring
  obtain ⟨M, hM⟩ := exists_nat_ge (8 * T + 1)
  have hMpos : (0 : ℝ) < M := by linarith
  have hmono : ∀ {N K : ℕ}, N ≤ K → P N ≤ P K := fun hNK =>
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hNK) (fun n _ _ => ha0 n)
  have hbound : ∀ N, P N ≤ 2 * P M := by
    intro N
    rcases le_or_gt N M with hNM | hMN
    · linarith [hmono hNM, hP0 M]
    · have hsplit := Finset.sum_range_add_sum_Ico (fun n => (n : ℝ) * a n) hMN.le
      have hsplitP := Finset.sum_range_add_sum_Ico a hMN.le
      have hlow : 0 ≤ ∑ n ∈ Finset.range M, (n : ℝ) * a n :=
        Finset.sum_nonneg fun n _ => mul_nonneg (Nat.cast_nonneg _) (ha0 n)
      have hhigh : (M : ℝ) * ∑ n ∈ Finset.Ico M N, a n ≤
          ∑ n ∈ Finset.Ico M N, (n : ℝ) * a n := by
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun n hn => ?_
        have : (M : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Ico.mp hn).1
        exact mul_le_mul_of_nonneg_right this (ha0 n)
      have hw := hweight N
      have hPN : P N = P M + ∑ n ∈ Finset.Ico M N, a n := hsplitP.symm
      have key : (M : ℝ) * (P N - P M) ≤ 4 * T * P N := by
        rw [hPN] at hw ⊢
        rw [add_sub_cancel_left]
        linarith
      nlinarith [hP0 N, hP0 M]
  exact summable_of_sum_range_le ha0 hbound

theorem xUnit_tempered : RTempered xUnit := by
  intro r hr0 hr1
  refine (xUnit_summable r hr0 hr1).congr fun n => ?_
  rw [coeff_map_rat, Complex.norm_ratCast, abs_of_nonneg (by exact_mod_cast xUnit_coeff_nonneg n)]

theorem xSeries_tempered : RTempered xSeries := by
  rw [xSeries, ← pow_one (X : ℚ⟦X⟧)]
  exact (rTempered_X_pow 1).mul xUnit_tempered

/-! ### Exact pullbacks of the seven germs -/

/-- `g_j(x(q))` for the unchanged rational germs. -/
def pulledGerm (c : ℚ) (j : Fin 6) : ℚ⟦X⟧ := (rationalGerms c j).subst xSeries

theorem constantCoeff_subst_x (f : ℚ⟦X⟧) :
    constantCoeff (f.subst xSeries) = constantCoeff f := by
  have h := constantCoeff_subst_eq_zero xSeries_constant (f - C (constantCoeff f)) (by simp)
  change constantCoeff ((f - C (constantCoeff f)).subst xSeries) = 0 at h
  have hs : (f - C (constantCoeff f)).subst xSeries = f.subst xSeries - C (constantCoeff f) := by
    rw [subst_sub x_hasSubst, subst_C]; rfl
  rw [hs, map_sub, constantCoeff_C] at h
  exact sub_eq_zero.mp h

theorem euler_primitive (f : ℚ⟦X⟧) : euler (Zeta7Common.primitive f) = X * f := by
  ext n
  rw [euler_coeff, coeff_primitive]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [if_neg (Nat.succ_ne_zero m), coeff_succ_X_mul, Nat.add_sub_cancel]
    field_simp

theorem constantCoeff_primitive (f : ℚ⟦X⟧) : constantCoeff (Zeta7Common.primitive f) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_primitive, if_pos rfl]

theorem rationalGerms_one (c : ℚ) : rationalGerms c 1 = euler (rationalGerms c 0) := rfl
theorem rationalGerms_two (c : ℚ) : rationalGerms c 2 = euler (rationalGerms c 1) := rfl
theorem rationalGerms_four (c : ℚ) :
    rationalGerms c 4 = Zeta7Common.primitive (rationalGerms c 3) := rfl
theorem rationalGerms_five (c : ℚ) :
    rationalGerms c 5 = Zeta7Common.primitive (rationalGerms c 4) := rfl

theorem pulledGerm_zero (c : ℚ) : pulledGerm c 0 = ASeries * (GSeries + C c) :=
  rationalH_subst_x c

theorem pulledGerm_one (c : ℚ) : ASeries * pulledGerm c 1 = euler (pulledGerm c 0) := by
  rw [pulledGerm, pulledGerm, rationalGerms_one, euler_subst_x]

theorem pulledGerm_two (c : ℚ) : ASeries * pulledGerm c 2 = euler (pulledGerm c 1) := by
  rw [pulledGerm, pulledGerm, rationalGerms_two, euler_subst_x]

theorem pulledGerm_three (c : ℚ) : pulledGerm c 3 = lambertQuadratic c := by
  have h := congrArg (fun f : ℚ⟦X⟧ => f.subst xSeries) (rationalK_eq_subst c)
  rw [subst_comp_subst_apply q_hasSubst x_hasSubst, q_subst_x, X_subst] at h
  exact h

theorem euler_pulled_primitive (f : ℚ⟦X⟧) :
    euler ((Zeta7Common.primitive f).subst xSeries) = ASeries * xSeries * f.subst xSeries := by
  rw [euler_subst_x, euler_primitive, subst_mul x_hasSubst, subst_X x_hasSubst]
  ring

theorem pulledGerm_four (c : ℚ) :
    euler (pulledGerm c 4) = ASeries * xSeries * pulledGerm c 3 ∧
      constantCoeff (pulledGerm c 4) = 0 := by
  refine ⟨?_, ?_⟩
  · rw [pulledGerm, pulledGerm, rationalGerms_four, euler_pulled_primitive]
  · rw [pulledGerm, constantCoeff_subst_x, rationalGerms_four, constantCoeff_primitive]

theorem pulledGerm_five (c : ℚ) :
    euler (pulledGerm c 5) = ASeries * xSeries * pulledGerm c 4 ∧
      constantCoeff (pulledGerm c 5) = 0 := by
  refine ⟨?_, ?_⟩
  · rw [pulledGerm, pulledGerm, rationalGerms_five, euler_pulled_primitive]
  · rw [pulledGerm, constantCoeff_subst_x, rationalGerms_five, constantCoeff_primitive]

/-- A series with zero constant term is dominated coefficientwise by its `θ`-derivative. -/
theorem RTempered.of_euler {f g : ℚ⟦X⟧} (hg : RTempered g) (he : Zeta7Common.euler f = g)
    (h0 : constantCoeff f = 0) : RTempered f := by
  refine Tempered.of_le hg fun n => ?_
  rw [coeff_map_rat, coeff_map_rat, Complex.norm_ratCast, Complex.norm_ratCast, ← he,
    euler_coeff]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [coeff_zero_eq_constantCoeff_apply, h0]; simp
  · have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    push_cast
    rw [abs_mul, Nat.abs_cast]
    nlinarith [abs_nonneg ((coeff n f : ℚ) : ℝ)]

theorem lambertQuadratic_tempered (c : ℚ) : RTempered (lambertQuadratic c) := by
  unfold lambertQuadratic
  have hG := GSeries_tempered
  exact ((hG.add (rTempered_C c)).mul hG.euler.euler).sub
    ((rTempered_C _).mul (hG.euler.pow 2))

theorem pulledGerm_zero_tempered (c : ℚ) : RTempered (pulledGerm c 0) := by
  rw [pulledGerm_zero]; exact ASeries_tempered.mul (GSeries_tempered.add (rTempered_C c))

theorem pulledGerm_three_tempered (c : ℚ) : RTempered (pulledGerm c 3) := by
  rw [pulledGerm_three]; exact lambertQuadratic_tempered c

theorem pulledGerm_four_tempered (c : ℚ) : RTempered (pulledGerm c 4) :=
  RTempered.of_euler ((ASeries_tempered.mul xSeries_tempered).mul (pulledGerm_three_tempered c))
    (pulledGerm_four c).1 (pulledGerm_four c).2

theorem pulledGerm_five_tempered (c : ℚ) : RTempered (pulledGerm c 5) :=
  RTempered.of_euler ((ASeries_tempered.mul xSeries_tempered).mul (pulledGerm_four_tempered c))
    (pulledGerm_five c).1 (pulledGerm_five c).2

/-! ### The pole-clearing factor -/

/-- The fixed clearing factor `a(q) = A(q)^3`. -/
def clearingFactor : ℚ⟦X⟧ := ASeries ^ 3

theorem clearingFactor_constant : constantCoeff clearingFactor = 1 := by
  simp [clearingFactor, ASeries_constant]

theorem clearingFactor_tempered : RTempered clearingFactor := ASeries_tempered.pow 3

/-- The pole-cleared pullbacks, written without any inverse. -/
def clearedGerm (c : ℚ) : Fin 6 → ℚ⟦X⟧ :=
  ![ASeries ^ 3 * pulledGerm c 0,
    ASeries ^ 2 * euler (pulledGerm c 0),
    ASeries * euler (euler (pulledGerm c 0)) - euler ASeries * euler (pulledGerm c 0),
    ASeries ^ 3 * pulledGerm c 3,
    ASeries ^ 3 * pulledGerm c 4,
    ASeries ^ 3 * pulledGerm c 5]

/-- **Pole clearing.** `a(q) g_j(x(q))` is the explicit inverse-free series. -/
theorem clearing_identity (c : ℚ) (j : Fin 6) :
    clearingFactor * pulledGerm c j = clearedGerm c j := by
  have h1 := pulledGerm_one c
  have h2 := pulledGerm_two c
  fin_cases j
  · simp [clearingFactor, clearedGerm]
  · change ASeries ^ 3 * pulledGerm c 1 = ASeries ^ 2 * euler (pulledGerm c 0)
    rw [← h1]; ring
  · change ASeries ^ 3 * pulledGerm c 2 =
      ASeries * euler (euler (pulledGerm c 0)) - euler ASeries * euler (pulledGerm c 0)
    have h1' := congrArg euler h1
    rw [euler_mul] at h1'
    linear_combination ASeries ^ 2 * h2 + ASeries * h1' - euler ASeries * h1 -
      ASeries * ASeries * h2 + ASeries * (ASeries * h2)
  · simp [clearingFactor, clearedGerm]
  · simp [clearingFactor, clearedGerm]
  · simp [clearingFactor, clearedGerm]

theorem clearedGerm_tempered (c : ℚ) (j : Fin 6) : RTempered (clearedGerm c j) := by
  have hA := ASeries_tempered
  have h0 := pulledGerm_zero_tempered c
  fin_cases j
  · exact (hA.pow 3).mul h0
  · exact (hA.pow 2).mul h0.euler
  · exact (hA.mul h0.euler.euler).sub (hA.euler.mul h0.euler)
  · exact (hA.pow 3).mul (pulledGerm_three_tempered c)
  · exact (hA.pow 3).mul (pulledGerm_four_tempered c)
  · exact (hA.pow 3).mul (pulledGerm_five_tempered c)

/-! ### Leading coefficients survive the pullback and the clearing -/

theorem subst_x_leading (f : ℚ⟦X⟧) (n : ℕ) (hf : ∀ k < n, coeff k f = 0) :
    (∀ k < n, coeff k (clearingFactor * f.subst xSeries) = 0) ∧
      coeff n (clearingFactor * f.subst xSeries) = coeff n f := by
  obtain ⟨g, rfl⟩ : X ^ n ∣ f := X_pow_dvd_iff.mpr hf
  have hs : clearingFactor * (X ^ n * g).subst xSeries =
      X ^ n * (clearingFactor * xUnit ^ n * g.subst xSeries) := by
    rw [subst_mul x_hasSubst, subst_pow x_hasSubst, subst_X x_hasSubst, xSeries]
    ring
  rw [hs]
  refine ⟨fun k hk => ?_, ?_⟩
  · rw [coeff_X_pow_mul', if_neg (by omega)]
  · rw [coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self, coeff_zero_eq_constantCoeff_apply,
      map_mul, map_mul, map_pow, constantCoeff_subst_x, clearingFactor_constant, xUnit_constant,
      coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self, coeff_zero_eq_constantCoeff_apply]
    ring

/-! ### Holomorphic functions on the unit disc -/

/-- The complex embedding of a rational series, evaluated on the q-disc. -/
def qFun (f : ℚ⟦X⟧) (q : ℂ) : ℂ := evalQ (f.map (algebraMap ℚ ℂ)) q

theorem qFun_analytic {f : ℚ⟦X⟧} (hf : RTempered f) :
    AnalyticOnNhd ℂ (qFun f) (Metric.ball 0 1) :=
  Tempered.analyticOnNhd hf

/-- **C1 endpoint.** The coordinate, the clearing factor and all six pole-cleared pullbacks of
the actual germs are holomorphic on `|q| < 1`; the clearing factor is `1` at `q = 0`. -/
theorem cleared_germs_holomorphic (c : ℚ) :
    AnalyticOnNhd ℂ (qFun xSeries) (Metric.ball 0 1) ∧
      AnalyticOnNhd ℂ (qFun clearingFactor) (Metric.ball 0 1) ∧
      qFun clearingFactor 0 = 1 ∧
      ∀ j, AnalyticOnNhd ℂ (qFun (clearedGerm c j)) (Metric.ball 0 1) := by
  refine ⟨qFun_analytic xSeries_tempered, qFun_analytic clearingFactor_tempered, ?_,
    fun j => qFun_analytic (clearedGerm_tempered c j)⟩
  rw [qFun, evalQ_zero_point, ← coeff_zero_eq_constantCoeff_apply, coeff_map_rat,
    coeff_zero_eq_constantCoeff_apply, clearingFactor_constant]
  simp

end Zeta7Arch

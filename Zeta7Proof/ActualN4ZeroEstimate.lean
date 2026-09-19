import Zeta7Proof.N4ActualPolynomialDeterminant

/-! The uniform zero estimate for the original seven rational blocks. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
open scoped RatFunc LaurentSeries
namespace Zeta7Germ

theorem lowerBound_laurent_iterate {f : ℂ⸨X⸩} {N : ℤ} (h : lowerBound f N) (k : ℕ) :
    lowerBound (laurentD^[k] f) N := by
  induction k with
  | zero => exact h
  | succ k ih => rw [Function.iterate_succ_apply']; exact lowerBound_euler ih

theorem clearedIterate_evaluation_lowerBound (c : ℚ) (z : SevenCoordinates) (N : ℤ)
    (hz : lowerBound (sevenEval c z) N) (k : ℕ) :
    lowerBound (sevenEval c (clearedIterate z k)) N := by
  rw [clearedIterate, sevenEval_smul, sevenEval_iterate]
  have hp := polynomialLaurent_regular (polynomialP ^ (3 * k))
  have he : polynomialLaurent (polynomialP ^ (3 * k)) = embed (P ^ (3 * k)) := by
    rw [map_pow]
    change embed (polynomialP : RatFunc ℂ) ^ (3 * k) = _
    rw [polynomialP_cast, map_pow]
  rw [he] at hp
  simpa only [zero_add] using lowerBound_mul hp (lowerBound_laurent_iterate hz k)

theorem complexSeries_lowerBound_of_coeff_zero (f : PowerSeries ℚ) (N : ℕ)
    (hf : ∀ n < N, PowerSeries.coeff n f = 0) : lowerBound (complexSeries f) N := by
  intro k hk
  by_cases hneg : k < 0
  · simp [complexSeries, PowerSeries.coeff_coe, hneg]
  · have hnonneg : 0 ≤ k := by omega
    lift k to ℕ using hnonneg with n
    have hn : n < N := by exact_mod_cast hk
    simp [complexSeries, PowerSeries.coeff_coe, show ¬(n : ℤ) < 0 by omega, hf n hn]

theorem actual_block_zero_estimate (c : ℚ) (d : ℕ)
    (b : Zeta7Common.BlockIndex d → ℚ) (hb : b ≠ 0) :
    ∃ n : ℕ, n ≤ 7 * d + 175 ∧
      PowerSeries.coeff n
        (∑ i, b i • Zeta7Common.blockSeries d (Zeta7Common.rationalGerms c) i) ≠ 0 := by
  classical
  by_contra h
  push_neg at h
  let F := ∑ i, b i • Zeta7Common.blockSeries d (Zeta7Common.rationalGerms c) i
  let z := actualBlockCoordinates d b
  have hF : lowerBound (complexSeries F) ((7 * d + 176 : ℕ) : ℤ) :=
    complexSeries_lowerBound_of_coeff_zero F _ (fun n hn => h n (by omega))
  have hz : lowerBound (sevenEval c z) ((7 * d + 176 : ℕ) : ℤ) := by
    rwa [actualBlockCoordinates_eval]
  by_cases hn : z.1.2 ≠ 0 ∨ z.2 ≠ 0
  · obtain ⟨r, hr, a, q, hdet, hdeg, heval⟩ := actual_source_polynomial_determinant c d b hn
    have ho := polynomial_det_order_comparison (adaptedMatrix a q) hdet (adaptedGerms c a)
      (.inl 0) (adaptedGerms_constant c a) ((7 * d + 176 : ℕ) : ℤ)
      (fun i => by rw [heval i]; exact clearedIterate_evaluation_lowerBound c z _ hz _)
    omega
  · have hv : z.1.2 = 0 := not_not.mp (not_or.mp hn).1
    have hw : z.2 = 0 := not_not.mp (not_or.mp hn).2
    let p := actualPolynomialCoordinates d b
    have hc : (p.1.1 : RatFunc ℂ) = z.1.1 :=
      congrArg (fun z : SevenCoordinates => z.1.1) (actualPolynomialCoordinates_cast d b)
    have hp : p.1.1 ≠ 0 := by
      intro he
      have hr : z.1.1 = 0 := by rw [← hc, he]; simp
      exact actualBlockCoordinates_ne_zero c d b hb (Prod.ext (Prod.ext hr hv) hw)
    have he : sevenEval c z = polynomialLaurent p.1.1 := by
      simp only [sevenEval, fourEval, hv, hw]
      simp only [jetEval, primitiveEval, Pi.zero_apply, map_zero, zero_mul, add_zero]
      exact congrArg embed hc.symm
    rw [he] at hz
    have ho := polynomial_lowerBound_le_degree p.1.1 hp _ hz
    have hd := (actualPolynomialCoordinates_degree d b).1
    change p.1.1.natDegree ≤ d + 1 at hd
    omega

theorem actual_block_order_le (c : ℚ) (d : ℕ)
    (b : Zeta7Common.BlockIndex d → ℚ)
    (hF : (∑ i, b i • Zeta7Common.blockSeries d (Zeta7Common.rationalGerms c) i) ≠ 0) :
    PowerSeries.order (∑ i, b i • Zeta7Common.blockSeries d (Zeta7Common.rationalGerms c) i) ≤
      ((7 * d + 175 : ℕ) : ℕ∞) := by
  have hb : b ≠ 0 := by intro h; apply hF; simp [h]
  obtain ⟨n, hn, hc⟩ := actual_block_zero_estimate c d b hb
  exact (PowerSeries.order_le n hc).trans (by exact_mod_cast hn)

end Zeta7Germ

namespace Zeta7Common

theorem coefficientPolynomial_of_degree_lt (d : ℕ) (p : Polynomial ℚ)
    (hp : p.degree < (d : WithBot ℕ)) :
    coefficientPolynomial d (fun k => p.coeff k.val) = p := by
  classical
  ext n
  by_cases hn : n < d
  · exact coefficientPolynomial_coeff d (fun k => p.coeff k.val) ⟨n, hn⟩
  · have hk : ∀ k : Fin d, k.val ≠ n := fun k => by have := k.isLt; omega
    have hz : p.coeff n = 0 := Polynomial.coeff_eq_zero_of_degree_lt
      (hp.trans_le (by exact_mod_cast Nat.le_of_not_gt hn))
    simp [coefficientPolynomial, Polynomial.coeff_monomial, hk, hz]

/-- N4 in polynomial language. `degree`, including its bottom value, handles zero polynomials
and d=0 without a false positive-degree convention. -/
theorem actual_polynomial_zero_estimate (c : ℚ) (d : ℕ)
    (p : Unit ⊕ Fin 6 → Polynomial ℚ)
    (hp : ∀ i, (p i).degree < (d : WithBot ℕ))
    (hF : (∑ i, p i • sevenGerms (rationalGerms c) i) ≠ 0) :
    PowerSeries.order (∑ i, p i • sevenGerms (rationalGerms c) i) ≤
      ((7 * d + 175 : ℕ) : ℕ∞) := by
  let b : BlockIndex d → ℚ :=
    Sum.elim (fun k => (p (.inl ())).coeff k.val)
      (fun jk => (p (.inr jk.1)).coeff jk.2.val)
  have he : blockPolynomial d b = p := by
    funext i
    cases i with
    | inl u =>
        cases u
        exact coefficientPolynomial_of_degree_lt d (p (.inl ())) (hp (.inl ()))
    | inr j =>
        change coefficientPolynomial d (fun k => (p (.inr j)).coeff k.val) = p (.inr j)
        exact coefficientPolynomial_of_degree_lt d (p (.inr j)) (hp (.inr j))
  have hrel := blockPolynomial_relation d (rationalGerms c) b
  rw [he] at hrel
  rw [hrel] at hF ⊢
  exact Zeta7Germ.actual_block_order_le c d b hF

end Zeta7Common

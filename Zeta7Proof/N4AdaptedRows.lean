import Zeta7Proof.N4AdaptedFrame
import Zeta7Proof.N4ClearingRecurrence

/-! The polynomial derivative rows in the adapted cyclic frame. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
open scoped RatFunc
open Polynomial
namespace Zeta7Germ

def adaptedConnection {r : ℕ} (a : Fin r → Fin 3 → ℂ)
    (v : AdaptedIndex r → RatFunc ℂ) : AdaptedIndex r → RatFunc ℂ :=
  Sum.elim ![rationalD (v (.inl 0)) + v (.inl 3) * R,
    rationalD (v (.inl 1)) + rationalD V / 2 * v (.inl 3) +
      ∑ j, v (.inr j) * (primitiveMultiplier (fun i => RatFunc.C (a j i)) * R),
    rationalD (v (.inl 2)) + v (.inl 1) + V * v (.inl 3),
    rationalD (v (.inl 3)) + v (.inl 2)]
    (fun j => rationalD (v (.inr j)))

theorem adaptedMap_connection {r : ℕ} (a : Fin r → Fin 3 → ℂ)
    (v : AdaptedIndex r → RatFunc ℂ) :
    adaptedMap a (adaptedConnection a v) = connection7 (adaptedMap a v) := by
  have hp : primitiveMultiplier (∑ j, v (.inr j) • (fun i => RatFunc.C (a j i))) =
      ∑ j, v (.inr j) * primitiveMultiplier (fun i => RatFunc.C (a j i)) := by
    simp only [primitiveMultiplier, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Finset.mul_sum, Finset.sum_div]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  apply Prod.ext
  · apply Prod.ext
    · simp [adaptedMap, adaptedConnection, connection7, connection4, primitiveCoupling]
    · ext i
      fin_cases i
      · change rationalD (v (.inl 1)) + rationalD V / 2 * v (.inl 3) +
          (∑ j, v (.inr j) * (primitiveMultiplier (fun i => RatFunc.C (a j i)) * R)) =
          rationalD (v (.inl 1)) + rationalD V * v (.inl 3) / 2 +
            primitiveMultiplier (∑ j, v (.inr j) • (fun i => RatFunc.C (a j i))) * R
        rw [hp, Finset.sum_mul]
        simp only [mul_assoc]
        ring
      · simp [adaptedMap, adaptedConnection, connection7, connection4, connection3, primitiveCoupling]
        ring
      · simp [adaptedMap, adaptedConnection, connection7, connection4, connection3, primitiveCoupling]
        ring
  · ext i
    simp [adaptedMap, adaptedConnection, connection7, Derivation.leibniz,
      rationalD_constant, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring

def adaptedClearedPart {r : ℕ} (a : Fin r → Fin 3 → ℂ)
    (q : AdaptedIndex r → Polynomial ℂ) : AdaptedIndex r → Polynomial ℂ :=
  Sum.elim ![clearedR * q (.inl 3),
    clearedHalfDV * q (.inl 3) + ∑ j, clearedPrimitive (a j) * q (.inr j),
    polynomialP ^ 3 * q (.inl 1) + clearedV * q (.inl 3),
    polynomialP ^ 3 * q (.inl 2)] (fun _ => 0)

def adaptedClearedDerivative {r : ℕ} (a : Fin r → Fin 3 → ℂ)
    (q : AdaptedIndex r → Polynomial ℂ) : AdaptedIndex r → Polynomial ℂ :=
  fun i => polynomialP ^ 3 * polynomialD (q i) + adaptedClearedPart a q i

theorem adaptedClearedDerivative_cast {r : ℕ} (a : Fin r → Fin 3 → ℂ)
    (q : AdaptedIndex r → Polynomial ℂ) :
    (fun i => (adaptedClearedDerivative a q i : RatFunc ℂ)) =
      P ^ 3 • adaptedConnection a (fun i => (q i : RatFunc ℂ)) := by
  have hd (p : Polynomial ℂ) : (polynomialD p : RatFunc ℂ) = rationalD (p : RatFunc ℂ) :=
    (rationalD_polynomial p).symm
  ext i
  cases i with
  | inl i =>
      fin_cases i <;>
        simp [adaptedClearedDerivative, adaptedClearedPart, adaptedConnection,
          smul_eq_mul, RatFunc.coePolynomial_eq_algebraMap, Algebra.smul_def] <;>
        simp only [← RatFunc.coePolynomial_eq_algebraMap, polynomialP_cast,
          clearedR_cast, clearedV_cast, clearedHalfDV_cast, clearedPrimitive_cast, hd,
          Finset.mul_sum] <;> ring_nf <;> congr 1 <;>
        (try { simp only [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring })
  | inr j =>
      simp only [adaptedClearedDerivative, adaptedClearedPart, adaptedConnection,
        Sum.elim_inr, add_zero, Pi.smul_apply, smul_eq_mul,
        RatFunc.coePolynomial_eq_algebraMap, map_mul, map_pow]
      simp only [← RatFunc.coePolynomial_eq_algebraMap, polynomialP_cast, hd]

theorem adaptedClearedPart_degree {r M : ℕ} (a : Fin r → Fin 3 → ℂ)
    (q : AdaptedIndex r → Polynomial ℂ) (hq : ∀ i, (q i).natDegree ≤ M) :
    ∀ i, (adaptedClearedPart a q i).natDegree ≤ M + 8 := by
  have hm (p : Polynomial ℂ) (hp : p.natDegree ≤ 8) (i : AdaptedIndex r) :
      (p * q i).natDegree ≤ M + 8 := natDegree_mul_le.trans (by have := hq i; omega)
  intro i
  cases i with
  | inl i =>
      fin_cases i
      · exact hm _ (clearedR_degree.trans (by omega)) _
      · apply (natDegree_add_le _ _).trans
        apply max_le
        · exact hm _ (clearedHalfDV_degree.trans (by omega)) _
        · exact natDegree_sum_le_of_forall_le _ _ (fun j _ => hm _ (clearedPrimitive_degree _) _)
      · exact (natDegree_add_le _ _).trans (max_le
          (hm _ (polynomialP_cube_degree.trans (by omega)) _)
          (hm _ (clearedV_degree.trans (by omega)) _))
      · exact hm _ (polynomialP_cube_degree.trans (by omega)) _
  | inr j => simp [adaptedClearedPart]

def adaptedNextRow {r : ℕ} (a : Fin r → Fin 3 → ℂ) (k : ℕ)
    (q : AdaptedIndex r → Polynomial ℂ) : AdaptedIndex r → Polynomial ℂ :=
  fun i => adaptedClearedDerivative a q i - clearingCorrection k * q i

theorem adaptedNextRow_degree {r M : ℕ} (a : Fin r → Fin 3 → ℂ) (k : ℕ)
    (q : AdaptedIndex r → Polynomial ℂ) (hq : ∀ i, (q i).natDegree ≤ M) :
    ∀ i, (adaptedNextRow a k q i).natDegree ≤ M + 8 := by
  intro i
  apply (natDegree_sub_le _ _).trans
  apply max_le
  · apply (natDegree_add_le _ _).trans
    exact max_le ((clearing_derivative_degree _).trans (by have := hq i; omega))
      (adaptedClearedPart_degree a q hq i)
  · exact natDegree_mul_le.trans (by have := clearingCorrection_degree k; have := hq i; omega)

theorem adaptedNextRow_map {r : ℕ} (a : Fin r → Fin 3 → ℂ) (k : ℕ)
    (q : AdaptedIndex r → Polynomial ℂ) :
    adaptedMap a (fun i => (adaptedNextRow a k q i : RatFunc ℂ)) =
      P ^ 3 • connection7 (adaptedMap a (fun i => (q i : RatFunc ℂ))) -
        (clearingCorrection k : RatFunc ℂ) • adaptedMap a (fun i => (q i : RatFunc ℂ)) := by
  have he : (fun i => (adaptedNextRow a k q i : RatFunc ℂ)) =
      (fun i => (adaptedClearedDerivative a q i : RatFunc ℂ)) -
        (clearingCorrection k : RatFunc ℂ) • (fun i => (q i : RatFunc ℂ)) := by
    ext i
    simp [adaptedNextRow, smul_eq_mul, RatFunc.coePolynomial_eq_algebraMap, Algebra.smul_def]
  rw [he, map_sub, adaptedClearedDerivative_cast, map_smul, map_smul, adaptedMap_connection]

def adaptedRows {r : ℕ} (a : Fin r → Fin 3 → ℂ)
    (q : AdaptedIndex r → Polynomial ℂ) : ℕ → AdaptedIndex r → Polynomial ℂ
  | 0 => q
  | k + 1 => adaptedNextRow a k (adaptedRows a q k)

theorem adaptedRows_degree {r M : ℕ} (a : Fin r → Fin 3 → ℂ)
    (q : AdaptedIndex r → Polynomial ℂ) (hq : ∀ i, (q i).natDegree ≤ M) (k : ℕ) :
    ∀ i, (adaptedRows a q k i).natDegree ≤ M + 8 * k := by
  induction k with
  | zero => simpa [adaptedRows] using hq
  | succ k ih =>
      have h := adaptedNextRow_degree a k (adaptedRows a q k) ih
      simpa only [adaptedRows, Nat.mul_add, Nat.mul_one, Nat.add_assoc] using h

theorem adaptedRows_map {r : ℕ} (a : Fin r → Fin 3 → ℂ)
    (q : AdaptedIndex r → Polynomial ℂ) (k : ℕ) :
    adaptedMap a (fun i => (adaptedRows a q k i : RatFunc ℂ)) =
      clearedIterate (adaptedMap a (fun i => (q i : RatFunc ℂ))) k := by
  induction k with
  | zero => simp [adaptedRows, clearedIterate_zero]
  | succ k ih => rw [adaptedRows, adaptedNextRow_map, ih, clearedIterate_recurrence]

end Zeta7Germ

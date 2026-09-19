import Zeta7Proof.N4PolynomialDescent

/-! Polynomial lifts of the original source blocks, with their actual
ordinary-primitive change of coordinates and the d+1 degree bound. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
open scoped RatFunc
open Polynomial
namespace Zeta7Germ

abbrev PolynomialSevenCoordinates :=
  (Polynomial ℂ × (Fin 3 → Polynomial ℂ)) × (Fin 3 → Polynomial ℂ)

def polynomialSevenCast (q : PolynomialSevenCoordinates) : SevenCoordinates :=
  ((q.1.1, fun i => q.1.2 i), fun i => q.2 i)

def sevenDegreeLE (M : ℕ) (q : PolynomialSevenCoordinates) : Prop :=
  q.1.1.natDegree ≤ M ∧ (∀ i, (q.1.2 i).natDegree ≤ M) ∧
    (∀ i, (q.2 i).natDegree ≤ M)

theorem polynomialSevenCast_zero : polynomialSevenCast 0 = 0 := by
  ext i <;> simp [polynomialSevenCast]

theorem polynomialSevenCast_add (q s : PolynomialSevenCoordinates) :
    polynomialSevenCast (q + s) = polynomialSevenCast q + polynomialSevenCast s := by
  ext i <;> simp [polynomialSevenCast, RatFunc.coePolynomial_eq_algebraMap]

theorem polynomialSevenCast_smul (p : Polynomial ℂ) (q : PolynomialSevenCoordinates) :
    polynomialSevenCast (p • q) = (p : RatFunc ℂ) • polynomialSevenCast q := by
  ext i <;> simp [polynomialSevenCast, smul_eq_mul, RatFunc.coePolynomial_eq_algebraMap,
    Algebra.smul_def]

theorem polynomialSevenCast_sum {ι : Type*} (s : Finset ι) (q : ι → PolynomialSevenCoordinates) :
    polynomialSevenCast (∑ i ∈ s, q i) = ∑ i ∈ s, polynomialSevenCast (q i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [polynomialSevenCast_zero]
  | @insert i s hi ih => simp only [Finset.sum_insert hi, polynomialSevenCast_add, ih]

theorem sevenDegreeLE_mono {M N : ℕ} {q : PolynomialSevenCoordinates}
    (h : sevenDegreeLE M q) (hm : M ≤ N) : sevenDegreeLE N q :=
  ⟨h.1.trans hm, fun i => (h.2.1 i).trans hm, fun i => (h.2.2 i).trans hm⟩

theorem sevenDegreeLE_zero (M : ℕ) : sevenDegreeLE M 0 := by
  simp [sevenDegreeLE]

theorem sevenDegreeLE_add {M : ℕ} {q s : PolynomialSevenCoordinates}
    (hq : sevenDegreeLE M q) (hs : sevenDegreeLE M s) : sevenDegreeLE M (q + s) := by
  exact ⟨(natDegree_add_le _ _).trans (max_le hq.1 hs.1),
    fun i => (natDegree_add_le _ _).trans (max_le (hq.2.1 i) (hs.2.1 i)),
    fun i => (natDegree_add_le _ _).trans (max_le (hq.2.2 i) (hs.2.2 i))⟩

theorem sevenDegreeLE_smul {M N : ℕ} {q : PolynomialSevenCoordinates} (p : Polynomial ℂ)
    (hp : p.natDegree ≤ N) (hq : sevenDegreeLE M q) : sevenDegreeLE (N + M) (p • q) := by
  exact ⟨natDegree_mul_le.trans (add_le_add hp hq.1),
    fun i => natDegree_mul_le.trans (add_le_add hp (hq.2.1 i)),
    fun i => natDegree_mul_le.trans (add_le_add hp (hq.2.2 i))⟩

theorem sevenDegreeLE_sum {ι : Type*} (s : Finset ι) (q : ι → PolynomialSevenCoordinates)
    (M : ℕ) (hq : ∀ i ∈ s, sevenDegreeLE M (q i)) : sevenDegreeLE M (∑ i ∈ s, q i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using sevenDegreeLE_zero M
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact sevenDegreeLE_add (hq i (Finset.mem_insert_self _ _))
        (ih (fun j hj => hq j (Finset.mem_insert_of_mem hj)))

def originalPolynomialGermCoordinates : Fin 6 → PolynomialSevenCoordinates :=
  ![((0, ![1, 0, 0]), 0), ((0, ![0, 1, 0]), 0), ((0, ![0, 0, 1]), 0),
    (0, ![1, 0, 0]), (0, ![X, 1, 0]), (0, ![C (1 / 2) * X ^ 2, X, 1])]

theorem originalPolynomialGermCoordinates_cast (j : Fin 6) :
    polynomialSevenCast (originalPolynomialGermCoordinates j) = originalGermCoordinates j := by
  fin_cases j <;> ext i <;> (try fin_cases i) <;>
    simp [polynomialSevenCast, originalPolynomialGermCoordinates, originalGermCoordinates,
      RatFunc.coePolynomial_eq_algebraMap, map_div₀, map_ofNat] <;> ring

theorem originalPolynomialGermCoordinates_degree (j : Fin 6) :
    sevenDegreeLE 2 (originalPolynomialGermCoordinates j) := by
  fin_cases j <;>
    simp [sevenDegreeLE, originalPolynomialGermCoordinates, Fin.forall_fin_succ]

def polynomialBlockVector (d : ℕ) : Zeta7Common.BlockIndex d → PolynomialSevenCoordinates
  | .inl k => (X : Polynomial ℂ) ^ k.val • (((1, 0), 0) : PolynomialSevenCoordinates)
  | .inr jk => (X : Polynomial ℂ) ^ jk.2.val • originalPolynomialGermCoordinates jk.1

theorem polynomialBlockVector_cast (d : ℕ) (i : Zeta7Common.BlockIndex d) :
    polynomialSevenCast (polynomialBlockVector d i) = blockCoordinateVector d i := by
  cases i with
  | inl k =>
      simp [polynomialBlockVector, blockCoordinateVector, polynomialSevenCast_smul,
        polynomialSevenCast, RatFunc.coePolynomial_eq_algebraMap]
      rfl
  | inr jk =>
      simp [polynomialBlockVector, blockCoordinateVector, polynomialSevenCast_smul,
        originalPolynomialGermCoordinates_cast, RatFunc.coePolynomial_eq_algebraMap]

theorem polynomialBlockVector_degree (d : ℕ) (i : Zeta7Common.BlockIndex d) :
    sevenDegreeLE (d + 1) (polynomialBlockVector d i) := by
  cases i with
  | inl k =>
      have h := sevenDegreeLE_smul (X ^ k.val : Polynomial ℂ) (by simp :
        (X ^ k.val : Polynomial ℂ).natDegree ≤ k.val)
        (show sevenDegreeLE 0 (((1, 0), 0) : PolynomialSevenCoordinates) by simp [sevenDegreeLE])
      exact sevenDegreeLE_mono h (by have := k.isLt; omega)
  | inr jk =>
      have h := sevenDegreeLE_smul (X ^ jk.2.val : Polynomial ℂ) (by simp :
        (X ^ jk.2.val : Polynomial ℂ).natDegree ≤ jk.2.val)
        (originalPolynomialGermCoordinates_degree jk.1)
      exact sevenDegreeLE_mono h (by have := jk.2.isLt; omega)

def actualPolynomialCoordinates (d : ℕ) (a : Zeta7Common.BlockIndex d → ℚ) :
    PolynomialSevenCoordinates := ∑ i, C (a i : ℂ) • polynomialBlockVector d i

theorem actualPolynomialCoordinates_cast (d : ℕ) (a : Zeta7Common.BlockIndex d → ℚ) :
    polynomialSevenCast (actualPolynomialCoordinates d a) = actualBlockCoordinates d a := by
  simp only [actualPolynomialCoordinates, actualBlockCoordinates, polynomialSevenCast_sum,
    polynomialSevenCast_smul, polynomialBlockVector_cast,
    RatFunc.coePolynomial_eq_algebraMap, RatFunc.algebraMap_C]

theorem actualPolynomialCoordinates_degree (d : ℕ) (a : Zeta7Common.BlockIndex d → ℚ) :
    sevenDegreeLE (d + 1) (actualPolynomialCoordinates d a) := by
  apply sevenDegreeLE_sum
  intro i _
  have h := sevenDegreeLE_smul (C (a i : ℂ)) (by simp : (C (a i : ℂ)).natDegree ≤ 0)
    (polynomialBlockVector_degree d i)
  simpa using h

end Zeta7Germ

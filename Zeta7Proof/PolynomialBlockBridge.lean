import Zeta7Proof.CommonJumpDeterminant

/-! The precise bridge from polynomial-coefficient independence of seven germs
to rational independence of every complete monomial block. Independence over
the constant field alone is not used as a substitute. -/
set_option autoImplicit false
noncomputable section
open PowerSeries
namespace Zeta7Common

def sevenGerms {K : Type*} [CommRing K] (g : Fin 6 → K⟦X⟧) : Unit ⊕ Fin 6 → K⟦X⟧ :=
  Sum.elim (fun _ => 1) g

def coefficientPolynomial (d : ℕ) (a : Fin d → ℚ) : Polynomial ℚ :=
  ∑ k : Fin d, Polynomial.monomial k.val (a k)

theorem coefficientPolynomial_coeff (d : ℕ) (a : Fin d → ℚ) (k : Fin d) :
    (coefficientPolynomial d a).coeff k.val = a k := by
  classical
  simp [coefficientPolynomial, Polynomial.coeff_monomial, Fin.val_inj]

theorem polynomial_smul_series {K : Type*} [CommRing K] (p : Polynomial K) (f : K⟦X⟧) :
    p • f = (p : K⟦X⟧) * f := by
  rw [Algebra.smul_def, PowerSeries.algebraMap_apply']
  simp

theorem coefficientPolynomial_smul (d : ℕ) (a : Fin d → ℚ) (f : ℚ⟦X⟧) :
    coefficientPolynomial d a • f = ∑ k : Fin d, a k • (X ^ k.val * f) := by
  classical
  rw [coefficientPolynomial, Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro k _
  rw [polynomial_smul_series, ← Polynomial.C_mul_X_pow_eq_monomial,
    Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_pow, Polynomial.coe_X]
  rw [smul_eq_C_mul]
  ring

def blockPolynomial (d : ℕ) (a : BlockIndex d → ℚ) : Unit ⊕ Fin 6 → Polynomial ℚ
  | .inl _ => coefficientPolynomial d (fun k => a (.inl k))
  | .inr j => coefficientPolynomial d (fun k => a (.inr (j, k)))

/-- Every finite block relation is exactly one polynomial relation in seven germs. -/
theorem blockPolynomial_relation (d : ℕ) (g : Fin 6 → ℚ⟦X⟧) (a : BlockIndex d → ℚ) :
    (∑ j : Unit ⊕ Fin 6, blockPolynomial d a j • sevenGerms g j) =
      ∑ j : BlockIndex d, a j • blockSeries d g j := by
  classical
  simp only [Fintype.sum_sum_type, Fintype.sum_unique, blockPolynomial, sevenGerms,
    Sum.elim_inl, Sum.elim_inr, coefficientPolynomial_smul, mul_one]
  rw [Fintype.sum_prod_type]
  rfl

/-- Polynomial-coefficient independence, not just constant-coefficient
independence, implies the exact block-family hypothesis used by N5. -/
theorem block_independent_of_polynomial_independent (g : Fin 6 → ℚ⟦X⟧)
    (h : LinearIndependent (Polynomial ℚ) (sevenGerms g)) (d : ℕ) :
    LinearIndependent ℚ (blockSeries d g) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro a ha j
  have hp := Fintype.linearIndependent_iff.mp h (blockPolynomial d a)
    ((blockPolynomial_relation d g a).trans ha)
  cases j with
  | inl k =>
    have hc := congrArg (fun p : Polynomial ℚ => p.coeff k.val) (hp (.inl ()))
    simpa only [blockPolynomial, coefficientPolynomial_coeff, Polynomial.coeff_zero] using hc
  | inr jk =>
    have hc := congrArg (fun p : Polynomial ℚ => p.coeff jk.2.val) (hp (.inr jk.1))
    simpa only [blockPolynomial, coefficientPolynomial_coeff, Polynomial.coeff_zero] using hc

/-- The resulting full-rank assertion uses the existing exact rational germs. -/
theorem actual_fullRank_of_polynomial_independent (c : ℚ)
    (h : LinearIndependent (Polynomial ℚ) (sevenGerms (rationalGerms c))) (d : ℕ) :
    Zeta7Jump.FullRank (coefficientRow d (rationalGerms c)) :=
  fullRank_of_block_independent d _ (block_independent_of_polynomial_independent _ h d)

/-- Scalar descent from polynomial independence over C to polynomial independence over Q. -/
theorem polynomial_independent_of_complex (g : Fin 6 → ℚ⟦X⟧)
    (h : LinearIndependent (Polynomial ℂ)
      (sevenGerms (fun j => (g j).map (algebraMap ℚ ℂ)))) :
    LinearIndependent (Polynomial ℚ) (sevenGerms g) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro p hp j
  have hmap : ∀ i : Unit ⊕ Fin 6,
      (p i • sevenGerms g i).map (algebraMap ℚ ℂ) =
      (p i).map (algebraMap ℚ ℂ) •
        sevenGerms (fun j => (g j).map (algebraMap ℚ ℂ)) i := by
    intro i
    simp only [polynomial_smul_series, map_mul, Polynomial.polynomial_map_coe]
    cases i <;> simp [sevenGerms]
  have heq := congrArg (PowerSeries.map (algebraMap ℚ ℂ)) hp
  rw [map_sum, map_zero] at heq
  simp only [hmap] at heq
  have hj := Fintype.linearIndependent_iff.mp h
    (fun i => (p i).map (algebraMap ℚ ℂ)) heq j
  ext n
  have hn := congrArg (fun f : Polynomial ℂ => f.coeff n) hj
  simpa using hn

/-- N3's polynomial consequence over C reaches exactly the common determinant's family. -/
theorem actual_block_independent_of_complex_polynomial (c : ℚ)
    (h : LinearIndependent (Polynomial ℂ)
      (sevenGerms (fun j => (rationalGerms c j).map (algebraMap ℚ ℂ)))) (d : ℕ) :
    LinearIndependent ℚ (blockSeries d (rationalGerms c)) :=
  block_independent_of_polynomial_independent _ (polynomial_independent_of_complex _ h) d

open scoped LaurentSeries RatFunc

/-- The actual seven complex germs in the standard Laurent-series field.
The rational-function scalar action is Mathlib's canonical one. -/
def complexLaurentGerms (c : ℚ) : Unit ⊕ Fin 6 → ℂ⸨X⸩ :=
  fun j => (sevenGerms (fun i => (rationalGerms c i).map (algebraMap ℚ ℂ)) j : ℂ⟦X⟧)

/-- The full scalar-extension/indexing bridge from exactly the C(x)-independence
assertion intended in N3. It does not prove that premise. -/
theorem actual_block_independent_of_ratFunc (c : ℚ)
    (h : LinearIndependent (RatFunc ℂ) (complexLaurentGerms c)) (d : ℕ) :
    LinearIndependent ℚ (blockSeries d (rationalGerms c)) := by
  apply actual_block_independent_of_complex_polynomial c _ d
  apply Fintype.linearIndependent_iff.mpr
  intro p hp j
  have hm : ∀ i : Unit ⊕ Fin 6,
      HahnSeries.ofPowerSeries ℤ ℂ
        (p i • sevenGerms (fun k => (rationalGerms c k).map (algebraMap ℚ ℂ)) i) =
      (p i : RatFunc ℂ) • complexLaurentGerms c i := by
    intro i
    rw [polynomial_smul_series, map_mul, Algebra.smul_def]
    change ((p i : ℂ⟦X⟧) : ℂ⸨X⸩) * _ =
      algebraMap (RatFunc ℂ) ℂ⸨X⸩ (p i : RatFunc ℂ) * _
    rw [RatFunc.coe_coe]
    rfl
  have heq := congrArg (HahnSeries.ofPowerSeries ℤ ℂ) hp
  rw [map_sum, map_zero] at heq
  simp only [hm] at heq
  have hj := Fintype.linearIndependent_iff.mp h (fun i => (p i : RatFunc ℂ)) heq j
  exact (IsFractionRing.injective (Polynomial ℂ) (RatFunc ℂ)) (hj.trans (map_zero _).symm)

/-- N3, once formalized for the actual Laurent germs, supplies the exact N5 input. -/
theorem actual_fullRank_of_ratFunc (c : ℚ)
    (h : LinearIndependent (RatFunc ℂ) (complexLaurentGerms c)) (d : ℕ) :
    Zeta7Jump.FullRank (coefficientRow d (rationalGerms c)) :=
  fullRank_of_block_independent d _ (actual_block_independent_of_ratFunc c h d)

end Zeta7Common

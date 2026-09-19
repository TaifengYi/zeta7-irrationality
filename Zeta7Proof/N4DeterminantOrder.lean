import Zeta7Proof.N4PolynomialDescent

/-! Polynomial determinant degree and the cofactor form of the N4 column
replacement argument. All comparisons concern complete Laurent series. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
open scoped RatFunc LaurentSeries
open Polynomial Matrix
namespace Zeta7Germ

abbrev polynomialLaurent : Polynomial ℂ →+* ℂ⸨X⸩ :=
  embed.comp (algebraMap (Polynomial ℂ) (RatFunc ℂ))

theorem polynomialLaurent_regular (p : Polynomial ℂ) : lowerBound (polynomialLaurent p) 0 := by
  change lowerBound (embed (p : RatFunc ℂ)) 0
  rw [embed_polynomial]
  exact lowerBound_powerSeries _

theorem polynomialLaurent_coeff (p : Polynomial ℂ) (n : ℕ) :
    (polynomialLaurent p).coeff (n : ℤ) = p.coeff n := by
  change (embed (p : RatFunc ℂ)).coeff (n : ℤ) = _
  rw [embed_polynomial]
  simp [PowerSeries.coeff_coe, show ¬(n : ℤ) < 0 by omega]

theorem polynomial_lowerBound_le_degree (p : Polynomial ℂ) (hp : p ≠ 0) (N : ℤ)
    (h : lowerBound (polynomialLaurent p) N) : N ≤ (p.natDegree : ℤ) := by
  by_contra hn
  have he := h p.natDegree (by omega)
  rw [polynomialLaurent_coeff] at he
  rw [coeff_natDegree] at he
  exact (leadingCoeff_ne_zero.mpr hp) he

theorem polynomial_det_degree {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : Matrix ι ι (Polynomial ℂ)) (b : ι → ℕ)
    (hQ : ∀ i j, (Q i j).natDegree ≤ b i) : Q.det.natDegree ≤ ∑ i, b i := by
  rw [Matrix.det_apply]
  apply natDegree_sum_le_of_forall_le
  intro s _
  calc
    (Equiv.Perm.sign s • ∏ i, Q (s i) i).natDegree ≤ (∏ i, Q (s i) i).natDegree := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign s) with h | h
      · rw [h, one_smul]
      · rw [h, Units.neg_smul, one_smul, natDegree_neg]
    _ ≤ ∑ i, (Q (s i) i).natDegree := natDegree_prod_le _ _
    _ ≤ ∑ i, b (s i) := Finset.sum_le_sum (fun i _ => hQ (s i) i)
    _ = ∑ i, b i := Equiv.sum_comp s b

/-- Cofactor expansion of the replaced column. The frame's constant component
is exactly one; no order estimate on unrelated auxiliary series is used. -/
theorem polynomial_det_lowerBound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : Matrix ι ι (Polynomial ℂ)) (g : ι → ℂ⸨X⸩) (j₀ : ι) (hg : g j₀ = 1)
    (N : ℤ) (hw : ∀ i, lowerBound (((Q.map polynomialLaurent) *ᵥ g) i) N) :
    lowerBound (polynomialLaurent Q.det) N := by
  let M := Q.map polynomialLaurent
  have he : (M.adjugate *ᵥ (M *ᵥ g)) j₀ = polynomialLaurent Q.det := by
    rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
    simp only [Pi.smul_apply, smul_eq_mul, hg, mul_one]
    exact (RingHom.map_det polynomialLaurent Q).symm
  rw [← he]
  change lowerBound (∑ i, M.adjugate j₀ i * (M *ᵥ g) i) N
  apply lowerBound_sum
  intro i _
  have hm : lowerBound (M.adjugate j₀ i) 0 := by
    have ha := RingHom.map_adjugate polynomialLaurent Q
    have hai := congrArg (fun A : Matrix ι ι ℂ⸨X⸩ => A j₀ i) ha
    change polynomialLaurent (Q.adjugate j₀ i) = M.adjugate j₀ i at hai
    rw [← hai]
    exact polynomialLaurent_regular _
  simpa only [zero_add] using lowerBound_mul hm (hw i)

theorem polynomial_det_order_comparison {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : Matrix ι ι (Polynomial ℂ)) (hQ : Q.det ≠ 0)
    (g : ι → ℂ⸨X⸩) (j₀ : ι) (hg : g j₀ = 1) (N : ℤ)
    (hw : ∀ i, lowerBound (((Q.map polynomialLaurent) *ᵥ g) i) N) :
    N ≤ (Q.det.natDegree : ℤ) :=
  polynomial_lowerBound_le_degree Q.det hQ N (polynomial_det_lowerBound Q g j₀ hg N hw)

end Zeta7Germ

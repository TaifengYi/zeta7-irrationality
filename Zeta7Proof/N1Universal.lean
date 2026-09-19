import Zeta7Proof.N1PolynomialReduction

/-! Universal N1 for the original rational potential and forcing. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open scoped RatFunc LaurentSeries
open Polynomial
namespace Zeta7Germ

theorem polynomial_solution_vanishes_at_root (p h : Polynomial ℂ)
    (he : L (p : RatFunc ℂ) = (h : RatFunc ℂ) * R)
    (a : ℂ) (ha : 1 + 13 * a + 49 * a ^ 2 = 0) : p.eval a = 0 := by
  have he' := congrArg (localExpansion a) he
  rw [localExpansion_L, map_mul] at he'
  have hc := congrArg (fun f : ℂ⸨X⸩ => f.coeff (-3)) he'
  have hl := localL_root_leading a (localExpansion_polynomial_lowerBound a p)
    (actual_V_root_lowerBound a ha) (actual_V_root_coeff a ha)
  have hb := lowerBound_mul (localExpansion_polynomial_lowerBound a h)
    (actual_R_root_lowerBound a ha)
  norm_num only [zero_sub, zero_add] at hl hb
  rw [hl, hb (-3) (by norm_num), localExpansion_polynomial_constant] at hc
  have hi : indicial (0 : ℂ) = -8 / 9 := by norm_num [indicial]
  rw [hi] at hc
  exact (mul_eq_zero.mp hc).resolve_left
    (mul_ne_zero (pow_ne_zero 3 (singular_root_algebra a ha).1) (by norm_num))

theorem polynomialP_two_roots : ∃ a b : ℂ, a ≠ b ∧
    1 + 13 * a + 49 * a ^ 2 = 0 ∧ 1 + 13 * b + 49 * b ^ 2 = 0 := by
  have hd : polynomialP.degree ≠ 0 := by
    intro hz
    have hn := natDegree_eq_of_degree_eq_some hz
    rw [polynomialP_degree] at hn
    norm_num at hn
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root polynomialP hd
  have hroot : 1 + 13 * a + 49 * a ^ 2 = 0 := by
    simpa [Polynomial.IsRoot, polynomialP] using ha
  refine ⟨a, -13 / 49 - a, ?_, hroot, ?_⟩
  · intro hab
    apply root_slope_ne_zero a hroot
    linear_combination 49 * hab
  · linear_combination hroot

theorem quadratic_vanishing_is_scalar_P (p : Polynomial ℂ) (hp : p.natDegree ≤ 2)
    (hroots : ∀ a : ℂ, 1 + 13 * a + 49 * a ^ 2 = 0 → p.eval a = 0) :
    ∃ c : ℂ, (p : RatFunc ℂ) = RatFunc.C c * P := by
  classical
  let c : ℂ := p.coeff 2 / 49
  let q : Polynomial ℂ := p - C c * polynomialP
  have hq : q.natDegree ≤ 1 := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro n hn
    by_cases hn2 : n = 2
    · subst n
      simp [q, c, polynomialP, coeff_mul, Finset.Nat.antidiagonal_succ,
        Finset.Nat.antidiagonal_zero, coeff_one, coeff_X]
    · have hn3 : 2 < n := by omega
      simp only [q, coeff_sub, coeff_C_mul,
        coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hp hn3),
        coeff_eq_zero_of_natDegree_lt (show polynomialP.natDegree < n by
          rw [polynomialP_degree]; exact hn3), mul_zero, sub_self]
  have hqroot (a : ℂ) (ha : 1 + 13 * a + 49 * a ^ 2 = 0) : q.eval a = 0 := by
    simp [q, hroots a ha, polynomialP, ha]
  obtain ⟨a, b, hab, ha, hb⟩ := polynomialP_two_roots
  have hqzero : q = 0 := by
    apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero' q {a, b}
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with hx | hx
      · subst x
        exact hqroot a ha
      · subst x
        exact hqroot b hb
    · simpa [hab] using lt_of_le_of_lt hq (by norm_num : 1 < 2)
  have he : p = C c * polynomialP := sub_eq_zero.mp hqzero
  refine ⟨c, ?_⟩
  rw [he]
  simp [RatFunc.coePolynomial_eq_algebraMap, ← polynomialP_cast]

theorem no_rational_inhomogeneous_solution (f : RatFunc ℂ) (h : Polynomial ℂ)
    (hh : h ≠ 0) (hdeg : h.natDegree ≤ 2) : L f ≠ (h : RatFunc ℂ) * R := by
  intro he
  obtain ⟨p, rfl⟩ := actual_L_solution_polynomial f h he
  have hp := polynomial_solution_degree_le_two p h hdeg he
  obtain ⟨c, hc⟩ := quadratic_vanishing_is_scalar_P p hp
    (polynomial_solution_vanishes_at_root p h he)
  rw [hc] at he
  exact no_scalar_P_solution c h hh he

end Zeta7Germ

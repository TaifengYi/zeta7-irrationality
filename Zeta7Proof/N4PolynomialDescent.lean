import Zeta7Proof.N4ActualBlockCoordinates
import Zeta7Proof.N4ClearedCoefficients

/-! Polynomial descent along a constant primitive frame. Taking a bounded
Laurent coefficient section proves polynomiality without rational denominators. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
open scoped RatFunc LaurentSeries
open Polynomial
namespace Zeta7Germ

def polynomialSection (M : ℕ) (f : ℂ⸨X⸩) : Polynomial ℂ :=
  PowerSeries.trunc (M + 1) (PowerSeries.mk fun n => f.coeff (n : ℤ))

theorem polynomialSection_coeff (M n : ℕ) (f : ℂ⸨X⸩) :
    (polynomialSection M f).coeff n = if n ≤ M then f.coeff (n : ℤ) else 0 := by
  simp [polynomialSection, PowerSeries.coeff_trunc, Nat.lt_succ_iff]

theorem polynomialSection_degree (M : ℕ) (f : ℂ⸨X⸩) :
    (polynomialSection M f).natDegree ≤ M := by
  exact Nat.le_of_lt_succ (PowerSeries.natDegree_trunc_lt _ M)

/-- A polynomial vector in a constant rational-function span has polynomial
coordinates with the same degree bound. This includes empty constant families. -/
theorem polynomial_coordinates_of_constant_span {r : ℕ}
    (a : Fin r → Fin 3 → ℂ) (w : Fin 3 → Polynomial ℂ) (M : ℕ)
    (hw : ∀ i, (w i).natDegree ≤ M)
    (hs : (fun i => (w i : RatFunc ℂ)) ∈
      Submodule.span (RatFunc ℂ) (Set.range (fun j i => RatFunc.C (a j i)))) :
    ∃ p : Fin r → Polynomial ℂ, (∀ j, (p j).natDegree ≤ M) ∧
      ∀ i, ∑ j, p j * C (a j i) = w i := by
  classical
  obtain ⟨b, hb⟩ := (Submodule.mem_span_range_iff_exists_fun (RatFunc ℂ)).mp hs
  let p := fun j => polynomialSection M (embed (b j))
  refine ⟨p, fun j => polynomialSection_degree M _, ?_⟩
  intro i
  ext n
  simp only [finset_sum_coeff, coeff_mul_C]
  by_cases hn : n ≤ M
  · have he := congrArg (fun v : Fin 3 → RatFunc ℂ => (embed (v i)).coeff (n : ℤ)) hb
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul,
      embed_C, HahnSeries.coeff_sum, HahnSeries.C_apply, HahnSeries.coeff_mul_single_zero,
      embed_polynomial, LaurentSeries.coeff_coe_powerSeries, PowerSeries.coeff_coe] at he
    rw [ite_eq_right (show ¬(n : ℤ) < 0 by omega)] at he
    simpa [p, polynomialSection_coeff, hn] using he
  · have hnw : (w i).natDegree < n := lt_of_le_of_lt (hw i) (by omega)
    simp [p, polynomialSection_coeff, hn, coeff_eq_zero_of_natDegree_lt hnw]

end Zeta7Germ

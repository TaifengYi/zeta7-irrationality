import Zeta7Proof.AnnularHypergeometricJets

/-! Denominator-cleared ordinary hypergeometric equations for the original
seven-adic Taylor series, with their analytic evaluations. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
open PowerSeries
namespace Zeta7Annulus
local instance AnnularOrdinaryEquations_local1 : Fact (Nat.Prime 7) := ⟨by decide⟩

theorem ordinary_equation_of_coeff_recurrence {K : Type*} [Field K]
    (f : K⟦X⟧) (a b c : K)
    (hrec : ∀ n : ℕ, ((n : K) + 1) * ((n : K) + c) * coeff (n + 1) f =
      ((n : K) + a) * ((n : K) + b) * coeff n f) :
    X * derivative K (derivative K f) + C c * derivative K f =
      X * (X * derivative K (derivative K f)) +
        C (a + b + 1) * (X * derivative K f) + C (a * b) * f := by
  ext n
  cases n with
  | zero =>
      simp only [map_add (coeff _), coeff_zero_X_mul, coeff_C_mul, coeff_derivative, zero_add]
      have h := hrec 0
      norm_num only [Nat.cast_zero, zero_add, mul_one, one_mul] at h ⊢
      linear_combination h
  | succ n =>
      cases n with
      | zero =>
          simp only [map_add (coeff _), coeff_succ_X_mul, coeff_zero_X_mul, coeff_C_mul,
            coeff_derivative, Nat.cast_zero, Nat.cast_one]
          have h := hrec 1
          norm_num only [Nat.cast_one] at h
          linear_combination h
      | succ n =>
          simp only [map_add (coeff _), coeff_succ_X_mul, coeff_C_mul, coeff_derivative, Nat.cast_add,
            Nat.cast_one, Nat.cast_succ]
          have h := hrec (n + 2)
          simp only [Nat.cast_add, Nat.cast_ofNat] at h
          linear_combination h

theorem hypergeometricPadic_recurrence (i : Fin 2) (n : ℕ) :
    ((n : ℚ_[7]) + 1) * ((n : ℚ_[7]) + (1 + 2 * i.val) / 2) *
        coeff (n + 1) (annularHypergeometricPadic i) =
      ((n : ℚ_[7]) + (1 + 6 * i.val) / 12) * ((n : ℚ_[7]) + (5 + 6 * i.val) / 12) *
        coeff n (annularHypergeometricPadic i) := by
  have h := hypergeometric_coefficient_recurrence
    ((1 + 6 * i.val) / 12 : ℚ) ((5 + 6 * i.val) / 12) ((1 + 2 * i.val) / 2)
      (by positivity) n
  simp only [annularHypergeometricPadic, coeff_mk, annularHypergeometricCoefficient]
  have hp := congrArg (fun z : ℚ => (z : ℚ_[7])) h
  simp only [Rat.cast_mul, Rat.cast_add, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] at hp
  exact hp

theorem hypergeometricPadic_ordinary_equation (i : Fin 2) :
    X * hypergeometricJetSeries i 2 + C ((1 + 2 * i.val) / 2 : ℚ_[7]) * hypergeometricJetSeries i 1 =
      X * (X * hypergeometricJetSeries i 2) +
        C ((3 + 2 * i.val) / 2 : ℚ_[7]) * (X * hypergeometricJetSeries i 1) +
        C (((1 + 6 * i.val) * (5 + 6 * i.val)) / 144 : ℚ_[7]) * hypergeometricJetSeries i 0 := by
  have h := ordinary_equation_of_coeff_recurrence (annularHypergeometricPadic i)
    ((1 + 6 * i.val) / 12) ((5 + 6 * i.val) / 12) ((1 + 2 * i.val) / 2)
    (hypergeometricPadic_recurrence i)
  have ha : ((1 + 6 * i.val) / 12 : ℚ_[7]) + (5 + 6 * i.val) / 12 + 1 =
      (3 + 2 * i.val) / 2 := by ring
  have hb : ((1 + 6 * i.val) / 12 : ℚ_[7]) * ((5 + 6 * i.val) / 12) =
      ((1 + 6 * i.val) * (5 + 6 * i.val)) / 144 := by ring
  rw [ha, hb] at h
  exact h

namespace ClosedAnnulus
variable {r R : ℝ} [Fact (0 < r)] [Fact (0 < R)]

theorem hypergeometricJetValue_ordinary_equation (i : Fin 2) (s : ClosedAnnulus r R) (hs : ‖s‖ < 1) :
    s * hypergeometricJetValue i 2 s + constant ((1 + 2 * i.val) / 2 : ℚ_[7]) * hypergeometricJetValue i 1 s =
      s * (s * hypergeometricJetValue i 2 s) +
        constant ((3 + 2 * i.val) / 2 : ℚ_[7]) * (s * hypergeometricJetValue i 1 s) +
        constant (((1 + 6 * i.val) * (5 + 6 * i.val)) / 144 : ℚ_[7]) * hypergeometricJetValue i 0 s := by
  have h0 := hypergeometricJetSeries_summable i 0 s hs
  have h1 := hypergeometricJetSeries_summable i 1 s hs
  have h2 := hypergeometricJetSeries_summable i 2 s hs
  have h := congrArg (fun f => taylorValue f s) (hypergeometricPadic_ordinary_equation i)
  rw [taylorValue_add h2.X_mul (h1.C_mul _), taylorValue_X_mul h2, taylorValue_C_mul _ h1,
    taylorValue_add ((h2.X_mul.X_mul).add (h1.X_mul.C_mul _)) (h0.C_mul _),
    taylorValue_add (h2.X_mul.X_mul) (h1.X_mul.C_mul _),
    taylorValue_X_mul h2.X_mul, taylorValue_X_mul h2,
    taylorValue_C_mul _ h1.X_mul, taylorValue_X_mul h1, taylorValue_C_mul _ h0] at h
  exact h

end ClosedAnnulus
end Zeta7Annulus

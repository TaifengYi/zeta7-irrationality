import Zeta7Proof.ActualSevenGermIndependence
import Zeta7Proof.RationalDeterminantProductFormula

/-! The unchanged auxiliary endpoint and its finite-support sign convention.
The equivalence below does not prove the endpoint. -/
noncomputable section
set_option autoImplicit false
namespace Zeta7Auxiliary
open Zeta7ProductFormula Zeta7Common

theorem auxiliary_eq_neg_prime_sum (q : ℚ) :
    auxiliary q = -(∑ p ∈ (primeSupport q).erase 7,
      (padicValRat p q : ℝ)*Real.log p) := by
  simp only [auxiliary, localTerm, neg_mul, Finset.sum_neg_distrib]

theorem auxiliary_le_iff_prime_sum (q : ℚ) (B : ℝ) :
    auxiliary q ≤ B ↔ -B ≤ ∑ p ∈ (primeSupport q).erase 7,
      (padicValRat p q : ℝ)*Real.log p := by
  rw [auxiliary_eq_neg_prime_sum]
  constructor <;> intro h <;> linarith

/-- The actual target P; this is a proposition, not an assumed or proved fact. -/
def ActualAuxiliaryEstimate : Prop :=
  ∀ c : ℚ, ∀ ε : ℝ, 0 < ε → ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
    auxiliary (actualCommonDeterminant d c) ≤ (12325/168+ε)*(d : ℝ)^2

theorem actualAuxiliaryEstimate_iff : ActualAuxiliaryEstimate ↔
    ∀ c : ℚ, ∀ ε : ℝ, 0 < ε → ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
      -((12325/168+ε)*(d : ℝ)^2) ≤
        ∑ p ∈ (primeSupport (actualCommonDeterminant d c)).erase 7,
          (padicValRat p (actualCommonDeterminant d c) : ℝ)*Real.log p := by
  simp only [ActualAuxiliaryEstimate, auxiliary_le_iff_prime_sum]

end Zeta7Auxiliary

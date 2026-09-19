import Zeta7Proof.AnnularSplitConvergence
import Mathlib.Tactic.ComputeDegree

/-! The finite boundary correction and its actual quadratic polynomial.
Only finite polynomials are evaluated at the boundary point. -/
noncomputable section
set_option autoImplicit false
namespace Zeta7Annulus
open Polynomial
local instance AnnularForcingCorrection_local1 : Fact (Nat.Prime 7) := ⟨by decide⟩

def annularBoundaryPoint : ℚ_[7] := -10 / 49
def annularForcingPolynomial : Polynomial ℚ_[7] :=
  C (annularFiniteForcing (-2)) + C (annularFiniteForcing (-1)) * X +
    C (annularFiniteForcing 0) * X ^ 2 + C (annularFiniteForcing 1) * X ^ 3
def annularBaseForcingPolynomial : Polynomial ℚ_[7] := -8 - 105 * X - 433 * X ^ 2 - 441 * X ^ 3

theorem annularBaseForcing_boundary :
    annularBoundaryPoint⁻¹ ^ 2 * annularBaseForcingPolynomial.eval annularBoundaryPoint =
      (-1029 / 50 : ℚ_[7]) := by
  norm_num [annularBaseForcingPolynomial, annularBoundaryPoint]

theorem annularBaseForcingPolynomial_boundary :
    annularBaseForcingPolynomial.eval annularBoundaryPoint = (-6 / 7 : ℚ_[7]) := by
  norm_num [annularBaseForcingPolynomial, annularBoundaryPoint]

def annularCorrectionConstant : ℚ_[7] :=
  annularForcingPolynomial.eval annularBoundaryPoint /
    annularBaseForcingPolynomial.eval annularBoundaryPoint

theorem annularCorrectionConstant_boundary_ratio : annularCorrectionConstant =
    (annularBoundaryPoint⁻¹ ^ 2 * annularForcingPolynomial.eval annularBoundaryPoint) / (-1029 / 50) := by
  rw [annularCorrectionConstant, annularBaseForcingPolynomial_boundary]
  unfold annularBoundaryPoint
  field_simp
  ring

def annularCorrectedForcingPolynomial : Polynomial ℚ_[7] :=
  annularForcingPolynomial - C annularCorrectionConstant * annularBaseForcingPolynomial

theorem annularCorrectedForcing_root :
    annularCorrectedForcingPolynomial.eval annularBoundaryPoint = 0 := by
  have hn : annularBaseForcingPolynomial.eval annularBoundaryPoint ≠ 0 := by
    rw [annularBaseForcingPolynomial_boundary]; norm_num
  simp only [annularCorrectedForcingPolynomial, eval_sub, eval_mul, eval_C,
    annularCorrectionConstant, div_mul_cancel₀ _ hn, sub_self]

def correctedForcing₀ : ℚ_[7] := annularFiniteForcing (-2) + 8 * annularCorrectionConstant
def correctedForcing₁ : ℚ_[7] := annularFiniteForcing (-1) + 105 * annularCorrectionConstant
def correctedForcing₂ : ℚ_[7] := annularFiniteForcing 0 + 433 * annularCorrectionConstant
def correctedForcing₃ : ℚ_[7] := annularFiniteForcing 1 + 441 * annularCorrectionConstant

theorem annularCorrectedForcing_coefficients : annularCorrectedForcingPolynomial =
    C correctedForcing₀ + C correctedForcing₁ * X + C correctedForcing₂ * X ^ 2 +
      C correctedForcing₃ * X ^ 3 := by
  unfold annularCorrectedForcingPolynomial annularForcingPolynomial annularBaseForcingPolynomial
    correctedForcing₀ correctedForcing₁ correctedForcing₂ correctedForcing₃
  polynomial

def annularQuadratic₀ : ℚ_[7] := -correctedForcing₃
def annularQuadratic₁ : ℚ_[7] := -correctedForcing₂ + 10 * correctedForcing₃ / 49
def annularQuadratic₂ : ℚ_[7] :=
  -correctedForcing₁ + 10 * correctedForcing₂ / 49 - 100 * correctedForcing₃ / 2401

def annularForcingQuadratic : Polynomial ℚ_[7] :=
  C annularQuadratic₀ + C annularQuadratic₁ * X + C annularQuadratic₂ * X ^ 2

/-- Padded reversal, valid even when the quadratic has degree below two. -/
def annularForcingReversed : Polynomial ℚ_[7] :=
  C annularQuadratic₀ * X ^ 2 + C annularQuadratic₁ * X + C annularQuadratic₂

theorem annularForcingQuadratic_degree : annularForcingQuadratic.natDegree ≤ 2 := by
  unfold annularForcingQuadratic
  compute_degree!

theorem annularCorrectedForcing_factorization : annularCorrectedForcingPolynomial =
    C (-1 / 49 : ℚ_[7]) * (10 + 49 * X) * annularForcingReversed := by
  have hr := annularCorrectedForcing_root
  rw [annularCorrectedForcing_coefficients] at hr
  simp only [eval_add, eval_mul, eval_pow, eval_C, eval_X] at hr
  rw [annularCorrectedForcing_coefficients]
  calc
    _ = C (-1 / 49 : ℚ_[7]) * (10 + 49 * X) * annularForcingReversed +
        C (correctedForcing₀ + correctedForcing₁ * annularBoundaryPoint +
          correctedForcing₂ * annularBoundaryPoint ^ 2 + correctedForcing₃ * annularBoundaryPoint ^ 3) := by
      unfold annularForcingReversed annularQuadratic₀ annularQuadratic₁ annularQuadratic₂ annularBoundaryPoint
      polynomial
    _ = _ := by rw [hr, C_0, add_zero]

end Zeta7Annulus

import Zeta7Proof.AnnularOrdinaryEquations

/-! Cleared differential equations and the four actual annular products.
No inverse of the hypergeometric discriminant is used. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
namespace Zeta7Annulus.ClosedAnnulus
local instance AnnularFourComponent_local1 : Fact (Nat.Prime 7) := ⟨by decide⟩
variable {r R : ℝ} [Fact (0 < r)] [Fact (0 < R)]

def hypergeometricDiscriminant : ClosedAnnulus r R :=
  annularSubstitution * (1 - annularSubstitution)

def hypergeometricAlpha : ClosedAnnulus r R :=
  constant (3 / 2 : ℚ_[7]) * annularSubstitution - constant (1 / 2 : ℚ_[7])

def hypergeometricGamma : ClosedAnnulus r R :=
  constant (5 / 2 : ℚ_[7]) * annularSubstitution - constant (3 / 2 : ℚ_[7])

theorem actual_hypergeometric_A_cleared (hr : 1 < r) (hR : R < 49) (hrR : r ≤ R) :
    hypergeometricDiscriminant * actualHypergeometricJet (r := r) (R := R) 0 2 =
      constant (5 / 144 : ℚ_[7]) * actualHypergeometricJet 0 0 +
        hypergeometricAlpha * actualHypergeometricJet 0 1 := by
  have h := hypergeometricJetValue_ordinary_equation (r := r) (R := R) 0
    annularSubstitution (annularSubstitution_norm_lt_one hr hR hrR)
  norm_num only [Fin.val_zero, Nat.cast_zero, mul_zero, add_zero, mul_one, one_mul] at h
  unfold hypergeometricDiscriminant hypergeometricAlpha actualHypergeometricJet
  linear_combination h

theorem actual_hypergeometric_C_cleared (hr : 1 < r) (hR : R < 49) (hrR : r ≤ R) :
    hypergeometricDiscriminant * actualHypergeometricJet (r := r) (R := R) 1 2 =
      constant (77 / 144 : ℚ_[7]) * actualHypergeometricJet 1 0 +
        hypergeometricGamma * actualHypergeometricJet 1 1 := by
  have h := hypergeometricJetValue_ordinary_equation (r := r) (R := R) 1
    annularSubstitution (annularSubstitution_norm_lt_one hr hR hrR)
  norm_num only [Fin.val_one, Nat.cast_one] at h
  unfold hypergeometricDiscriminant hypergeometricGamma actualHypergeometricJet
  linear_combination h

def fourComponentValue (ell : Fin 4 → ClosedAnnulus r R) : ClosedAnnulus r R :=
  ell 0 * (actualHypergeometricJet 0 0 * actualHypergeometricJet 1 0) +
  ell 1 * (actualHypergeometricJet 0 1 * actualHypergeometricJet 1 0) +
  ell 2 * (actualHypergeometricJet 0 0 * actualHypergeometricJet 1 1) +
  ell 3 * (actualHypergeometricJet 0 1 * actualHypergeometricJet 1 1)

def fourComponentNext (ell : Fin 4 → ClosedAnnulus r R)
    (mu : Fin 3 → ClosedAnnulus r R) : Fin 4 → ClosedAnnulus r R :=
  ![euler (ell 0) + constant (5 / 144 : ℚ_[7]) * mu 0 + constant (77 / 144 : ℚ_[7]) * mu 1,
    euler (ell 1) + ell 0 * euler annularSubstitution + hypergeometricAlpha * mu 0 +
      constant (77 / 144 : ℚ_[7]) * mu 2,
    euler (ell 2) + ell 0 * euler annularSubstitution + hypergeometricGamma * mu 1 +
      constant (5 / 144 : ℚ_[7]) * mu 2,
    euler (ell 3) + (ell 1 + ell 2) * euler annularSubstitution +
      (hypergeometricAlpha + hypergeometricGamma) * mu 2]

/-- The reduction hypotheses are polynomial multiplier identities, not units of q. -/
theorem fourComponent_derivative (hr : 1 < r) (hR : R < 49) (hrR : r ≤ R)
    (ell : Fin 4 → ClosedAnnulus r R) (mu : Fin 3 → ClosedAnnulus r R)
    (h1 : ell 1 * euler annularSubstitution = hypergeometricDiscriminant * mu 0)
    (h2 : ell 2 * euler annularSubstitution = hypergeometricDiscriminant * mu 1)
    (h3 : ell 3 * euler annularSubstitution = hypergeometricDiscriminant * mu 2) :
    euler (fourComponentValue ell) = fourComponentValue (fourComponentNext ell mu) := by
  have hA := actual_hypergeometric_A_cleared hr hR hrR
  have hC := actual_hypergeometric_C_cleared hr hR hrR
  simp only [fourComponentValue, fourComponentNext, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons, Matrix.tail_cons,
    euler_add, euler_mul, actualHypergeometricJet_chain hr hR hrR]
  linear_combination
    (mu 0 * actualHypergeometricJet 1 0 + mu 2 * actualHypergeometricJet 1 1) * hA +
    (mu 1 * actualHypergeometricJet 0 0 + mu 2 * actualHypergeometricJet 0 1) * hC +
    (actualHypergeometricJet 0 2 * actualHypergeometricJet 1 0) * h1 +
    (actualHypergeometricJet 0 0 * actualHypergeometricJet 1 2) * h2 +
    (actualHypergeometricJet 0 2 * actualHypergeometricJet 1 1 +
      actualHypergeometricJet 0 1 * actualHypergeometricJet 1 2) * h3

end Zeta7Annulus.ClosedAnnulus

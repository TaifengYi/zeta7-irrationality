import Zeta7Proof.AnnularBilateralBand

/-! The actual split between -2 and -3 and its four-term forcing, as complete coefficient identities. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
namespace Zeta7Annulus
local instance AnnularFiniteForcing_local1 : Fact (Nat.Prime 7) := ⟨by decide⟩

def annularPositivePart (k : ℤ) : ℚ_[7] := if -2 ≤ k then annularCandidateA k else 0
def annularNegativePart : LaurentCoefficients := annularCandidateA - annularPositivePart
def annularFiniteForcing : LaurentCoefficients := bilateralBand annularPositivePart

theorem annularPositivePart_below {k : ℤ} (hk : k < -2) : annularPositivePart k = 0 := by
  simp only [annularPositivePart, if_neg (by omega : ¬ -2 ≤ k)]

theorem annularNegativePart_above {k : ℤ} (hk : -2 ≤ k) : annularNegativePart k = 0 := by
  simp only [annularNegativePart, Pi.sub_apply, annularPositivePart, if_pos hk, sub_self]

theorem annular_split : annularPositivePart + annularNegativePart = annularCandidateA := by
  unfold annularNegativePart
  abel

theorem annularFiniteForcing_negative : annularFiniteForcing = -bilateralBand annularNegativePart := by
  rw [annularNegativePart, bilateralBand_sub, annularCandidateA_band_zero, zero_sub, neg_neg]
  rfl

theorem annularFiniteForcing_below {k : ℤ} (hk : k < -2) : annularFiniteForcing k = 0 := by
  simp only [annularFiniteForcing, bilateralBand, annularPositivePart_below hk,
    annularPositivePart_below (by omega : k - 1 < -2),
    annularPositivePart_below (by omega : k - 2 < -2),
    annularPositivePart_below (by omega : k - 3 < -2),
    annularPositivePart_below (by omega : k - 4 < -2), mul_zero, add_zero]

theorem annularFiniteForcing_above {k : ℤ} (hk : 1 < k) : annularFiniteForcing k = 0 := by
  rw [annularFiniteForcing_negative]
  simp only [Pi.neg_apply, bilateralBand, annularNegativePart_above (by omega : -2 ≤ k),
    annularNegativePart_above (by omega : -2 ≤ k - 1),
    annularNegativePart_above (by omega : -2 ≤ k - 2),
    annularNegativePart_above (by omega : -2 ≤ k - 3),
    annularNegativePart_above (by omega : -2 ≤ k - 4), mul_zero, add_zero, neg_zero]

theorem annularFiniteForcing_coefficients :
    annularFiniteForcing (-2) = -8 * annularCandidateA (-2) ∧
    annularFiniteForcing (-1) = -annularCandidateA (-1) - 105 * annularCandidateA (-2) ∧
    annularFiniteForcing 0 = -9 * annularCandidateA (-1) - 433 * annularCandidateA (-2) ∧
    annularFiniteForcing 1 = annularCandidateA 1 + 9 * annularCandidateA 0 - 441 * annularCandidateA (-2) := by
  norm_num [annularFiniteForcing, bilateralBand, annularPositivePart, bandWeight₀,
    bandWeight₁, bandWeight₂, bandWeight₃, bandWeight₄]
  ring_nf
  simp

theorem annularFiniteForcing_four_terms : annularFiniteForcing =
    bilateralMonomial (-2) (annularFiniteForcing (-2)) +
    bilateralMonomial (-1) (annularFiniteForcing (-1)) +
    bilateralMonomial 0 (annularFiniteForcing 0) +
    bilateralMonomial 1 (annularFiniteForcing 1) := by
  funext k
  by_cases h0 : k = -2
  · subst k; simp [bilateralMonomial]
  by_cases h1 : k = -1
  · subst k; simp [bilateralMonomial]
  by_cases h2 : k = 0
  · subst k; simp [bilateralMonomial]
  by_cases h3 : k = 1
  · subst k; simp [bilateralMonomial]
  simp only [Pi.add_apply, bilateralMonomial, if_neg h0, if_neg h1, if_neg h2, if_neg h3, add_zero]
  have hk : k < -2 ∨ 1 < k := by omega
  exact hk.elim annularFiniteForcing_below annularFiniteForcing_above

end Zeta7Annulus

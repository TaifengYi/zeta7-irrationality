import Zeta7Proof.AnnularCorrectionBounds
import Zeta7Proof.AnnularCorrectedSolution

/-! The actual corrected coefficient family, including its uniform integral bound. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
namespace Zeta7Annulus
local instance AnnularCorrectedCoefficients_prime : Fact (Nat.Prime 7) := ⟨by decide⟩
local instance AnnularCorrectedCoefficients_radius : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

def annularCorrectedPart : LaurentCoefficients :=
  annularPositivePart - bilateralMonomial (-2) annularCorrectionConstant

def annularCorrectedCoefficients (k : ℤ) : ℚ_[7] :=
  annularCorrectedPart k + 13 * annularCorrectedPart (k - 1) +
    49 * annularCorrectedPart (k - 2)

theorem ClosedAnnulus.correctedSolutionOn_coefficients {r R : ℝ}
    [Fact (0 < r)] [Fact (0 < R)] (hR : R < 49) (hrR : r ≤ R) :
    (correctedSolutionOn (r := r) hR hrR).coeffs = annularCorrectedCoefficients := by
  funext k
  simp only [correctedSolutionOn, annularP, add_mul, one_mul, coeffs_add,
    coeffs_mul, monomial_coeffs, Pi.add_apply, bilateralMonomial_convolution]
  simp only [correctedPartOn, coeffs_sub, monomial_coeffs,
    annularCorrectedCoefficients, annularCorrectedPart]
  rfl

theorem annularCorrectedCoefficients_decays (ρ : ℝ) (hρ : 0 < ρ) (h49 : ρ < 49) :
    DecaysAt annularCorrectedCoefficients ρ := by
  letI : Fact (0 < ρ) := ⟨hρ⟩
  rw [← ClosedAnnulus.correctedSolutionOn_coefficients (r := ρ) h49 le_rfl]
  exact (ClosedAnnulus.correctedSolutionOn h49 le_rfl).inner

theorem annularCorrectedPart_below {k : ℤ} (hk : k < -2) : annularCorrectedPart k = 0 := by
  simp [annularCorrectedPart, annularPositivePart_below hk, bilateralMonomial, ne_of_lt hk]

theorem annularCorrectedCoefficients_below {k : ℤ} (hk : k < -2) :
    annularCorrectedCoefficients k = 0 := by
  simp [annularCorrectedCoefficients, annularCorrectedPart_below hk,
    annularCorrectedPart_below (by omega : k - 1 < -2),
    annularCorrectedPart_below (by omega : k - 2 < -2)]

theorem annularPositivePart_coefficient_bound (k : ℤ) : ‖annularPositivePart k‖ ≤ (7 : ℝ) := by
  unfold annularPositivePart
  split_ifs with hk
  · have hp : (7 : ℝ) ^ (-k) ≤ (7 : ℝ) ^ (2 : ℤ) :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    exact (annularCandidateA_coefficient_bound k).trans
      ((mul_le_mul_of_nonneg_left hp (by positivity)).trans (by norm_num))
  · norm_num

theorem annularCorrectedPart_coefficient_bound (k : ℤ) :
    ‖annularCorrectedPart k‖ ≤ (2401 : ℝ) := by
  apply padic_sub_bound ((annularPositivePart_coefficient_bound k).trans (by norm_num))
  by_cases hk : k = -2
  · simpa only [bilateralMonomial, if_pos hk] using annularCorrectionConstant_bound
  · simp [bilateralMonomial, hk]

theorem annularCorrectedCoefficients_bound (k : ℤ) :
    ‖annularCorrectedCoefficients k‖ ≤ (2401 : ℝ) := by
  exact padic_add_bound (padic_add_bound (annularCorrectedPart_coefficient_bound k)
    (padic_int_mul_bound 13 (annularCorrectedPart_coefficient_bound (k - 1))))
    (padic_int_mul_bound 49 (annularCorrectedPart_coefficient_bound (k - 2)))

namespace ClosedAnnulus

theorem unitCircle_norm_le {a : ClosedAnnulus 1 1} {C : ℝ}
    (h : ∀ k, ‖a.coeffs k‖ ≤ C) : ‖a‖ ≤ C := by
  rw [norm_eq, closedAnnulusGauss, max_self]
  apply bilateralGauss_le
  intro k
  simpa only [weightedCoefficient, one_zpow, mul_one] using h k

def correctedUnitCircle : ClosedAnnulus 1 1 :=
  correctedSolutionOn (by norm_num) le_rfl

theorem correctedUnitCircle_coefficients : correctedUnitCircle.coeffs = annularCorrectedCoefficients :=
  correctedSolutionOn_coefficients _ _

theorem correctedUnitCircle_norm_bound : ‖correctedUnitCircle‖ ≤ (2401 : ℝ) := by
  apply unitCircle_norm_le
  rw [correctedUnitCircle_coefficients]
  exact annularCorrectedCoefficients_bound

def reflectUnitCircle (a : ClosedAnnulus 1 1) : ClosedAnnulus 1 1 where
  coeffs k := a.coeffs (-k)
  inner := by
    have h := a.inner
    simp only [DecaysAt, inv_one, one_pow, mul_one] at h ⊢
    simpa only [neg_neg] using h.symm
  outer := by
    have h := a.outer
    simp only [DecaysAt, inv_one, one_pow, mul_one] at h ⊢
    simpa only [neg_neg] using h.symm

theorem reflectUnitCircle_coefficients (a : ClosedAnnulus 1 1) (k : ℤ) :
    (reflectUnitCircle a).coeffs k = a.coeffs (-k) := rfl

theorem reflectUnitCircle_norm_le (a : ClosedAnnulus 1 1) : ‖reflectUnitCircle a‖ ≤ ‖a‖ := by
  apply unitCircle_norm_le
  intro k
  simpa only [reflectUnitCircle_coefficients, one_zpow, mul_one] using a.coeff_norm_le (-k)

def reflectedCorrectedSolution : ClosedAnnulus 1 1 := reflectUnitCircle correctedUnitCircle

theorem reflectedCorrectedSolution_coefficients (k : ℤ) :
    reflectedCorrectedSolution.coeffs k = annularCorrectedCoefficients (-k) := by
  simp only [reflectedCorrectedSolution, reflectUnitCircle_coefficients, correctedUnitCircle_coefficients]

theorem reflectedCorrectedSolution_norm_bound : ‖reflectedCorrectedSolution‖ ≤ (2401 : ℝ) :=
  (reflectUnitCircle_norm_le _).trans correctedUnitCircle_norm_bound

theorem reflectedCorrectedSolution_above {k : ℤ} (hk : 2 < k) :
    reflectedCorrectedSolution.coeffs k = 0 := by
  rw [reflectedCorrectedSolution_coefficients]
  exact annularCorrectedCoefficients_below (by omega)

end ClosedAnnulus
end Zeta7Annulus

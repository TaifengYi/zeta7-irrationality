import Zeta7Proof.AnnularHomogeneousSolution

/-! The homogeneous equation for the existing global bilateral coefficient family. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
namespace Zeta7Annulus
local instance AnnularGlobalHomogeneous_local1 : Fact (Nat.Prime 7) := ⟨by decide⟩
local instance AnnularGlobalHomogeneous_local2 : Fact (0 < (2 : ℝ)) := ⟨by norm_num⟩
local instance AnnularGlobalHomogeneous_local3 : Fact (0 < (3 : ℝ)) := ⟨by norm_num⟩
namespace ClosedAnnulus
variable {r R : ℝ} [Fact (0 < r)] [Fact (0 < R)]

theorem coeffs_constant_mul (z : ℚ_[7]) (f : ClosedAnnulus r R) (k : ℤ) :
    (constant z * f).coeffs k = z * f.coeffs k := by
  change bilateralConvolution (bilateralMonomial 0 z) f.coeffs k = _
  rw [bilateralMonomial_convolution, sub_zero]

theorem coeffs_euler (f : ClosedAnnulus r R) : (euler f).coeffs = bilateralEuler f.coeffs := rfl

theorem restrict_annularPotential {s S : ℝ} [Fact (0 < s)] [Fact (0 < S)]
    (hr : 1 < r) (hR : R < 49) (hrs : r ≤ s) (hsS : s ≤ S) (hSR : S ≤ R) :
    restrict hrs hsS hSR annularPotential = annularPotential := by
  simp only [annularPotential_formula, map_mul, map_add, map_pow, map_one, map_ofNat,
    restrict_monomial, restrict_pInverse hr hR hrs hsS hSR]

end ClosedAnnulus

def annularPotentialCoefficients : LaurentCoefficients :=
  (ClosedAnnulus.annularPotential (r := 2) (R := 3)).coeffs

theorem annularPotentialCoefficients_eq {r R : ℝ} [Fact (0 < r)] [Fact (0 < R)]
    (hr : 1 < r) (hR : R < 49) (hrR : r ≤ R) :
    annularPotentialCoefficients = (ClosedAnnulus.annularPotential (r := r) (R := R)).coeffs := by
  have hlo : 1 < min r 2 := lt_min hr (by norm_num)
  have hhi : max R 3 < 49 := max_lt hR (by norm_num)
  letI : Fact (0 < min r 2) := ⟨by linarith⟩
  letI : Fact (0 < max R 3) := ⟨(by norm_num : (0 : ℝ) < 3).trans_le (le_max_right _ _)⟩
  have hA := congrArg ClosedAnnulus.coeffs (ClosedAnnulus.restrict_annularPotential hlo hhi
    (min_le_left r 2) hrR (le_max_left R 3))
  have hB := congrArg ClosedAnnulus.coeffs (ClosedAnnulus.restrict_annularPotential hlo hhi
    (min_le_right r 2) (by norm_num : (2 : ℝ) ≤ 3) (le_max_right R 3))
  simp only [ClosedAnnulus.restrict_coeffs] at hA hB
  exact hB.symm.trans hA

theorem annularPotentialCoefficients_decays : DecaysOn annularPotentialCoefficients 1 49 := by
  intro ρ hρ h49
  letI : Fact (0 < ρ) := ⟨by linarith⟩
  rw [annularPotentialCoefficients_eq hρ h49 le_rfl]
  exact (ClosedAnnulus.annularPotential (r := ρ) (R := ρ)).inner

theorem annularCandidateB_homogeneous (k : ℤ) :
    bilateralEuler (bilateralEuler (bilateralEuler annularCandidateB)) k -
      bilateralConvolution annularPotentialCoefficients (bilateralEuler annularCandidateB) k -
      (1 / 2 : ℚ_[7]) * bilateralConvolution (bilateralEuler annularPotentialCoefficients)
        annularCandidateB k = 0 := by
  have h := ClosedAnnulus.candidateB_homogeneous (r := 2) (R := 3)
    (by norm_num) (by norm_num) (by norm_num)
  rw [mul_assoc (ClosedAnnulus.constant (1 / 2 : ℚ_[7]))] at h
  have hk := congrArg (fun f : ClosedAnnulus 2 3 => f.coeffs k) h
  simp only [ClosedAnnulus.coeffs_sub, Pi.sub_apply] at hk
  rw [ClosedAnnulus.coeffs_constant_mul] at hk
  simp only [ClosedAnnulus.coeffs_mul, ClosedAnnulus.coeffs_euler, ClosedAnnulus.coeffs_zero,
    Pi.zero_apply] at hk
  exact hk

end Zeta7Annulus

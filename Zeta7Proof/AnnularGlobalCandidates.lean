import Zeta7Proof.AnnularSubstitution

/-! One coefficient family on the entire open annulus for each of the guide's
explicit candidates b = (T/N²) A(s) C(s) and a = b/P. Restriction compatibility
is proved. Their homogeneous differential equations are not asserted here. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
namespace Zeta7Annulus
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩
local instance : Fact (0 < (2 : ℝ)) := ⟨by norm_num⟩
local instance : Fact (0 < (3 : ℝ)) := ⟨by norm_num⟩

namespace ClosedAnnulus
variable {r R : ℝ} [Fact (0 < r)] [Fact (0 < R)]

def candidateB : ClosedAnnulus r R :=
  annularT * nInverse ^ 2 * actualHypergeometricValue 0 * actualHypergeometricValue 1

def candidateA : ClosedAnnulus r R := candidateB * pInverse

def candidate (i : Fin 2) : ClosedAnnulus r R := if i = 0 then candidateB else candidateA

theorem restrict_candidateB {s S : ℝ} [Fact (0 < s)] [Fact (0 < S)]
    (hr : 1 < r) (hR : R < 49) (hrs : r ≤ s) (hsS : s ≤ S) (hSR : S ≤ R) :
    restrict hrs hsS hSR candidateB = candidateB := by
  simp only [candidateB, map_mul, map_pow, restrict_T,
    restrict_nInverse hr hR hrs hsS hSR, restrict_actualHypergeometricValue hr hR hrs hsS hSR]

theorem restrict_candidateA {s S : ℝ} [Fact (0 < s)] [Fact (0 < S)]
    (hr : 1 < r) (hR : R < 49) (hrs : r ≤ s) (hsS : s ≤ S) (hSR : S ≤ R) :
    restrict hrs hsS hSR candidateA = candidateA := by
  simp only [candidateA, map_mul, restrict_candidateB hr hR hrs hsS hSR,
    restrict_pInverse hr hR hrs hsS hSR]

theorem restrict_candidate {s S : ℝ} [Fact (0 < s)] [Fact (0 < S)]
    (hr : 1 < r) (hR : R < 49) (hrs : r ≤ s) (hsS : s ≤ S) (hSR : S ≤ R) (i : Fin 2) :
    restrict hrs hsS hSR (candidate i) = candidate i := by
  unfold candidate
  split_ifs
  · exact restrict_candidateB hr hR hrs hsS hSR
  · exact restrict_candidateA hr hR hrs hsS hSR

end ClosedAnnulus

def annularCandidateCoefficients (i : Fin 2) : LaurentCoefficients :=
  (ClosedAnnulus.candidate (r := 2) (R := 3) i).coeffs

theorem annularCandidateCoefficients_eq {r R : ℝ} [Fact (0 < r)] [Fact (0 < R)]
    (hr : 1 < r) (hR : R < 49) (hrR : r ≤ R) (i : Fin 2) :
    annularCandidateCoefficients i = (ClosedAnnulus.candidate (r := r) (R := R) i).coeffs := by
  have hlo : 1 < min r 2 := lt_min hr (by norm_num)
  have hhi : max R 3 < 49 := max_lt hR (by norm_num)
  letI : Fact (0 < min r 2) := ⟨by linarith⟩
  letI : Fact (0 < max R 3) := ⟨(by norm_num : (0 : ℝ) < 3).trans_le (le_max_right _ _)⟩
  have hA := ClosedAnnulus.restrict_candidate hlo hhi (min_le_left r 2) hrR (le_max_left R 3) i
  have hB := ClosedAnnulus.restrict_candidate hlo hhi (min_le_right r 2)
    (by norm_num : (2 : ℝ) ≤ 3) (le_max_right R 3) i
  have hA' := congrArg ClosedAnnulus.coeffs hA
  have hB' := congrArg ClosedAnnulus.coeffs hB
  simp only [ClosedAnnulus.restrict_coeffs] at hA' hB'
  exact hB'.symm.trans hA'

theorem annularCandidateCoefficients_decays (i : Fin 2) :
    DecaysOn (annularCandidateCoefficients i) 1 49 := by
  intro ρ hρ h49
  letI : Fact (0 < ρ) := ⟨by linarith⟩
  rw [annularCandidateCoefficients_eq hρ h49 le_rfl i]
  exact (ClosedAnnulus.candidate (r := ρ) (R := ρ) i).inner

def annularCandidateB : LaurentCoefficients := annularCandidateCoefficients 0
def annularCandidateA : LaurentCoefficients := annularCandidateCoefficients 1

theorem annularCandidateB_decays : DecaysOn annularCandidateB 1 49 :=
  annularCandidateCoefficients_decays 0

theorem annularCandidateA_decays : DecaysOn annularCandidateA 1 49 :=
  annularCandidateCoefficients_decays 1

end Zeta7Annulus

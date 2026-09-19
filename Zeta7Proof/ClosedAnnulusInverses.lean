import Zeta7Proof.ClosedAnnulusPolynomialUnits

/-! Canonical inverses of the actual annular polynomials, their geometric
series formula, and compatibility on smaller closed annuli. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
namespace Zeta7Annulus.ClosedAnnulus
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩
variable {r R : ℝ} [Fact (0 < r)] [Fact (0 < R)]

def pInverse : ClosedAnnulus r R := Ring.inverse annularP
def nInverse : ClosedAnnulus r R := Ring.inverse annularN

theorem annularP_mul_inverse (hr : 1 < r) (hR : R < 49) (hrR : r ≤ R) :
    annularP (r := r) (R := R) * pInverse = 1 :=
  Ring.mul_inverse_cancel _ (annularP_isUnit hr hR hrR)

theorem annularN_mul_inverse (hr : 1 < r) (hR : R < 49) (hrR : r ≤ R) :
    annularN (r := r) (R := R) * nInverse = 1 :=
  Ring.mul_inverse_cancel _ (annularN_isUnit hr hR hrR)

theorem nInverse_geometric (hr : 1 < r) (hR : R < 49) (hrR : r ≤ R) :
    HasSum (fun n : ℕ => (-nContraction (r := r) (R := R)) ^ n) nInverse := by
  have ht := hasSum_geom_series_inverse (-nContraction (r := r) (R := R))
    (by simpa only [norm_neg] using nContraction_norm_lt_one hr hR hrR)
  simpa only [nInverse, annularN, nContraction, sub_neg_eq_add, add_assoc] using ht

theorem pInverse_geometric (hr : 1 < r) (hR : R < 49) (hrR : r ≤ R) :
    HasSum (fun n : ℕ => (-pContraction (r := r) (R := R)) ^ n * monomial (-1) (1 / 13))
      pInverse := by
  have ht := (hasSum_geom_series_inverse (-pContraction (r := r) (R := R))
    (by simpa only [norm_neg] using pContraction_norm_lt_one hr hR hrR)).mul_right
      (monomial (-1) (1 / 13))
  suffices he : Ring.inverse (1 - -pContraction (r := r) (R := R)) *
      monomial (-1) (1 / 13) = pInverse by rwa [he] at ht
  apply (annularP_isUnit hr hR hrR).mul_left_cancel
  rw [annularP_mul_inverse hr hR hrR, annularP_factorization]
  have hu : IsUnit (1 - -pContraction (r := r) (R := R)) :=
    isUnit_one_sub_of_norm_lt_one (by simpa only [norm_neg] using pContraction_norm_lt_one hr hR hrR)
  have hc := Ring.mul_inverse_cancel _ hu
  rw [sub_neg_eq_add] at hc
  calc
    _ = (monomial (r := r) (R := R) 1 13 * monomial (-1) (1 / 13)) *
        ((1 + pContraction (r := r) (R := R)) * Ring.inverse (1 + pContraction)) := by
      simp only [sub_neg_eq_add]
      ring
    _ = 1 := by
      rw [hc, monomial_mul]
      norm_num [monomial_zero_one]

theorem restrict_monomial {s S : ℝ} [Fact (0 < s)] [Fact (0 < S)]
    (hrs : r ≤ s) (hsS : s ≤ S) (hSR : S ≤ R) (n : ℤ) (z : ℚ_[7]) :
    restrict hrs hsS hSR (monomial n z) = monomial n z := rfl

theorem restrict_P {s S : ℝ} [Fact (0 < s)] [Fact (0 < S)]
    (hrs : r ≤ s) (hsS : s ≤ S) (hSR : S ≤ R) :
    restrict hrs hsS hSR annularP = annularP := by
  simp only [annularP, map_add, map_one, restrict_monomial]

theorem restrict_N {s S : ℝ} [Fact (0 < s)] [Fact (0 < S)]
    (hrs : r ≤ s) (hsS : s ≤ S) (hSR : S ≤ R) :
    restrict hrs hsS hSR annularN = annularN := by
  simp only [annularN, map_add, map_one, restrict_monomial]

theorem restrict_pInverse {s S : ℝ} [Fact (0 < s)] [Fact (0 < S)]
    (hr : 1 < r) (hR : R < 49) (hrs : r ≤ s) (hsS : s ≤ S) (hSR : S ≤ R) :
    restrict hrs hsS hSR pInverse = pInverse := by
  apply (annularP_isUnit (hr.trans_le hrs) (hSR.trans_lt hR) hsS).mul_left_cancel
  rw [← restrict_P hrs hsS hSR, ← map_mul, annularP_mul_inverse hr hR (hrs.trans (hsS.trans hSR)),
    map_one, restrict_P hrs hsS hSR,
    annularP_mul_inverse (hr.trans_le hrs) (hSR.trans_lt hR) hsS]

theorem restrict_nInverse {s S : ℝ} [Fact (0 < s)] [Fact (0 < S)]
    (hr : 1 < r) (hR : R < 49) (hrs : r ≤ s) (hsS : s ≤ S) (hSR : S ≤ R) :
    restrict hrs hsS hSR nInverse = nInverse := by
  apply (annularN_isUnit (hr.trans_le hrs) (hSR.trans_lt hR) hsS).mul_left_cancel
  rw [← restrict_N hrs hsS hSR, ← map_mul, annularN_mul_inverse hr hR (hrs.trans (hsS.trans hSR)),
    map_one, restrict_N hrs hsS hSR,
    annularN_mul_inverse (hr.trans_le hrs) (hSR.trans_lt hR) hsS]

end Zeta7Annulus.ClosedAnnulus

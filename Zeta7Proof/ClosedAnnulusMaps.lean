import Zeta7Proof.ClosedAnnulusComplete

/-! Laurent monomials, scalar constants, and compatible restriction maps. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
namespace Zeta7Annulus
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

theorem bilateralGauss_monomial (n : ℤ) (z : ℚ_[7]) {ρ : ℝ} (hρ : 0 < ρ) :
    bilateralGauss (bilateralMonomial n z) ρ = ‖z‖ * ρ ^ n := by
  apply le_antisymm
  · apply bilateralGauss_le
    intro k
    by_cases hk : k = n
    · subst k; simp [weightedCoefficient, bilateralMonomial]
    · simp only [weightedCoefficient, bilateralMonomial, if_neg hk, norm_zero, zero_mul]
      positivity
  · simpa [weightedCoefficient, bilateralMonomial] using
      weightedCoefficient_le_gauss (bilateralMonomial_decays n z ρ) n

namespace ClosedAnnulus
variable {r R : ℝ} [Fact (0 < r)] [Fact (0 < R)]

def monomial (n : ℤ) (z : ℚ_[7]) : ClosedAnnulus r R :=
  ⟨bilateralMonomial n z, bilateralMonomial_decays _ _ _, bilateralMonomial_decays _ _ _⟩

@[simp] theorem monomial_coeffs (n : ℤ) (z : ℚ_[7]) :
    (monomial (r := r) (R := R) n z).coeffs = bilateralMonomial n z := rfl

theorem monomial_norm (n : ℤ) (z : ℚ_[7]) :
    ‖monomial (r := r) (R := R) n z‖ = max (‖z‖ * r ^ n) (‖z‖ * R ^ n) := by
  simp only [norm_eq, closedAnnulusGauss, monomial_coeffs,
    bilateralGauss_monomial n z (Fact.out : 0 < r),
    bilateralGauss_monomial n z (Fact.out : 0 < R)]

@[simp] theorem monomial_zero (n : ℤ) : monomial (r := r) (R := R) n 0 = 0 := by
  ext k; simp [bilateralMonomial]

@[simp] theorem monomial_add (n : ℤ) (z w : ℚ_[7]) :
    monomial (r := r) (R := R) n (z + w) = monomial n z + monomial n w := by
  ext k; simp only [coeffs_add, monomial_coeffs, Pi.add_apply, bilateralMonomial]
  split_ifs <;> simp

@[simp] theorem monomial_zero_one : monomial (r := r) (R := R) 0 1 = 1 := rfl

theorem monomial_mul (n m : ℤ) (z w : ℚ_[7]) :
    monomial (r := r) (R := R) n z * monomial m w = monomial (n + m) (z * w) := by
  ext k
  rw [coeffs_mul, monomial_coeffs, monomial_coeffs, bilateralMonomial_convolution]
  change z * (if k - n = m then w else 0) = if k = n + m then z * w else 0
  have hh : k - n = m ↔ k = n + m := by omega
  simp only [hh, mul_ite, mul_zero]

theorem monomial_isUnit (n : ℤ) {z : ℚ_[7]} (hz : z ≠ 0) :
    IsUnit (monomial (r := r) (R := R) n z) := by
  apply isUnit_iff_exists_inv.mpr
  refine ⟨monomial (-n) z⁻¹, ?_⟩
  rw [monomial_mul, add_neg_cancel, mul_inv_cancel₀ hz, monomial_zero_one]

def constant : ℚ_[7] →+* ClosedAnnulus r R where
  toFun := monomial 0
  map_zero' := monomial_zero 0
  map_one' := rfl
  map_add' := monomial_add 0
  map_mul' z w := by simpa only [zero_add] using (monomial_mul (r := r) (R := R) 0 0 z w).symm

@[simp] theorem constant_norm (z : ℚ_[7]) : ‖constant (r := r) (R := R) z‖ = ‖z‖ := by
  change ‖monomial (r := r) (R := R) 0 z‖ = ‖z‖
  rw [monomial_norm]
  simp

instance : NormOneClass (ClosedAnnulus r R) where
  norm_one := by simpa only [map_one, norm_one] using constant_norm (r := r) (R := R) 1

instance : IsUltrametricDist (ClosedAnnulus r R) :=
  IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm
    (fun a b => norm_add_le_max a b)

def restrict {s S : ℝ} [Fact (0 < s)] [Fact (0 < S)]
    (hrs : r ≤ s) (hsS : s ≤ S) (hSR : S ≤ R) : ClosedAnnulus r R →+* ClosedAnnulus s S where
  toFun a := ⟨a.coeffs, a.inner.intermediate a.outer Fact.out hrs (hsS.trans hSR),
    a.inner.intermediate a.outer Fact.out (hrs.trans hsS) hSR⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

@[simp] theorem restrict_coeffs {s S : ℝ} [Fact (0 < s)] [Fact (0 < S)]
    (hrs : r ≤ s) (hsS : s ≤ S) (hSR : S ≤ R) (a : ClosedAnnulus r R) :
    (restrict hrs hsS hSR a).coeffs = a.coeffs := rfl

theorem restrict_norm_le {s S : ℝ} [Fact (0 < s)] [Fact (0 < S)]
    (hrs : r ≤ s) (hsS : s ≤ S) (hSR : S ≤ R) (a : ClosedAnnulus r R) :
    ‖restrict hrs hsS hSR a‖ ≤ ‖a‖ :=
  max_le (intermediate_gauss_le a.inner a.outer Fact.out hrs (hsS.trans hSR))
    (intermediate_gauss_le a.inner a.outer Fact.out (hrs.trans hsS) hSR)

theorem restrict_continuous {s S : ℝ} [Fact (0 < s)] [Fact (0 < S)]
    (hrs : r ≤ s) (hsS : s ≤ S) (hSR : S ≤ R) : Continuous (restrict hrs hsS hSR) := by
  apply LipschitzWith.continuous (K := 1)
  apply LipschitzWith.of_dist_le_mul
  intro a b
  simpa only [dist_eq_norm, ← map_sub, NNReal.coe_one, one_mul] using
    restrict_norm_le hrs hsS hSR (a - b)

end ClosedAnnulus
end Zeta7Annulus

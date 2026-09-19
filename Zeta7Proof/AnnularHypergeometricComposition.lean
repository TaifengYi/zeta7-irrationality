import Zeta7Proof.ClosedAnnulusMaps
import Zeta7Proof.AnnularLogCoefficientBound

/-! Convergent substitution of the original hypergeometric coefficients into
strict contractions in the actual complete annulus ring. Restrictions commute
with these sums. The specific T²/(PN³) contraction is a separate obligation. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
open Filter Topology
namespace Zeta7Annulus.ClosedAnnulus
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩
variable {r R : ℝ} [Fact (0 < r)] [Fact (0 < R)]

theorem hypergeometric_terms_summable (i : Fin 2) (s : ClosedAnnulus r R) (hs : ‖s‖ < 1) :
    Summable (fun n : ℕ => constant (annularHypergeometricCoefficient i n : ℚ_[7]) * s ^ n) := by
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  rw [tendsto_zero_iff_norm_tendsto_zero, Nat.cofinite_eq_atTop]
  have ht := (tendsto_self_mul_const_pow_of_lt_one (norm_nonneg s) hs).const_mul (12 : ℝ)
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) ?_ (by simpa using ht)
  filter_upwards [eventually_gt_atTop 0] with n hn
  calc
    _ ≤ ‖constant (r := r) (R := R) (annularHypergeometricCoefficient i n : ℚ_[7])‖ * ‖s ^ n‖ :=
      norm_mul_le _ _
    _ ≤ (12 * (n : ℝ)) * ‖s‖ ^ n := mul_le_mul
      (by simpa only [constant_norm] using annularHypergeometricCoefficient_norm_bound i n hn)
      (norm_pow_le _ _) (norm_nonneg _) (by positivity)
    _ = _ := by simp only [norm_eq]; ring

def hypergeometricCompose (i : Fin 2) (s : ClosedAnnulus r R) : ClosedAnnulus r R :=
  ∑' n : ℕ, constant (annularHypergeometricCoefficient i n : ℚ_[7]) * s ^ n

theorem hypergeometricCompose_hasSum (i : Fin 2) (s : ClosedAnnulus r R) (hs : ‖s‖ < 1) :
    HasSum (fun n : ℕ => constant (annularHypergeometricCoefficient i n : ℚ_[7]) * s ^ n)
      (hypergeometricCompose i s) := (hypergeometric_terms_summable i s hs).hasSum

theorem restrict_constant {s S : ℝ} [Fact (0 < s)] [Fact (0 < S)]
    (hrs : r ≤ s) (hsS : s ≤ S) (hSR : S ≤ R) (z : ℚ_[7]) :
    restrict hrs hsS hSR (constant z) = constant z := rfl

theorem restrict_hypergeometricCompose {s S : ℝ} [Fact (0 < s)] [Fact (0 < S)]
    (hrs : r ≤ s) (hsS : s ≤ S) (hSR : S ≤ R)
    (i : Fin 2) (z : ClosedAnnulus r R) (hz : ‖z‖ < 1) :
    restrict hrs hsS hSR (hypergeometricCompose i z) =
      hypergeometricCompose i (restrict hrs hsS hSR z) := by
  unfold hypergeometricCompose
  rw [(hypergeometric_terms_summable i z hz).map_tsum (restrict hrs hsS hSR)
    (restrict_continuous hrs hsS hSR)]
  apply tsum_congr
  intro n
  rw [map_mul, map_pow, restrict_constant]

def eulerAddHom : ClosedAnnulus r R →+ ClosedAnnulus r R where
  toFun := euler
  map_zero' := by ext k; simp [euler, bilateralEuler]
  map_add' a b := by ext k; simp [euler, bilateralEuler, mul_add]

theorem euler_continuous : Continuous (euler (r := r) (R := R)) := by
  apply LipschitzWith.continuous (K := 1)
  apply LipschitzWith.of_dist_le_mul
  intro a b
  have he := (eulerAddHom (r := r) (R := R)).map_sub a b
  change euler (a - b) = euler a - euler b at he
  rw [dist_eq_norm, ← he]
  simpa only [dist_eq_norm, NNReal.coe_one, one_mul] using euler_norm_le (a - b)

theorem euler_tsum {ι : Type*} {f : ι → ClosedAnnulus r R} (hf : Summable f) :
    euler (∑' i, f i) = ∑' i, euler (f i) := hf.map_tsum eulerAddHom euler_continuous

end Zeta7Annulus.ClosedAnnulus

import Zeta7Proof.Radius49GeometryCore
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Phase VI, R1: the functional-analytic bridge from coefficient decay to the
Gauss-completion disc algebra, independent of modular geometry.

* `exists_discAlgebra_of_decay`: a formal series whose coefficients decay at a radius
  `s > ρ` is the full expansion of an element of `DiscAlgebra ρ` (a convergent sum of monomials).
* `hasRadius49_of_HSeries_decay`: decay of `HSeries` on every disc of radius `< 49` implies
  `HasRadius49GeometricContinuation` (with the proved substitution identity).
* `hasRadius49_of_valueGroup_decay`: the same from decay on the value-group radii `7^r`,
  `r ∈ ℚ`, `r < 2` only.

No declaration here uses the published radius input. -/

set_option autoImplicit false
noncomputable section
namespace Zeta7Radius49
open Filter Topology UniformSpace PowerSeries
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- The coefficient map as an additive homomorphism of the completion. -/
def discCoeffHom (ρ : ℝ) (hρ : 0 < ρ) (n : ℕ) : DiscAlgebra ρ hρ →+ ℚ_[7] :=
  AddMonoidHom.ofMapSub (discCoeff ρ hρ n) (discCoeff_sub ρ hρ n)

/-- A monomial `a Xⁿ` as an element of the disc algebra. -/
def discMonomial (ρ : ℝ) (hρ : 0 < ρ) (n : ℕ) (a : ℚ_[7]) : DiscAlgebra ρ hρ :=
  (((WithAbs.equiv (discAbsolute ρ hρ)).symm (Polynomial.monomial n a) :
    DiscPolynomial ρ hρ) : DiscAlgebra ρ hρ)

theorem norm_discMonomial (ρ : ℝ) (hρ : 0 < ρ) (n : ℕ) (a : ℚ_[7]) :
    ‖discMonomial ρ hρ n a‖ = ‖a‖ * ρ ^ n := by
  rw [discMonomial, Completion.norm_coe]
  change discAbsolute ρ hρ (Polynomial.monomial n a) = _
  exact Polynomial.gaussNorm_monomial sevenAbsolute ρ n a

theorem discCoeff_discMonomial (ρ : ℝ) (hρ : 0 < ρ) (m n : ℕ) (a : ℚ_[7]) :
    discCoeff ρ hρ m (discMonomial ρ hρ n a) = if n = m then a else 0 := by
  rw [discMonomial, discCoeff_coe]
  change (Polynomial.monomial n a).coeff m = _
  rw [Polynomial.coeff_monomial]

/-- Decay at a larger radius implies decay at a smaller one. -/
theorem decay_mono {f : ℚ_[7]⟦X⟧} {ρ s : ℝ} (hρ : 0 ≤ ρ) (hρs : ρ ≤ s)
    (hf : Tendsto (fun n : ℕ => ‖coeff n f‖ * s ^ n) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => ‖coeff n f‖ * ρ ^ n) atTop (𝓝 0) :=
  squeeze_zero (fun n => mul_nonneg (norm_nonneg _) (pow_nonneg hρ n))
    (fun n => mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hρ hρs n) (norm_nonneg _)) hf

/-- **The bridge.** Coefficient decay at a radius `s > ρ` gives an element of the Gauss
completion at `ρ` whose full expansion is the given series. -/
theorem exists_discAlgebra_of_decay {ρ s : ℝ} (hρ : 0 < ρ) (hρs : ρ < s)
    (f : ℚ_[7]⟦X⟧) (hf : Tendsto (fun n : ℕ => ‖coeff n f‖ * s ^ n) atTop (𝓝 0)) :
    ∃ F : DiscAlgebra ρ hρ, discSeries ρ hρ F = f := by
  have hs : 0 < s := hρ.trans hρs
  obtain ⟨C, hC⟩ := hf.bddAbove_range
  have hC' (n : ℕ) : ‖coeff n f‖ * s ^ n ≤ C := hC ⟨n, rfl⟩
  have hr0 : 0 ≤ ρ / s := div_nonneg hρ.le hs.le
  have hr1 : ρ / s < 1 := (div_lt_one hs).mpr hρs
  let term : ℕ → DiscAlgebra ρ hρ := fun n => discMonomial ρ hρ n (coeff n f)
  have hbound (n : ℕ) : ‖term n‖ ≤ C * (ρ / s) ^ n := by
    have hsn : 0 < s ^ n := pow_pos hs n
    rw [norm_discMonomial, div_pow]
    calc
      ‖coeff n f‖ * ρ ^ n = (‖coeff n f‖ * s ^ n) * (ρ ^ n / s ^ n) := by
        field_simp
      _ ≤ C * (ρ ^ n / s ^ n) :=
        mul_le_mul_of_nonneg_right (hC' n) (div_nonneg (pow_nonneg hρ.le n) hsn.le)
  have hsum : Summable term :=
    Summable.of_norm_bounded ((summable_geometric_of_lt_one hr0 hr1).mul_left C) hbound
  refine ⟨∑' n, term n, ?_⟩
  ext m
  rw [discSeries_coeff]
  have h1 : HasSum (fun n => discCoeffHom ρ hρ m (term n))
      (discCoeffHom ρ hρ m (∑' n, term n)) :=
    hsum.hasSum.map (discCoeffHom ρ hρ m) (discCoeff_continuous ρ hρ m)
  have h2 : HasSum (fun n => discCoeffHom ρ hρ m (term n)) (coeff m f) := by
    have : (fun n => discCoeffHom ρ hρ m (term n)) =
        fun n => if n = m then coeff m f else 0 := by
      funext n
      change discCoeff ρ hρ m (discMonomial ρ hρ n (coeff n f)) = _
      rw [discCoeff_discMonomial]
      split_ifs with h
      · rw [h]
      · rfl
    rw [this]
    exact hasSum_ite_eq m (coeff m f)
  exact h1.unique h2

end Zeta7Radius49

namespace Zeta7Main
open PowerSeries Filter Topology Zeta7Radius49
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- **R1 endpoint.** Coefficient decay of `HSeries` on every disc of radius below `49`
implies the geometric continuation statement. -/
theorem hasRadius49_of_HSeries_decay
    (h : ∀ ρ : ℝ, 0 < ρ → ρ < 49 →
      Tendsto (fun n : ℕ => ‖coeff n HSeries‖ * ρ ^ n) atTop (𝓝 0)) :
    HasRadius49GeometricContinuation := by
  intro ρ hρ hρ49
  obtain ⟨F, hF⟩ := exists_discAlgebra_of_decay hρ (by linarith : ρ < (ρ + 49) / 2) HSeries
    (h _ (by linarith) (by linarith))
  exact ⟨F, by rw [hF]; exact HSeries_subst_xSeries⟩

/-- **R1 endpoint, value-group form.** It suffices to have decay on the discs of radius
`7^r` with `r` rational and `r < 2` (radii in the value group of `ℂ₇`). -/
theorem hasRadius49_of_valueGroup_decay
    (h : ∀ r : ℚ, r < 2 →
      Tendsto (fun n : ℕ => ‖coeff n HSeries‖ * ((7 : ℝ) ^ (r : ℝ)) ^ n) atTop (𝓝 0)) :
    HasRadius49GeometricContinuation := by
  intro ρ hρ hρ49
  have hlog : Real.logb 7 ρ < 2 := by
    rw [Real.logb_lt_iff_lt_rpow (by norm_num) hρ]
    norm_num
    exact hρ49
  obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn hlog
  have hρs : ρ < (7 : ℝ) ^ (r : ℝ) := (Real.logb_lt_iff_lt_rpow (by norm_num) hρ).mp hr1
  obtain ⟨F, hF⟩ := exists_discAlgebra_of_decay hρ hρs HSeries (h r (by exact_mod_cast hr2))
  exact ⟨F, by rw [hF]; exact HSeries_subst_xSeries⟩

end Zeta7Main

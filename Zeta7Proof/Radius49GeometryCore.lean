import Zeta7Proof.Radius49FormalIdentification
import Mathlib.RingTheory.Polynomial.GaussNorm
import Mathlib.Analysis.Normed.Ring.WithAbs
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.Normed.Group.Uniform

/-! An independent closed-disc algebra: the Gauss-norm completion of polynomials.
Its definition contains no assertion about coefficients of HSeries, nor any
coefficient-decay field. Decay is proved from density of polynomials below. -/

set_option autoImplicit false
noncomputable section
namespace Zeta7Radius49
open Filter Topology UniformSpace PowerSeries
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- The seven-adic norm, bundled independently of any series. -/
def sevenAbsolute : AbsoluteValue ℚ_[7] ℝ :=
  IsAbsoluteValue.toAbsoluteValue (norm : ℚ_[7] → ℝ)

/-- The multiplicative polynomial Gauss absolute value at a positive real radius. -/
def discAbsolute (ρ : ℝ) (hρ : 0 < ρ) : AbsoluteValue (Polynomial ℚ_[7]) ℝ := by
  letI : IsAbsoluteValue (Polynomial.gaussNorm sevenAbsolute ρ) :=
    Polynomial.gaussNorm_isAbsoluteValue IsUltrametricDist.isNonarchimedean_norm hρ
  exact IsAbsoluteValue.toAbsoluteValue (Polynomial.gaussNorm sevenAbsolute ρ)

/-- Polynomials equipped with the radius-ρ Gauss norm. -/
abbrev DiscPolynomial (ρ : ℝ) (hρ : 0 < ρ) := WithAbs (discAbsolute ρ hρ)

instance discPolynomialNormedCommRing (ρ : ℝ) (hρ : 0 < ρ) :
    NormedCommRing (DiscPolynomial ρ hρ) where
  __ : NormedRing (DiscPolynomial ρ hρ) := inferInstance
  mul_comm := mul_comm

instance discPolynomialNormedAlgebra (ρ : ℝ) (hρ : 0 < ρ) :
    NormedAlgebra ℚ_[7] (DiscPolynomial ρ hρ) where
  norm_smul_le c P := by
    change discAbsolute ρ hρ (c • P.ofAbs) ≤ ‖c‖ * discAbsolute ρ hρ P.ofAbs
    rw [← Polynomial.C_mul', map_mul]
    have hc : discAbsolute ρ hρ (Polynomial.C c) = ‖c‖ :=
      Polynomial.gaussNorm_C sevenAbsolute ρ c
    rw [hc]

/-- The generalized one-variable Tate algebra, constructed by metric completion.
For arbitrary positive real ρ this is the Gauss completion, without assuming
that ρ belongs to the value group. -/
abbrev DiscAlgebra (ρ : ℝ) (hρ : 0 < ρ) := Completion (DiscPolynomial ρ hρ)

/-- The polynomial coefficient map before completion. -/
def polynomialCoeff (ρ : ℝ) (hρ : 0 < ρ) (n : ℕ) :
    DiscPolynomial ρ hρ →+ ℚ_[7] :=
  (Polynomial.lcoeff ℚ_[7] n).toAddMonoidHom.comp
    (WithAbs.equiv (discAbsolute ρ hρ)).toAddMonoidHom

theorem polynomialCoeff_bound (ρ : ℝ) (hρ : 0 < ρ) (n : ℕ)
    (P : DiscPolynomial ρ hρ) :
    ‖polynomialCoeff ρ hρ n P‖ * ρ ^ n ≤ ‖P‖ := by
  exact Polynomial.le_gaussNorm sevenAbsolute P.ofAbs hρ.le n

theorem polynomialCoeff_uniformContinuous (ρ : ℝ) (hρ : 0 < ρ) (n : ℕ) :
    UniformContinuous (polynomialCoeff ρ hρ n) := by
  apply (AddMonoidHomClass.lipschitz_of_bound
    (polynomialCoeff ρ hρ n) (ρ ^ n)⁻¹ ?_).uniformContinuous
  intro P
  have hb := polynomialCoeff_bound ρ hρ n P
  calc
    ‖polynomialCoeff ρ hρ n P‖ ≤ ‖P‖ / ρ ^ n := (le_div_iff₀ (pow_pos hρ n)).mpr hb
    _ = (ρ ^ n)⁻¹ * ‖P‖ := by ring

/-- Coefficients are continuous extensions of polynomial coefficient maps. -/
def discCoeff (ρ : ℝ) (hρ : 0 < ρ) (n : ℕ) : DiscAlgebra ρ hρ → ℚ_[7] :=
  Completion.extension (polynomialCoeff ρ hρ n)

theorem discCoeff_continuous (ρ : ℝ) (hρ : 0 < ρ) (n : ℕ) :
    Continuous (discCoeff ρ hρ n) := Completion.continuous_extension

theorem discCoeff_coe (ρ : ℝ) (hρ : 0 < ρ) (n : ℕ) (P : DiscPolynomial ρ hρ) :
    discCoeff ρ hρ n (P : DiscAlgebra ρ hρ) = polynomialCoeff ρ hρ n P :=
  Completion.extension_coe (polynomialCoeff_uniformContinuous ρ hρ n) P

theorem discCoeff_sub (ρ : ℝ) (hρ : 0 < ρ) (n : ℕ) (F G : DiscAlgebra ρ hρ) :
    discCoeff ρ hρ n (F - G) = discCoeff ρ hρ n F - discCoeff ρ hρ n G := by
  induction F, G using Completion.induction_on₂ with
  | hp =>
    exact isClosed_eq ((discCoeff_continuous ρ hρ n).comp (continuous_fst.sub continuous_snd))
      (((discCoeff_continuous ρ hρ n).comp continuous_fst).sub
        ((discCoeff_continuous ρ hρ n).comp continuous_snd))
  | ih P Q =>
    rw [← Completion.coe_sub, discCoeff_coe, discCoeff_coe, discCoeff_coe, map_sub]

theorem discCoeff_bound (ρ : ℝ) (hρ : 0 < ρ) (n : ℕ) (F : DiscAlgebra ρ hρ) :
    ‖discCoeff ρ hρ n F‖ * ρ ^ n ≤ ‖F‖ := by
  induction F using Completion.induction_on with
  | hp => exact isClosed_le ((discCoeff_continuous ρ hρ n).norm.mul_const _) continuous_norm
  | ih P =>
    rw [discCoeff_coe, Completion.norm_coe]
    exact polynomialCoeff_bound ρ hρ n P

/-- Gauss-norm coefficient decay follows from approximation by polynomials. -/
theorem discCoeff_decay (ρ : ℝ) (hρ : 0 < ρ) (F : DiscAlgebra ρ hρ) :
    Tendsto (fun n : ℕ => ‖discCoeff ρ hρ n F‖ * ρ ^ n) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨P, hP⟩ := Completion.denseRange_coe.exists_dist_lt F hε
  refine ⟨P.ofAbs.natDegree + 1, fun n hn => ?_⟩
  have hz : polynomialCoeff ρ hρ n P = 0 := by
    change P.ofAbs.coeff n = 0
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  have heq : discCoeff ρ hρ n F = discCoeff ρ hρ n (F - (P : DiscAlgebra ρ hρ)) := by
    rw [discCoeff_sub, discCoeff_coe, hz, sub_zero]
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (mul_nonneg (norm_nonneg _) (pow_nonneg hρ.le n)), heq]
  exact (discCoeff_bound ρ hρ n _).trans_lt (by simpa only [dist_eq_norm] using hP)

/-- The full formal expansion of a Gauss-completion element. -/
def discSeries (ρ : ℝ) (hρ : 0 < ρ) (F : DiscAlgebra ρ hρ) : ℚ_[7]⟦X⟧ :=
  PowerSeries.mk (fun n => discCoeff ρ hρ n F)

theorem discSeries_coeff (ρ : ℝ) (hρ : 0 < ρ) (F : DiscAlgebra ρ hρ) (n : ℕ) :
    PowerSeries.coeff n (discSeries ρ hρ F) = discCoeff ρ hρ n F := PowerSeries.coeff_mk _ _

theorem discSeries_decay (ρ : ℝ) (hρ : 0 < ρ) (F : DiscAlgebra ρ hρ) :
    Tendsto (fun n : ℕ => ‖PowerSeries.coeff n (discSeries ρ hρ F)‖ * ρ ^ n)
      atTop (𝓝 0) := by
  simpa only [discSeries_coeff] using discCoeff_decay ρ hρ F

/-- The full coefficient expansion is faithful, by polynomial density and the
finite maximum defining the polynomial Gauss norm. -/
theorem discSeries_injective (ρ : ℝ) (hρ : 0 < ρ) :
    Function.Injective (discSeries ρ hρ) := by
  intro F G hFG
  have hz (n : ℕ) : discCoeff ρ hρ n (F - G) = 0 := by
    rw [discCoeff_sub]
    apply sub_eq_zero.mpr
    simpa only [discSeries_coeff] using congrArg (PowerSeries.coeff n) hFG
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  by_contra! hpos
  obtain ⟨P, hP⟩ := Completion.denseRange_coe.exists_dist_lt
    (F - G) (by positivity : 0 < ‖F - G‖ / 3)
  obtain ⟨n, hn⟩ := Polynomial.exists_eq_gaussNorm sevenAbsolute ρ P.ofAbs
  have hpbound : ‖P‖ ≤ ‖F - G - (P : DiscAlgebra ρ hρ)‖ := by
    have hb := discCoeff_bound ρ hρ n (F - G - (P : DiscAlgebra ρ hρ))
    rw [discCoeff_sub, hz, zero_sub, norm_neg, discCoeff_coe] at hb
    change Polynomial.gaussNorm sevenAbsolute ρ P.ofAbs ≤ _
    rw [hn]
    exact hb
  have htri : ‖F - G‖ ≤ ‖F - G - (P : DiscAlgebra ρ hρ)‖ + ‖P‖ := by
    simpa only [sub_add_cancel, Completion.norm_coe] using
      norm_add_le (F - G - (P : DiscAlgebra ρ hρ)) (P : DiscAlgebra ρ hρ)
  rw [dist_eq_norm] at hP
  linarith

end Zeta7Radius49

namespace Zeta7Main
open PowerSeries Zeta7Radius49
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- An independent Gauss-completion representative on every smaller closed disc,
with a complete cusp-substitution identity. This proposition contains no decay
condition; `discSeries_decay` proves that property for every completion element. -/
def HasRadius49GeometricContinuation : Prop :=
  ∀ (ρ : ℝ) (hρ : 0 < ρ), ρ < 49 →
    ∃ F : DiscAlgebra ρ hρ,
      (discSeries ρ hρ F).subst (xSeries.map (algebraMap ℚ ℚ_[7])) =
        ASeries.map (algebraMap ℚ ℚ_[7]) *
          (GSeries.map (algebraMap ℚ ℚ_[7]) + C eta)

end Zeta7Main

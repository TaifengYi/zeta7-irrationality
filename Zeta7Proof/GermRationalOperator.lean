import Zeta7Proof.GermRationalCalculus

/-! The rational coefficients of the actual operator, without any radius input. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open scoped LaurentSeries RatFunc
open PowerSeries
namespace Zeta7Germ

def P : RatFunc ℂ := 1 + 13 * RatFunc.X + 49 * RatFunc.X ^ 2
def V : RatFunc ℂ := 8 * RatFunc.X * (1 + 16 * RatFunc.X + 49 * RatFunc.X ^ 2) / P ^ 2
def R : RatFunc ℂ := RatFunc.X * (1 + 10 * RatFunc.X) / P
def L (f : RatFunc ℂ) : RatFunc ℂ :=
  rationalD (rationalD (rationalD f)) - V * rationalD f - rationalD V * f / 2
def riccati (u : RatFunc ℂ) : RatFunc ℂ :=
  rationalD (rationalD u) + 3 * u * rationalD u + u ^ 3 - V * u - rationalD V / 2

def complexSeries (f : ℚ⟦X⟧) : ℂ⸨X⸩ := (f.map (algebraMap ℚ ℂ) : ℂ⟦X⟧)

theorem complexSeries_add (f g : ℚ⟦X⟧) : complexSeries (f + g) =
    complexSeries f + complexSeries g := by simp [complexSeries]
theorem complexSeries_mul (f g : ℚ⟦X⟧) : complexSeries (f * g) =
    complexSeries f * complexSeries g := by simp [complexSeries]
theorem complexSeries_euler (f : ℚ⟦X⟧) : complexSeries (Zeta7Common.euler f) =
    laurentD (complexSeries f) := by
  rw [complexSeries, Zeta7Common.map_euler, ← laurentD_powerSeries]
  rfl

theorem embed_X : embed RatFunc.X = (X : ℂ⟦X⟧) := by
  rw [← RatFunc.algebraMap_X, ← RatFunc.coePolynomial_eq_algebraMap, embed_polynomial]
  simp

theorem embed_P : embed P = complexSeries Zeta7Common.shortP := by
  simp [P, Zeta7Common.shortP_value, complexSeries, map_ofNat, embed_X]

theorem P_ne_zero : P ≠ 0 := by
  intro h
  have hh := embed_P
  rw [h, map_zero] at hh
  have hs : Zeta7Common.shortP.map (algebraMap ℚ ℂ) = 0 :=
    HahnSeries.ofPowerSeries_injective (hh.symm.trans (map_zero _).symm)
  have hz := congrArg (constantCoeff (R := ℂ)) hs
  norm_num [Zeta7Common.shortP_value] at hz

theorem embed_V : embed V = complexSeries Zeta7Common.rationalPotential := by
  rw [V, map_div₀, map_pow]
  apply (div_eq_iff (pow_ne_zero 2 ((map_ne_zero embed).mpr P_ne_zero))).mpr
  have h := congrArg complexSeries Zeta7Common.rationalPotential_cleared
  simp only [complexSeries_mul] at h
  have hp : complexSeries (Zeta7Common.shortP ^ 2) = embed P ^ 2 := by
    simp [complexSeries, embed_P]
  rw [hp] at h
  simpa [map_mul, map_pow, map_add, map_one, map_ofNat, embed_X,
    complexSeries, mul_comm] using h.symm

theorem embed_R : embed R = complexSeries Zeta7Common.rationalForcing := by
  have h := congrArg complexSeries Zeta7Common.rationalForcing_cleared
  rw [complexSeries_mul, ← embed_P] at h
  rw [R, map_div₀]
  apply (div_eq_iff ((map_ne_zero embed).mpr P_ne_zero)).mpr
  rw [mul_comm]
  simpa [complexSeries, map_mul, map_add, map_ofNat, embed_X, mul_comm] using h.symm

end Zeta7Germ

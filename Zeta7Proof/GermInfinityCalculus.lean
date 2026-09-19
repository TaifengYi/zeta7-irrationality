import Zeta7Proof.N2LocalRiccati
import Zeta7Proof.GermLPObstruction

/-! Substitution x = 1/t is performed on rational functions before Laurent expansion. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open scoped RatFunc LaurentSeries nonZeroDivisors
open PowerSeries Polynomial
namespace Zeta7Germ

theorem reciprocal_aeval_injective :
    Function.Injective (aeval ((RatFunc.X : RatFunc ℂ)⁻¹) : Polynomial ℂ → RatFunc ℂ) := by
  apply transcendental_iff_injective.mp
  intro h
  exact RatFunc.transcendental_X (IsAlgebraic.inv_iff.mp h)

def reciprocal : RatFunc ℂ →+* RatFunc ℂ :=
  RatFunc.liftRingHom (aeval ((RatFunc.X : RatFunc ℂ)⁻¹)).toRingHom (by
    intro p hp
    change aeval ((RatFunc.X : RatFunc ℂ)⁻¹) p ∈ (RatFunc ℂ)⁰
    simp only [mem_nonZeroDivisors_iff_ne_zero] at hp ⊢
    intro hz
    exact hp (reciprocal_aeval_injective (hz.trans (map_zero _).symm)))

theorem reciprocal_polynomial (p : Polynomial ℂ) :
    reciprocal (p : RatFunc ℂ) = aeval ((RatFunc.X : RatFunc ℂ)⁻¹) p := by
  simp [reciprocal, RatFunc.coePolynomial_eq_algebraMap]

theorem reciprocal_X : reciprocal RatFunc.X = (RatFunc.X : RatFunc ℂ)⁻¹ := by
  rw [← RatFunc.algebraMap_X, ← RatFunc.coePolynomial_eq_algebraMap, reciprocal_polynomial]
  simp

theorem reciprocal_C (a : ℂ) : reciprocal (RatFunc.C a) = RatFunc.C a := by
  rw [← RatFunc.algebraMap_C, ← RatFunc.coePolynomial_eq_algebraMap, reciprocal_polynomial]
  simp

theorem rationalD_X_inv : rationalD ((RatFunc.X : RatFunc ℂ)⁻¹) = -RatFunc.X⁻¹ := by
  rw [Derivation.leibniz_inv, rationalD_X, smul_eq_mul]
  field_simp

theorem reciprocal_rationalD_polynomial (p : Polynomial ℂ) :
    reciprocal (rationalD (p : RatFunc ℂ)) = -rationalD (reciprocal (p : RatFunc ℂ)) := by
  rw [rationalD_polynomial, reciprocal_polynomial, reciprocal_polynomial, Derivation.map_aeval]
  simp [rationalD_X_inv, smul_eq_mul, mul_comm]

theorem reciprocal_rationalD (f : RatFunc ℂ) :
    reciprocal (rationalD f) = -rationalD (reciprocal f) := by
  induction f using RatFunc.induction_on with
  | f p q hq =>
    simp only [← RatFunc.coePolynomial_eq_algebraMap]
    rw [Derivation.leibniz_div]
    simp only [smul_eq_mul, map_mul, map_sub, map_pow, map_inv₀, map_div₀,
      reciprocal_rationalD_polynomial, Derivation.leibniz_div]
    ring

def infinityExpansion : RatFunc ℂ →+* ℂ⸨X⸩ := embed.comp reciprocal

theorem infinityExpansion_rationalD (f : RatFunc ℂ) :
    infinityExpansion (rationalD f) = -laurentD (infinityExpansion f) := by
  change embed (reciprocal (rationalD f)) = _
  rw [reciprocal_rationalD, map_neg, embed_rationalD]
  rfl

theorem infinityExpansion_X : infinityExpansion RatFunc.X = HahnSeries.single (-1 : ℤ) 1 := by
  change embed (reciprocal RatFunc.X) = _
  rw [reciprocal_X, map_inv₀, embed_X]
  simp [HahnSeries.ofPowerSeries_X, HahnSeries.inv_single]

theorem infinityExpansion_C (a : ℂ) : infinityExpansion (RatFunc.C a) = HahnSeries.C a := by
  change embed (reciprocal (RatFunc.C a)) = _
  rw [reciprocal_C, embed_C]

theorem infinityExpansion_monomial (n : ℕ) (a : ℂ) :
    infinityExpansion ((Polynomial.monomial n a : Polynomial ℂ) : RatFunc ℂ) =
      HahnSeries.single (-(n : ℤ)) a := by
  rw [← Polynomial.C_mul_X_pow_eq_monomial, RatFunc.coePolynomial_eq_algebraMap,
    map_mul, map_pow, RatFunc.algebraMap_C, RatFunc.algebraMap_X,
    map_mul, map_pow, infinityExpansion_C, infinityExpansion_X]
  simp [HahnSeries.C_apply, HahnSeries.single_pow, HahnSeries.single_mul_single]

theorem infinityExpansion_polynomial_coeff (p : Polynomial ℂ) (n : ℕ) :
    (infinityExpansion (p : RatFunc ℂ)).coeff (-(n : ℤ)) = p.coeff n := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simpa [RatFunc.coePolynomial_eq_algebraMap, map_add] using congrArg₂ (· + ·) hp hq
  | monomial m a =>
    rw [infinityExpansion_monomial]
    simp [HahnSeries.coeff_single, Polynomial.coeff_monomial, eq_comm]

theorem polynomial_zero_of_infinity_decay (p : Polynomial ℂ)
    (hp : lowerBound (infinityExpansion (p : RatFunc ℂ)) 1) : p = 0 := by
  ext n
  rw [Polynomial.coeff_zero, ← infinityExpansion_polynomial_coeff]
  exact hp (-(n : ℤ)) (by omega)

def infinityDen : ℂ⟦X⟧ := PowerSeries.C 49 + PowerSeries.C 13 * PowerSeries.X + PowerSeries.X ^ 2
def infinityVRegular : ℂ⟦X⟧ :=
  PowerSeries.C 8 * PowerSeries.X *
    (PowerSeries.C 49 + PowerSeries.C 16 * PowerSeries.X + PowerSeries.X ^ 2) *
    infinityDen⁻¹ ^ 2

theorem infinity_V_rational : reciprocal V =
    8 * RatFunc.X * (49 + 16 * RatFunc.X + RatFunc.X ^ 2) /
      (49 + 13 * RatFunc.X + RatFunc.X ^ 2) ^ 2 := by
  have hp : (49 + 13 * RatFunc.X + RatFunc.X ^ 2 : RatFunc ℂ) ≠ 0 := by
    have he : reciprocal P = (49 + 13 * RatFunc.X + RatFunc.X ^ 2) / RatFunc.X ^ 2 := by
      simp only [P, map_add, map_mul, map_pow, map_one, map_ofNat, reciprocal_X]
      field_simp [RatFunc.X_ne_zero]
      ring
    have hn : reciprocal P ≠ 0 := (map_ne_zero reciprocal).mpr P_ne_zero
    intro hz
    rw [he, hz, zero_div] at hn
    exact hn rfl
  simp only [V, P, map_div₀, map_add, map_mul, map_pow, map_one, map_ofNat, reciprocal_X]
  field_simp [RatFunc.X_ne_zero, hp]
  ring

theorem infinity_V_powerSeries : infinityExpansion V = (infinityVRegular : ℂ⸨X⸩) := by
  have hd : PowerSeries.constantCoeff infinityDen ≠ 0 := by norm_num [infinityDen]
  change embed (reciprocal V) = _
  rw [infinity_V_rational]
  simp only [infinityVRegular, PowerSeries.coe_mul, map_pow, coe_powerSeries_inv _ hd]
  simp [infinityDen, embed_X, map_ofNat, div_eq_mul_inv, inv_pow]

theorem infinity_V_lowerBound : lowerBound (infinityExpansion V) 1 := by
  rw [infinity_V_powerSeries]
  apply lowerBound_powerSeries_one
  simp [infinityVRegular]

end Zeta7Germ

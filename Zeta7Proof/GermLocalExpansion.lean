import Zeta7Proof.GermLocalCalculus

/-! Translation to an arbitrary finite point, followed by the canonical Laurent map. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open scoped LaurentSeries RatFunc
open HahnSeries
namespace Zeta7Germ

def localExpansion (a : ℂ) : RatFunc ℂ →+* ℂ⸨X⸩ :=
  embed.comp (RatFunc.laurent a).toRingHom

theorem localExpansion_injective (a : ℂ) : Function.Injective (localExpansion a) :=
  embed_injective.comp (RatFunc.laurent_injective a)

def localD (a : ℂ) (f : ℂ⸨X⸩) : ℂ⸨X⸩ :=
  (HahnSeries.C a + single (1 : ℤ) 1) * ordinaryD f

theorem localD_div (a : ℂ) (f g : ℂ⸨X⸩) :
    localD a (f / g) = g⁻¹ ^ 2 * (g * localD a f - f * localD a g) := by
  simp only [localD, ordinaryD, Derivation.leibniz_div, smul_eq_mul]
  ring

theorem localD_coeff (a : ℂ) (f : ℂ⸨X⸩) (n : ℤ) :
    (localD a f).coeff n =
      a * ((n + 1 : ℤ) : ℂ) * f.coeff (n + 1) + (n : ℂ) * f.coeff n := by
  simp [localD, Derivation.smul_apply, smul_eq_mul, add_mul, HahnSeries.C_apply,
    coeff_single_mul, ordinaryD_coeff, mul_assoc]

theorem lowerBound_localD (a : ℂ) {f : ℂ⸨X⸩} {n : ℤ} (hf : lowerBound f n) :
    lowerBound (localD a f) (n - 1) := by
  intro k hk
  rw [localD_coeff, hf (k + 1) (by omega), hf k (by omega)]
  ring

theorem localD_leading (a : ℂ) {f : ℂ⸨X⸩} {n : ℤ} (hf : lowerBound f n) :
    (localD a f).coeff (n - 1) = a * (n : ℂ) * f.coeff n := by
  rw [localD_coeff, hf (n - 1) (by omega)]
  simp

theorem localD_two_leading (a : ℂ) {f : ℂ⸨X⸩} {n : ℤ} (hf : lowerBound f n) :
    (localD a (localD a f)).coeff (n - 2) =
      a ^ 2 * (n : ℂ) * ((n : ℂ) - 1) * f.coeff n := by
  have hn : n - 2 = (n - 1) - 1 := by omega
  rw [hn, localD_leading a (lowerBound_localD a hf), localD_leading a hf]
  push_cast
  ring

theorem localD_three_leading (a : ℂ) {f : ℂ⸨X⸩} {n : ℤ} (hf : lowerBound f n) :
    (localD a (localD a (localD a f))).coeff (n - 3) =
      a ^ 3 * (n : ℂ) * ((n : ℂ) - 1) * ((n : ℂ) - 2) * f.coeff n := by
  have hn : n - 3 = ((n - 1) - 1) - 1 := by omega
  rw [hn, localD_leading a (lowerBound_localD a (lowerBound_localD a hf)),
    localD_leading a (lowerBound_localD a hf), localD_leading a hf]
  push_cast
  ring

theorem ordinaryD_polynomial (p : Polynomial ℂ) :
    ordinaryD (embed (p : RatFunc ℂ)) = embed (p.derivative : RatFunc ℂ) := by
  change single (-1 : ℤ) (1 : ℂ) * laurentD (embed (p : RatFunc ℂ)) = _
  rw [laurentD_polynomial]
  simp only [RatFunc.coePolynomial_eq_algebraMap, map_mul]
  rw [← mul_assoc]
  have hx : embed ((Polynomial.X : Polynomial ℂ) : RatFunc ℂ) = single (1 : ℤ) 1 := by
    rw [embed_polynomial]
    simp
  simp only [RatFunc.coePolynomial_eq_algebraMap] at hx
  rw [hx]
  simp [single_mul_single]

theorem derivative_taylor (a : ℂ) (p : Polynomial ℂ) :
    (Polynomial.taylor a p).derivative = Polynomial.taylor a p.derivative := by
  simp [Polynomial.taylor_apply, Polynomial.derivative_comp]

theorem localExpansion_polynomial (a : ℂ) (p : Polynomial ℂ) :
    localExpansion a (p : RatFunc ℂ) = embed ((Polynomial.taylor a p : Polynomial ℂ) : RatFunc ℂ) := by
  simp [localExpansion]

theorem localExpansion_rationalD_polynomial (a : ℂ) (p : Polynomial ℂ) :
    localExpansion a (rationalD (p : RatFunc ℂ)) = localD a (localExpansion a (p : RatFunc ℂ)) := by
  rw [rationalD_polynomial, localExpansion_polynomial, localExpansion_polynomial]
  simp only [localD, Derivation.smul_apply, smul_eq_mul, ordinaryD_polynomial,
    derivative_taylor, Polynomial.taylor_mul, Polynomial.taylor_X, map_mul, map_add]
  simp only [RatFunc.coePolynomial_eq_algebraMap, map_mul, map_add]
  rw [← RatFunc.coePolynomial_eq_algebraMap, embed_polynomial]
  simp [embed_C, RatFunc.algebraMap_C, add_comm]

theorem localExpansion_rationalD (a : ℂ) (f : RatFunc ℂ) :
    localExpansion a (rationalD f) = localD a (localExpansion a f) := by
  induction f using RatFunc.induction_on with
  | f p q hq =>
    simp only [← RatFunc.coePolynomial_eq_algebraMap]
    simp only [Derivation.leibniz_div, localD_div, smul_eq_mul, map_mul, map_sub, map_pow,
      map_inv₀, map_div₀, localExpansion_rationalD_polynomial]

end Zeta7Germ

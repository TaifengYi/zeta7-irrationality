import Zeta7Proof.GermEulerCalculus

/-! Euler derivation on C(x), justified through its canonical Laurent embedding. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open scoped LaurentSeries RatFunc
open PowerSeries
namespace Zeta7Germ

abbrev embed : RatFunc ℂ →+* ℂ⸨X⸩ := algebraMap _ _

theorem embed_injective : Function.Injective embed := RingHom.injective _

theorem embed_polynomial (p : Polynomial ℂ) :
    embed (p : RatFunc ℂ) = (p : ℂ⟦X⟧) := (RatFunc.coe_coe p).symm

theorem embed_C (a : ℂ) : embed (RatFunc.C a) = HahnSeries.C a := by
  rw [← RatFunc.algebraMap_C, ← RatFunc.coePolynomial_eq_algebraMap, embed_polynomial]
  simp

theorem laurentD_polynomial (p : Polynomial ℂ) :
    laurentD (embed (p : RatFunc ℂ)) =
      embed ((Polynomial.X * p.derivative : Polynomial ℂ) : RatFunc ℂ) := by
  simp only [embed_polynomial]
  rw [laurentD_powerSeries]
  congr 1
  simp [Zeta7Common.euler, PowerSeries.derivative_coe]

def rationalEuler (f : RatFunc ℂ) : RatFunc ℂ :=
  ((Polynomial.X * f.num.derivative : Polynomial ℂ) : RatFunc ℂ) /
      (f.denom : RatFunc ℂ) -
    (f.num : RatFunc ℂ) *
      ((Polynomial.X * f.denom.derivative : Polynomial ℂ) : RatFunc ℂ) /
        (f.denom : RatFunc ℂ) ^ 2

theorem embed_rationalEuler (f : RatFunc ℂ) :
    embed (rationalEuler f) = laurentD (embed f) := by
  conv_rhs => rw [← RatFunc.num_div_denom f]
  simp only [← RatFunc.coePolynomial_eq_algebraMap]
  simp only [rationalEuler, map_sub, map_div₀, map_mul, map_pow,
    Derivation.leibniz_div, smul_eq_mul, laurentD_polynomial]
  field_simp
  <;> ring

theorem rationalEuler_add (f g : RatFunc ℂ) :
    rationalEuler (f + g) = rationalEuler f + rationalEuler g := by
  apply embed_injective
  simp only [map_add, embed_rationalEuler]

theorem rationalEuler_mul (f g : RatFunc ℂ) :
    rationalEuler (f * g) = f * rationalEuler g + g * rationalEuler f := by
  apply embed_injective
  simp only [map_add, map_mul, embed_rationalEuler, Derivation.leibniz, smul_eq_mul]

theorem rationalEuler_smul (a : ℂ) (f : RatFunc ℂ) :
    rationalEuler (a • f) = a • rationalEuler f := by
  apply embed_injective
  simp only [Algebra.smul_def, map_mul, embed_rationalEuler, Derivation.leibniz,
    smul_eq_mul]
  have hc : embed ((algebraMap ℂ (RatFunc ℂ)) a) = HahnSeries.C a := embed_C a
  rw [hc]
  have hz : laurentD (HahnSeries.C a) = 0 := laurentEuler_C a
  rw [hz]
  simp

theorem rationalEuler_one : rationalEuler 1 = 0 := by
  apply embed_injective
  simp only [embed_rationalEuler, map_one, map_zero, Derivation.map_one_eq_zero]

def rationalD : Derivation ℂ (RatFunc ℂ) (RatFunc ℂ) where
  toFun := rationalEuler
  map_add' := rationalEuler_add
  map_smul' := rationalEuler_smul
  map_one_eq_zero' := rationalEuler_one
  leibniz' f g := by simpa [smul_eq_mul] using rationalEuler_mul f g

theorem embed_rationalD (f : RatFunc ℂ) :
    embed (rationalD f) = laurentD (embed f) := embed_rationalEuler f

theorem rationalD_polynomial (p : Polynomial ℂ) :
    rationalD (p : RatFunc ℂ) =
      ((Polynomial.X * p.derivative : Polynomial ℂ) : RatFunc ℂ) := by
  apply embed_injective
  rw [embed_rationalD, laurentD_polynomial]

end Zeta7Germ

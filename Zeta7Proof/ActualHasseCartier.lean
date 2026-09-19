import Zeta7Proof.ActualHasseRoots

set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

/-! Exact Cartier calculus and kernel for the original Hasse quotient. -/


/- Source section: HasseCartierSeries. -/

/-! Coefficient extraction and the exact Euler kernel on formal power series.
These results do not assert a rational-function Cartier kernel. -/
noncomputable section
set_option autoImplicit false
namespace Zeta7Auxiliary
open PowerSeries Zeta7Common
variable (p : ℕ) [Fact p.Prime]

def cartierSeries (f : PowerSeries (ZMod p)) : PowerSeries (ZMod p) :=
  PowerSeries.mk fun n => coeff (p*n) f

theorem cartierSeries_coeff (f : PowerSeries (ZMod p)) (n : ℕ) :
    coeff n (cartierSeries p f) = coeff (p*n) f := coeff_mk _ _

theorem cartierSeries_add (f g : PowerSeries (ZMod p)) :
    cartierSeries p (f+g) = cartierSeries p f + cartierSeries p g := by
  ext n
  simp only [cartierSeries_coeff, map_add]

theorem cartierSeries_euler (f : PowerSeries (ZMod p)) :
    cartierSeries p (euler f) = 0 := by
  ext n
  rw [cartierSeries_coeff, euler_coeff, map_zero, Nat.cast_mul,
    ZMod.natCast_self, zero_mul, zero_mul]

theorem cartierSeries_expand (f : PowerSeries (ZMod p)) :
    cartierSeries p (expand p (Fact.out : p.Prime).ne_zero f) = f := by
  ext n
  rw [cartierSeries_coeff, coeff_expand_mul]

theorem cartierSeries_coeff_right (f : PowerSeries (ZMod p)) (n : ℕ) :
    coeff n (cartierSeries p f) = coeff (n*p) f := by
  rw [cartierSeries_coeff, Nat.mul_comm p n]

theorem cartierSeries_mul_expand (f g : PowerSeries (ZMod p)) :
    cartierSeries p (f * expand p (Fact.out : p.Prime).ne_zero g) =
      cartierSeries p f * g := by
  classical
  have hp := (Fact.out : p.Prime).ne_zero
  have hx (m : ℕ) : coeff (m*p) (expand p hp g) = coeff m g := by
    rw [Nat.mul_comm m p, coeff_expand_mul]
  ext n
  rw [cartierSeries_coeff_right, coeff_mul, coeff_mul, ← Finset.sum_subset
    (s₁ := (Finset.HasAntidiagonal.antidiagonal n).image fun x ↦ (x.1*p,x.2*p)), Finset.sum_image]
  · simp_rw [hx, cartierSeries_coeff_right]
  · intro x hx y hy he
    simpa only [Prod.ext_iff, Nat.mul_right_cancel_iff hp.bot_lt] using he
  · simp_rw [Finset.subset_iff, Finset.mem_image, Finset.HasAntidiagonal.mem_antidiagonal]
    rintro _ ⟨x,rfl,rfl⟩
    simp_rw [add_mul]
  simp_rw [Finset.mem_image, Finset.HasAntidiagonal.mem_antidiagonal]
  intro ⟨x,y⟩ he hn
  by_cases h : p ∣ y
  · obtain ⟨x,rfl⟩ : p ∣ x := (Nat.dvd_add_iff_left h).mpr (he ▸ dvd_mul_left p n)
    obtain ⟨y,rfl⟩ := h
    refine (hn ⟨⟨x,y⟩, (Nat.mul_right_cancel_iff hp.bot_lt).mp ?_, by simp_rw [mul_comm]⟩).elim
    rw [← he, mul_comm, mul_add]
  · rw [coeff_expand, if_neg h, mul_zero]

theorem expand_cartierSeries_of_euler_zero (f : PowerSeries (ZMod p))
    (hf : euler f = 0) :
    expand p (Fact.out : p.Prime).ne_zero (cartierSeries p f) = f := by
  ext n
  rw [coeff_expand]
  by_cases hn : p ∣ n
  · rw [if_pos hn, cartierSeries_coeff, Nat.mul_div_cancel' hn]
  · rw [if_neg hn]
    have h := congrArg (coeff n) hf
    rw [euler_coeff, map_zero] at h
    exact ((mul_eq_zero.mp h).resolve_left
      (fun hz => hn ((ZMod.natCast_eq_zero_iff n p).mp hz))).symm

theorem euler_zero_iff_expand (f : PowerSeries (ZMod p)) :
    euler f = 0 ↔ ∃ g : PowerSeries (ZMod p),
      f = expand p (Fact.out : p.Prime).ne_zero g := by
  constructor
  · intro hf
    exact ⟨cartierSeries p f, (expand_cartierSeries_of_euler_zero p f hf).symm⟩
  · rintro ⟨g,rfl⟩
    exact euler_frobenius_zero p g

end Zeta7Auxiliary
end


/- Source section: HasseLaurentCalculus. -/

/-! Euler calculus over arbitrary fields, generalized from the existing germ calculus. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open scoped LaurentSeries RatFunc
open HahnSeries PowerSeries
namespace Zeta7FiniteCalculus
variable {K : Type*} [Field K]

def laurentEuler (f : K⸨X⸩) : K⸨X⸩ where
  coeff n := (n : K) * f.coeff n
  isPWO_support' := f.isPWO_support.mono (by
    intro n hn
    contrapose! hn
    simp only [HahnSeries.mem_support, not_not] at hn
    simp [hn])

@[simp] theorem laurentEuler_coeff (f : K⸨X⸩) (n : ℤ) :
    (laurentEuler f).coeff n = (n : K) * f.coeff n := rfl

theorem laurentEuler_support (f : K⸨X⸩) : (laurentEuler f).support ⊆ f.support := by
  intro n hn
  simp only [mem_support, laurentEuler_coeff, ne_eq] at *
  exact fun h => hn (by rw [h, mul_zero])

@[simp] theorem laurentEuler_add (f g : K⸨X⸩) :
    laurentEuler (f + g) = laurentEuler f + laurentEuler g := by
  ext n
  simp [mul_add]

@[simp] theorem laurentEuler_C (a : K) : laurentEuler (HahnSeries.C a) = 0 := by
  ext n
  by_cases hn : n = 0 <;> simp [HahnSeries.C_apply, hn]

@[simp] theorem laurentEuler_one : laurentEuler (1 : K⸨X⸩) = 0 := by
  simpa using laurentEuler_C (1 : K)

@[simp] theorem laurentEuler_zero : laurentEuler (0 : K⸨X⸩) = 0 := by ext n; simp

theorem laurentEuler_mul (f g : K⸨X⸩) :
    laurentEuler (f * g) = laurentEuler f * g + f * laurentEuler g := by
  classical
  ext n
  rw [laurentEuler_coeff, coeff_add,
    coeff_mul_left' f.isPWO_support (laurentEuler_support f),
    coeff_mul_right' g.isPWO_support (laurentEuler_support g), HahnSeries.coeff_mul,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ij hij
  have he : ij.1 + ij.2 = n := (Finset.mem_antidiagonal.mp hij).2.2
  rw [← he, Int.cast_add, laurentEuler_coeff, laurentEuler_coeff]
  ring

theorem laurentEuler_smul (a : K) (f : K⸨X⸩) :
    laurentEuler (a • f) = a • laurentEuler f := by
  ext n
  simp [mul_left_comm]

def laurentD : Derivation K K⸨X⸩ K⸨X⸩ where
  toFun := laurentEuler
  map_add' := laurentEuler_add
  map_smul' a f := by
    simp only [Algebra.smul_def, RingHom.id_apply]
    have ha : (algebraMap K K⸨X⸩) a = HahnSeries.C a := by
      change HahnSeries.ofPowerSeries ℤ K ((algebraMap K K⟦X⟧) a) = _
      exact HahnSeries.ofPowerSeries_C a
    rw [ha]
    ext n
    simp [HahnSeries.C_apply, coeff_single_zero_mul,
      mul_left_comm]
  map_one_eq_zero' := laurentEuler_one
  leibniz' f g := by simpa [smul_eq_mul, mul_comm, add_comm] using laurentEuler_mul f g

theorem laurentD_powerSeries (f : K⟦X⟧) :
    laurentD (f : K⸨X⸩) = (Zeta7Common.euler f : K⟦X⟧) := by
  ext n
  change (n : K) * (f : K⸨X⸩).coeff n = _
  cases n with
  | ofNat n => simp [PowerSeries.coeff_coe, Zeta7Common.euler_coeff]
  | negSucc n => simp [PowerSeries.coeff_coe]

end Zeta7FiniteCalculus
end


/- Source section: HasseRationalCalculus. -/

/-! Euler derivation over arbitrary fields, with its canonical Laurent embedding. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency true
open scoped LaurentSeries RatFunc
open PowerSeries
namespace Zeta7FiniteCalculus
variable {K : Type*} [Field K]

abbrev embed : RatFunc K →+* K⸨X⸩ := algebraMap _ _

theorem embed_injective : Function.Injective (embed (K := K)) := RingHom.injective _

theorem embed_polynomial (p : Polynomial K) :
    embed (p : RatFunc K) = (p : K⟦X⟧) := (RatFunc.coe_coe p).symm

theorem embed_C (a : K) : embed (RatFunc.C a) = HahnSeries.C a := by
  rw [← RatFunc.algebraMap_C, ← RatFunc.coePolynomial_eq_algebraMap, embed_polynomial]
  simp

theorem laurentD_polynomial (p : Polynomial K) :
    laurentD (embed (p : RatFunc K)) =
      embed ((Polynomial.X * p.derivative : Polynomial K) : RatFunc K) := by
  simp only [embed_polynomial]
  rw [laurentD_powerSeries]
  congr 1
  simp [Zeta7Common.euler, PowerSeries.derivative_coe]

def rationalEuler (f : RatFunc K) : RatFunc K :=
  ((Polynomial.X * f.num.derivative : Polynomial K) : RatFunc K) /
      (f.denom : RatFunc K) -
    (f.num : RatFunc K) *
      ((Polynomial.X * f.denom.derivative : Polynomial K) : RatFunc K) /
        (f.denom : RatFunc K) ^ 2

theorem embed_rationalEuler (f : RatFunc K) :
    embed (rationalEuler f) = laurentD (embed f) := by
  conv_rhs => rw [← RatFunc.num_div_denom f]
  simp only [← RatFunc.coePolynomial_eq_algebraMap]
  simp only [rationalEuler, map_sub, map_div₀, map_mul, map_pow,
    Derivation.leibniz_div, smul_eq_mul, laurentD_polynomial]
  field_simp
  <;> ring

theorem rationalEuler_add (f g : RatFunc K) :
    rationalEuler (f + g) = rationalEuler f + rationalEuler g := by
  apply embed_injective
  simp only [map_add, embed_rationalEuler]

theorem rationalEuler_mul (f g : RatFunc K) :
    rationalEuler (f * g) = f * rationalEuler g + g * rationalEuler f := by
  apply embed_injective
  simp only [map_add, map_mul, embed_rationalEuler, Derivation.leibniz, smul_eq_mul]

theorem rationalEuler_smul (a : K) (f : RatFunc K) :
    rationalEuler (a • f) = a • rationalEuler f := by
  apply embed_injective
  simp only [Algebra.smul_def, map_mul, embed_rationalEuler, Derivation.leibniz,
    smul_eq_mul]
  have hc : embed ((algebraMap K (RatFunc K)) a) = HahnSeries.C a := embed_C a
  rw [hc]
  have hz : laurentD (HahnSeries.C a) = 0 := laurentEuler_C a
  rw [hz]
  simp

theorem rationalEuler_one : rationalEuler (1 : RatFunc K) = 0 := by
  apply embed_injective
  simp only [embed_rationalEuler, map_one, map_zero, Derivation.map_one_eq_zero]

def rationalD : Derivation K (RatFunc K) (RatFunc K) where
  toFun := rationalEuler
  map_add' := rationalEuler_add
  map_smul' := rationalEuler_smul
  map_one_eq_zero' := rationalEuler_one
  leibniz' f g := by simpa [smul_eq_mul] using rationalEuler_mul f g

theorem embed_rationalD (f : RatFunc K) :
    embed (rationalD f) = laurentD (embed f) := embed_rationalEuler f

theorem rationalD_polynomial (p : Polynomial K) :
    rationalD (p : RatFunc K) =
      ((Polynomial.X * p.derivative : Polynomial K) : RatFunc K) := by
  apply embed_injective
  rw [embed_rationalD, laurentD_polynomial]

end Zeta7FiniteCalculus
end


/- Source section: HasseRationalCartier. -/

/-! Cartier extraction on the actual rational function field over the prime field. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
namespace Zeta7Auxiliary
open Polynomial
open Zeta7FiniteCalculus
variable (p : ℕ) [Fact p.Prime]

abbrev primePolynomialMap : Polynomial (ZMod p) →+* RatFunc (ZMod p) := algebraMap _ _

theorem primePolynomialMap_ne_zero (f : Polynomial (ZMod p)) (hf : f ≠ 0) :
    primePolynomialMap p f ≠ 0 := RatFunc.algebraMap_ne_zero hf

theorem zmod_polynomial_frobenius (f : Polynomial (ZMod p)) :
    f^p = Polynomial.expand (ZMod p) p f := by
  have h := Polynomial.map_frobenius_expand p f
  have he : frobenius (ZMod p) p = RingHom.id (ZMod p) := by
    ext a
    simpa only [frobenius_def, RingHom.id_apply, ZMod.card] using FiniteField.pow_card a
  simpa only [he, Polynomial.map_id] using h.symm

def cartierRational (f : RatFunc (ZMod p)) : RatFunc (ZMod p) :=
  primePolynomialMap p ((f.num*f.denom^(p-1)).contract p) / primePolynomialMap p f.denom

theorem rational_frobenius_denominator (f : RatFunc (ZMod p)) :
    f = primePolynomialMap p (f.num*f.denom^(p-1)) / (primePolynomialMap p f.denom)^p := by
  have hd := primePolynomialMap_ne_zero p _ f.denom_ne_zero
  have hn := (Fact.out : p.Prime).ne_zero
  rw [map_mul, map_pow, ← pow_sub_one_mul hn (primePolynomialMap p f.denom),
    mul_comm ((primePolynomialMap p f.denom)^(p-1)) (primePolynomialMap p f.denom),
    mul_div_mul_right _ _ (pow_ne_zero _ hd)]
  exact f.num_div_denom.symm

/-- Extraction on every polynomial numerator over a Frobenius denominator;
the numerator and denominator need not be coprime. -/
theorem cartierRational_fraction (a b : Polynomial (ZMod p)) (hb : b ≠ 0) :
    cartierRational p (primePolynomialMap p a / (primePolynomialMap p b)^p) =
      primePolynomialMap p (a.contract p) / primePolynomialMap p b := by
  let f := primePolynomialMap p a / (primePolynomialMap p b)^p
  have hp := (Fact.out : p.Prime).ne_zero
  have he : f.num*b^p=a*f.denom :=
    (RatFunc.num_mul_eq_mul_denom_iff (pow_ne_zero p hb)).mpr (by simp only [map_pow]; rfl)
  have he' : (f.num*f.denom^(p-1))*b^p=a*f.denom^p := by
    rw [← pow_sub_one_mul hp f.denom]
    linear_combination f.denom^(p-1)*he
  have hc := congrArg (Polynomial.contract p) he'
  rw [zmod_polynomial_frobenius, zmod_polynomial_frobenius,
    Polynomial.contract_mul_expand hp, Polynomial.contract_mul_expand hp] at hc
  change primePolynomialMap p ((f.num*f.denom^(p-1)).contract p) /
    primePolynomialMap p f.denom = _
  apply (div_eq_div_iff (primePolynomialMap_ne_zero p _ f.denom_ne_zero)
    (primePolynomialMap_ne_zero p b hb)).mpr
  simpa only [map_mul] using congrArg (primePolynomialMap p) hc

theorem cartierRational_polynomial (a : Polynomial (ZMod p)) :
    cartierRational p (primePolynomialMap p a) = primePolynomialMap p (a.contract p) := by
  simpa only [map_one, one_pow, div_one] using cartierRational_fraction p a 1 one_ne_zero

theorem cartierRational_frobenius (f : RatFunc (ZMod p)) :
    cartierRational p (f^p)=f := by
  nth_rw 1 [← f.num_div_denom]
  rw [div_pow, ← map_pow]
  change cartierRational p (primePolynomialMap p (f.num^p) /
    (primePolynomialMap p f.denom)^p)=f
  rw [cartierRational_fraction p _ _ f.denom_ne_zero, zmod_polynomial_frobenius,
    Polynomial.contract_expand p (Fact.out : p.Prime).ne_zero]
  exact f.num_div_denom

theorem cartierRational_one : cartierRational p 1=1 := by
  simpa only [one_pow] using cartierRational_frobenius p 1

theorem cartierRational_add (f g : RatFunc (ZMod p)) :
    cartierRational p (f+g)=cartierRational p f+cartierRational p g := by
  let a := f.num*f.denom^(p-1)
  let b := g.num*g.denom^(p-1)
  have hf := primePolynomialMap_ne_zero p _ f.denom_ne_zero
  have hg := primePolynomialMap_ne_zero p _ g.denom_ne_zero
  have he : f+g = primePolynomialMap p (a*g.denom^p+b*f.denom^p) /
      (primePolynomialMap p (f.denom*g.denom))^p := by
    conv_lhs => rw [rational_frobenius_denominator p f,rational_frobenius_denominator p g]
    simp only [map_add,map_mul,map_pow,mul_pow]
    dsimp [a,b]
    simp only [map_mul,map_pow]
    field_simp
    <;> ring
  rw [he,cartierRational_fraction p _ _ (mul_ne_zero f.denom_ne_zero g.denom_ne_zero),
    Polynomial.contract_add (Fact.out : p.Prime).ne_zero,
    zmod_polynomial_frobenius,zmod_polynomial_frobenius,
    Polynomial.contract_mul_expand (Fact.out : p.Prime).ne_zero,
    Polynomial.contract_mul_expand (Fact.out : p.Prime).ne_zero,map_add,map_mul,map_mul,map_mul]
  change (primePolynomialMap p (a.contract p)*primePolynomialMap p g.denom+
      primePolynomialMap p (b.contract p)*primePolynomialMap p f.denom) /
    (primePolynomialMap p f.denom*primePolynomialMap p g.denom) =
      primePolynomialMap p (a.contract p)/primePolynomialMap p f.denom+
      primePolynomialMap p (b.contract p)/primePolynomialMap p g.denom
  field_simp
  <;> ring

/-- Frobenius semilinearity on the rational function field. -/
theorem cartierRational_frobenius_mul (f g : RatFunc (ZMod p)) :
    cartierRational p (g^p*f)=g*cartierRational p f := by
  let a := f.num*f.denom^(p-1)
  have he : g^p*f = primePolynomialMap p (g.num^p*a) /
      (primePolynomialMap p (g.denom*f.denom))^p := by
    conv_lhs => rw [← g.num_div_denom, rational_frobenius_denominator p f]
    simp only [a, map_mul, map_pow, mul_pow, div_pow, div_mul_div_comm]
  rw [he, cartierRational_fraction p _ _ (mul_ne_zero g.denom_ne_zero f.denom_ne_zero)]
  have hc : (g.num^p*a).contract p = g.num*a.contract p := by
    rw [mul_comm, zmod_polynomial_frobenius,
      Polynomial.contract_mul_expand (Fact.out : p.Prime).ne_zero, mul_comm]
  rw [hc, map_mul, map_mul, ← div_mul_div_comm]
  change (primePolynomialMap p g.num / primePolynomialMap p g.denom) *
    cartierRational p f = _
  rw [g.num_div_denom]

theorem rationalD_frobenius (f : RatFunc (ZMod p)) : rationalD (f^p)=0 := by
  rw [Derivation.leibniz_pow]
  simp only [smul_eq_mul, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul, mul_zero]

theorem rationalD_frobenius_fraction (a b : Polynomial (ZMod p)) (hb : b≠0) :
    rationalD (primePolynomialMap p a / (primePolynomialMap p b)^p) =
      primePolynomialMap p (X*a.derivative) / (primePolynomialMap p b)^p := by
  rw [Derivation.leibniz_div_const rationalD _ _ (rationalD_frobenius p _)]
  have ha : rationalD (primePolynomialMap p a) = primePolynomialMap p (X*a.derivative) :=
    rationalD_polynomial a
  rw [ha]
  simp only [smul_eq_mul,div_eq_mul_inv,mul_comm]

theorem contract_polynomial_euler (a : Polynomial (ZMod p)) :
    (X*a.derivative).contract p = 0 := by
  ext n
  rw [Polynomial.coeff_contract (Fact.out : p.Prime).ne_zero, Polynomial.coeff_zero]
  have he := congrArg (PowerSeries.coeff (n*p))
    (show (Zeta7Common.euler (a:PowerSeries (ZMod p))) =
      ((X*a.derivative : Polynomial (ZMod p)) : PowerSeries (ZMod p)) by
        simp [Zeta7Common.euler, PowerSeries.derivative_coe])
  rw [Zeta7Common.euler_coeff] at he
  simpa only [Polynomial.coeff_coe, Nat.cast_mul, ZMod.natCast_self,
    mul_zero, zero_mul] using he.symm

theorem cartierRational_euler (f : RatFunc (ZMod p)) : cartierRational p (rationalD f)=0 := by
  nth_rw 1 [rational_frobenius_denominator p f]
  rw [rationalD_frobenius_fraction p _ _ f.denom_ne_zero,
    cartierRational_fraction p _ _ f.denom_ne_zero, contract_polynomial_euler,
    map_zero, zero_div]

/-- The constants of the actual rational Euler derivation are exactly p-th powers. -/
theorem rationalD_zero_iff_frobenius (f : RatFunc (ZMod p)) :
    rationalD f=0 ↔ ∃ g : RatFunc (ZMod p), f=g^p := by
  constructor
  · intro hf
    let a := f.num*f.denom^(p-1)
    have he : primePolynomialMap p (X*a.derivative)=0 := by
      have h := hf
      nth_rw 1 [rational_frobenius_denominator p f] at h
      rw [rationalD_frobenius_fraction p _ _ f.denom_ne_zero] at h
      exact (div_eq_zero_iff.mp h).resolve_right
        (pow_ne_zero _ (primePolynomialMap_ne_zero p _ f.denom_ne_zero))
    have ha : a.derivative=0 := by
      have hz : X*a.derivative=0 := by
        apply RatFunc.algebraMap_injective (ZMod p)
        simpa only [map_zero] using he
      exact (mul_eq_zero.mp hz).resolve_left Polynomial.X_ne_zero
    have hc : (a.contract p)^p=a := by
      rw [zmod_polynomial_frobenius]
      exact Polynomial.expand_contract p ha (Fact.out : p.Prime).ne_zero
    refine ⟨primePolynomialMap p (a.contract p)/primePolynomialMap p f.denom, ?_⟩
    rw [div_pow, ← map_pow, hc]
    exact rational_frobenius_denominator p f
  · rintro ⟨g,rfl⟩
    exact rationalD_frobenius p g

end Zeta7Auxiliary
end


/- Source section: HasseRationalGamma. -/

/-! The rational Hasse factor and its identification with the original formal factor. -/
noncomputable section
set_option autoImplicit false
namespace Zeta7Auxiliary
open scoped LaurentSeries
open Zeta7FiniteCalculus
variable (p : ℕ) [Fact p.Prime]

abbrev primeLaurentMap : PowerSeries (ZMod p) →+* (ZMod p)⸨X⸩ :=
  HahnSeries.ofPowerSeries ℤ (ZMod p)

theorem hassePolyP_coe_reducedP :
    ((hassePolyP : Polynomial (ZMod p)) : PowerSeries (ZMod p)) = reducedP p := by
  rw [hassePolyP_coe, reducedP_value]
  rfl

theorem reducedP_laurent_inverse : primeLaurentMap p ((reducedP p)⁻¹) =
    (primeLaurentMap p (reducedP p))⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  rw [← map_mul, reducedP_mul_inv, map_one]

def hasseGammaRational (hp : 5 ≤ p) : RatFunc (ZMod p) :=
  (primePolynomialMap p (reducedQuotient p hp))^2 /
    (primePolynomialMap p hassePolyP)^(2*((p-1)/3))

theorem hasseGammaRational_embed (hp : 5 ≤ p) :
    embed (hasseGammaRational p hp) = primeLaurentMap p (hasseGammaSeries p hp) := by
  have he (f : Polynomial (ZMod p)) :
      embed (primePolynomialMap p f) = primeLaurentMap p (f : PowerSeries (ZMod p)) :=
    embed_polynomial f
  simp only [hasseGammaRational, map_div₀, map_inv₀, map_pow, he, hassePolyP_coe_reducedP,
    hasseGammaSeries, map_mul, reducedP_laurent_inverse, div_eq_mul_inv, inv_pow]

theorem hasseGammaRational_ne_zero (hp : 5 ≤ p) : hasseGammaRational p hp ≠ 0 := by
  intro h
  have he := hasseGammaRational_embed p hp
  rw [h, map_zero] at he
  have hz : hasseGammaSeries p hp = 0 := HahnSeries.ofPowerSeries_injective
    (show primeLaurentMap p (hasseGammaSeries p hp) = primeLaurentMap p 0 by
      rw [map_zero]; exact he.symm)
  have hc := hasseGammaSeries_constant p hp
  rw [hz, map_zero] at hc
  exact zero_ne_one hc

/-- The characteristic-p rational Euler calculus agrees with the actual formal logarithmic derivative. -/
theorem hasseGammaRational_logarithmic_embed (hp : 5 ≤ p) :
    embed (rationalD (hasseGammaRational p hp) / hasseGammaRational p hp) =
      laurentD (primeLaurentMap p (hasseGammaSeries p hp)) /
        primeLaurentMap p (hasseGammaSeries p hp) := by
  rw [map_div₀, embed_rationalD, hasseGammaRational_embed]

theorem hasseGammaRational_actual_logarithmic (hp : 5 ≤ p) :
    embed (rationalD (hasseGammaRational p hp) / hasseGammaRational p hp) =
      primeLaurentMap p (Zeta7Common.euler (reducedB p) * (reducedB p)⁻¹) := by
  have hi : primeLaurentMap p ((hasseGammaSeries p hp)⁻¹) =
      (primeLaurentMap p (hasseGammaSeries p hp))⁻¹ := by
    apply eq_inv_of_mul_eq_one_right
    rw [← map_mul, PowerSeries.mul_inv_cancel _ (by
      rw [hasseGammaSeries_constant]; exact one_ne_zero), map_one]
  rw [hasseGammaRational_logarithmic_embed]
  have hD : laurentD (primeLaurentMap p (hasseGammaSeries p hp)) =
      primeLaurentMap p (Zeta7Common.euler (hasseGammaSeries p hp)) :=
    laurentD_powerSeries _
  rw [hD, div_eq_mul_inv, ← hi, ← map_mul, ← reducedB_logarithmic_derivative p hp]

theorem hasseGammaSeries_clearedRiccati (hp : 5 ≤ p) :
    clearedRiccati (hasseGammaSeries p hp)=0 := by
  have hY := hasseRootSeries_equation p hp
  rw [reducedP_value] at hY
  change 4*hasseP^2*Zeta7Common.euler (Zeta7Common.euler (hasseRootSeries p hp)) =
    hasseW*hasseRootSeries p hp at hY
  have hadd (a b : PowerSeries (ZMod p)) :
      Zeta7Common.euler (a+b)=Zeta7Common.euler a+Zeta7Common.euler b :=
    Zeta7Common.eulerLinear.map_add a b
  unfold clearedRiccati
  rw [← hasseRootSeries_sq]
  simp only [pow_two, Zeta7Common.euler_mul_general, hadd]
  linear_combination (hasseRootSeries p hp)^3*hY

end Zeta7Auxiliary
end


/- Source section: HasseHermiteReduction. -/

/-! Polynomial Hermite reduction for the actual Hasse second-order equation. -/
noncomputable section
set_option autoImplicit false
namespace Zeta7Auxiliary
open Polynomial
variable {K : Type*} [Field K]

theorem polynomial_coprime_X_of_constant_one (Q : Polynomial K) (hQ : Q.coeff 0=1) :
    IsCoprime Q X := by
  refine ⟨1,-Q.divX,?_⟩
  have h := X_mul_divX_add Q
  rw [hQ,map_one] at h
  linear_combination -h

theorem separable_square_dvd (Q F : Polynomial K) (hsep : IsCoprime Q Q.derivative)
    (hF : Q ∣ F) (hF' : Q ∣ F.derivative) : Q^2 ∣ F := by
  obtain ⟨T,hT⟩ := hF
  rw [hT,derivative_mul] at hF'
  have ht : Q ∣ Q.derivative*T :=
    (dvd_add_left (dvd_mul_right Q T.derivative)).mp hF'
  obtain ⟨U,hU⟩ := hsep.dvd_of_dvd_mul_left ht
  refine ⟨U,?_⟩
  rw [hT,hU]
  ring

theorem polynomial_derivative_pow_cleared (P : Polynomial K) (k : ℕ) :
    P*(P^k).derivative=(k:Polynomial K)*P^k*P.derivative := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ,derivative_mul,Nat.cast_add,Nat.cast_one]
    linear_combination P*ih

/-- A polynomial divisible by Q², of no larger degree, is determined by its constant. -/
theorem square_divisor_zero (Q F : Polynomial K) (hQ : Q.coeff 0=1)
    (hdiv : Q^2 ∣ F) (hdeg : F.natDegree ≤ 2*Q.natDegree) (hF : F.coeff 0=0) : F=0 := by
  have hQ0 : Q≠0 := by intro h; simpa [h] using hQ
  obtain ⟨T,hT⟩ := hdiv
  by_cases ht : T=0
  · simp [hT,ht]
  have hd : T.natDegree=0 := by
    rw [hT,natDegree_mul (pow_ne_zero _ hQ0) ht,natDegree_pow] at hdeg
    omega
  have he := congrArg (Polynomial.eval 0) hT
  simp only [eval_mul,eval_pow,← coeff_zero_eq_eval_zero,hF,hQ,
    one_pow,one_mul] at he
  rw [hT,eq_C_of_natDegree_eq_zero hd,← he,map_zero,mul_zero]

/-- Hermite reduction justified by the second-order equation and degree bounds. -/
theorem hasse_hermite_reduction (P Q : Polynomial K) (k : ℕ)
    (hP : P.coeff 0=1) (hQ : Q.coeff 0=1) (hk : 0 < k)
    (hPdeg : P.natDegree ≤ 2) (hQdeg : Q.natDegree=k)
    (hsep : IsCoprime Q Q.derivative) (hcop : IsCoprime Q P)
    (hode : Q ∣ X*P*Q.derivative.derivative+
      (P-(k:Polynomial K)*X*P.derivative)*Q.derivative) :
    ∃ S : Polynomial K, S.natDegree < Q.natDegree ∧
      P^k-Q^2=X*(S.derivative*Q-S*Q.derivative) := by
  have hQX := polynomial_coprime_X_of_constant_one Q hQ
  obtain ⟨a,b,hab⟩ := hQX.mul_right hsep
  let T := -b*P^k
  let S := T%Q
  have hs : S.natDegree < Q.natDegree := natDegree_mod_lt T (by omega)
  have hmod : S+Q*(T/Q)=T := EuclideanDomain.mod_add_div T Q
  have hfirst : Q ∣ P^k+X*S*Q.derivative := by
    refine ⟨a*P^k-X*Q.derivative*(T/Q),?_⟩
    dsimp [T] at hmod
    linear_combination -P^k*hab + X*Q.derivative*hmod
  let F := P^k-Q^2-X*(S.derivative*Q-S*Q.derivative)
  have hf : Q ∣ F := by
    obtain ⟨U,hU⟩ := hfirst
    refine ⟨U-Q-X*S.derivative,?_⟩
    dsimp [F]
    linear_combination hU
  have hf' : Q ∣ F.derivative := by
    apply hcop.dvd_of_dvd_mul_left
    obtain ⟨U,hU⟩ := hfirst
    obtain ⟨V,hV⟩ := hode
    refine ⟨(k:Polynomial K)*P.derivative*U+S*V-
      2*P*Q.derivative-P*S.derivative-X*P*S.derivative.derivative,?_⟩
    have hQsq : (Q^2).derivative=2*Q*Q.derivative := by
      rw [pow_two,derivative_mul]; ring
    dsimp [F]
    simp only [derivative_sub,derivative_mul,derivative_X,one_mul,hQsq]
    linear_combination polynomial_derivative_pow_cleared P k +
      (k:Polynomial K)*P.derivative*hU + S*hV
  have hdeg : F.natDegree ≤ 2*Q.natDegree := by
    have hdS : S.derivative.natDegree ≤ S.natDegree :=
      (natDegree_derivative_le S).trans (Nat.sub_le _ _)
    have hdQ : Q.derivative.natDegree ≤ Q.natDegree :=
      (natDegree_derivative_le Q).trans (Nat.sub_le _ _)
    have hleft : (P^k-Q^2).natDegree ≤ 2*Q.natDegree := by
      apply (natDegree_sub_le _ _).trans
      apply max_le
      · rw [natDegree_pow,hQdeg]
        nlinarith
      · rw [natDegree_pow]
    have ht : (X*(S.derivative*Q-S*Q.derivative)).natDegree ≤ 2*Q.natDegree := by
      have h₁ := natDegree_mul_le (p := S.derivative) (q := Q)
      have h₂ := natDegree_mul_le (p := S) (q := Q.derivative)
      have h₃ := natDegree_sub_le (S.derivative*Q) (S*Q.derivative)
      have h₄ := natDegree_mul_le (p := (X:Polynomial K)) (q := S.derivative*Q-S*Q.derivative)
      rw [natDegree_X] at h₄
      omega
    exact (natDegree_sub_le _ _).trans (max_le hleft ht)
  have hconst : F.coeff 0=0 := by
    have hp0 : P.eval 0=1 := by rw [← coeff_zero_eq_eval_zero,hP]
    have hq0 : Q.eval 0=1 := by rw [← coeff_zero_eq_eval_zero,hQ]
    rw [coeff_zero_eq_eval_zero]
    simp [F,hp0,hq0]
  have hz := square_divisor_zero Q F hQ (separable_square_dvd Q F hsep hf hf') hdeg hconst
  exact ⟨S,hs,sub_eq_zero.mp hz⟩

variable (p : ℕ) [Fact p.Prime]

theorem reducedQuotient_hermite_ode (hp : 11 ≤ p) :
    reducedQuotient p (by omega) ∣
      X*hassePolyP*(reducedQuotient p (by omega)).derivative.derivative+
      (hassePolyP-((2*((p-1)/3):ℕ):Polynomial (ZMod p))*X*hassePolyP.derivative)*
        (reducedQuotient p (by omega)).derivative := by
  let Q := reducedQuotient p (by omega)
  let n := (p-1)/3
  let P : Polynomial (ZMod p) := hassePolyP
  have hQX : IsCoprime Q X := polynomial_coprime_X_of_constant_one Q
    (reducedQuotient_constant p (by omega))
  have hQP : IsCoprime Q P := reducedQuotient_coprime p hp
  have h4 : (4:ZMod p)≠0 := small_natCast_ne_zero p 4 (by omega) (by omega)
  have hQ4 : IsCoprime Q (4:Polynomial (ZMod p)) := by
    refine ⟨0,C ((4:ZMod p)⁻¹),?_⟩
    rw [zero_mul,zero_add,show (4:Polynomial (ZMod p))=C (4:ZMod p) from
      (map_ofNat C 4).symm,← map_mul,inv_mul_cancel₀ h4,map_one]
  apply ((hQ4.mul_right hQX).mul_right hQP).dvd_of_dvd_mul_left
  refine ⟨-hassePolyC n,?_⟩
  have he := reducedQuotient_polynomialODE p (by omega)
  change hassePolynomialODE n Q=0 at he
  unfold hassePolynomialODE hassePolyA hassePolyB at he
  change (4*X*P)*(X*P*Q.derivative.derivative+
    (P-((2*n:ℕ):Polynomial (ZMod p))*X*P.derivative)*Q.derivative)=Q*(-hassePolyC n)
  push_cast
  dsimp [P]
  linear_combination he

/-- An exact rational primitive for the inverse of the actual Hasse factor minus one. -/
theorem reducedQuotient_hermite (hp : 11 ≤ p) :
    ∃ S : Polynomial (ZMod p), S.natDegree < (reducedQuotient p (by omega)).natDegree ∧
      hassePolyP^(2*((p-1)/3))-(reducedQuotient p (by omega))^2 =
        X*(S.derivative*reducedQuotient p (by omega)-S*(reducedQuotient p (by omega)).derivative) := by
  apply hasse_hermite_reduction hassePolyP (reducedQuotient p (by omega)) (2*((p-1)/3))
  · simp [hassePolyP]
  · exact reducedQuotient_constant p (by omega)
  · omega
  · unfold hassePolyP
    compute_degree!
  · exact reducedQuotient_degree p hp
  · exact (separable_def _).mp (reducedQuotient_separable p hp)
  · exact reducedQuotient_coprime p hp
  · exact reducedQuotient_hermite_ode p hp

end Zeta7Auxiliary
end


/- Source section: ActualHasseCartier. -/

/-! The actual inverse Hasse factor has Cartier extraction equal to one. -/
noncomputable section
set_option autoImplicit false
namespace Zeta7Auxiliary
open Polynomial Zeta7FiniteCalculus
variable (p : ℕ) [Fact p.Prime]

theorem hasseGammaRational_inverse_primitive (hp : 11 ≤ p) :
    ∃ f : RatFunc (ZMod p), (hasseGammaRational p (by omega))⁻¹=1+rationalD f := by
  obtain ⟨S,hS,he⟩ := reducedQuotient_hermite p hp
  let Q := reducedQuotient p (by omega)
  have hQ : Q≠0 := by
    intro h
    have hc := reducedQuotient_constant p (by omega)
    change Q.coeff 0=1 at hc
    rw [h,coeff_zero] at hc
    exact zero_ne_one hc
  have hQr := primePolynomialMap_ne_zero p Q hQ
  refine ⟨primePolynomialMap p S/primePolynomialMap p Q,?_⟩
  have hDS : rationalD (primePolynomialMap p S)=primePolynomialMap p (X*S.derivative) :=
    rationalD_polynomial S
  have hDQ : rationalD (primePolynomialMap p Q)=primePolynomialMap p (X*Q.derivative) :=
    rationalD_polynomial Q
  rw [hasseGammaRational,inv_div,Derivation.leibniz_div,hDS,hDQ]
  simp only [smul_eq_mul]
  have hm := congrArg (primePolynomialMap p) he
  simp only [map_sub,map_pow,map_mul] at hm
  change (primePolynomialMap p hassePolyP)^(2*((p-1)/3)) / (primePolynomialMap p Q)^2 = _
  field_simp
  simp only [map_mul]
  dsimp [Q]
  simp only [primePolynomialMap,RatFunc.algebraMap_X] at hm ⊢
  linear_combination hm

/-- Equation (22) for the original Hasse quotient, without a formal-unit hypothesis. -/
theorem cartierRational_hasseGamma_inverse (hp : 11 ≤ p) :
    cartierRational p ((hasseGammaRational p (by omega))⁻¹)=1 := by
  obtain ⟨f,hf⟩ := hasseGammaRational_inverse_primitive p hp
  rw [hf,cartierRational_add,cartierRational_one,cartierRational_euler,add_zero]

end Zeta7Auxiliary
end


/- Source section: HasseRationalKernel. -/

/-! The characteristic-p rational kernel of the original third-order operator. -/
noncomputable section
set_option autoImplicit false
namespace Zeta7Auxiliary
open Zeta7FiniteCalculus
variable (p : ℕ) [Fact p.Prime]

def hassePotentialRational : RatFunc (ZMod p) :=
  primePolynomialMap p hassePolyW / (primePolynomialMap p hassePolyP)^2

def hasseOperatorRational (f : RatFunc (ZMod p)) : RatFunc (ZMod p) :=
  rationalD (rationalD (rationalD f)) - hassePotentialRational p * rationalD f -
    rationalD (hassePotentialRational p) / 2 * f

theorem hasseGammaRational_clearedRiccati (hp : 5 ≤ p) :
    (primePolynomialMap p hassePolyP)^2 *
      (2*hasseGammaRational p hp*rationalD (rationalD (hasseGammaRational p hp))-
        (rationalD (hasseGammaRational p hp))^2) -
      primePolynomialMap p hassePolyW*(hasseGammaRational p hp)^2=0 := by
  apply embed_injective
  have h := congrArg (primeLaurentMap p) (hasseGammaSeries_clearedRiccati p hp)
  simp only [clearedRiccati,map_sub,map_mul,map_pow,map_ofNat,map_zero] at h
  simp only [map_sub,map_mul,map_pow,map_ofNat,map_zero,embed_rationalD,
    hasseGammaRational_embed]
  have hP : embed (primePolynomialMap p hassePolyP)=primeLaurentMap p hasseP := by
    have he : embed (primePolynomialMap p hassePolyP)=
        primeLaurentMap p ((hassePolyP : Polynomial (ZMod p)) : PowerSeries (ZMod p)) :=
      embed_polynomial _
    simpa only [hassePolyP_coe] using he
  have hW : embed (primePolynomialMap p hassePolyW)=primeLaurentMap p hasseW := by
    have he : embed (primePolynomialMap p hassePolyW)=
        primeLaurentMap p ((hassePolyW : Polynomial (ZMod p)) : PowerSeries (ZMod p)) :=
      embed_polynomial _
    simpa only [hassePolyW_coe] using he
  rw [hP,hW,laurentD_powerSeries,laurentD_powerSeries]
  exact h

theorem hasseGammaRational_riccati (hp : 5 ≤ p) :
    let u := rationalD (hasseGammaRational p hp)/hasseGammaRational p hp
    2*rationalD u+u^2=hassePotentialRational p := by
  have hG := hasseGammaRational_ne_zero p hp
  have hP : primePolynomialMap p hassePolyP≠0 := by
    apply primePolynomialMap_ne_zero
    intro h
    have h0 := congrArg (fun f : Polynomial (ZMod p) => f.coeff 0) h
    simpa [hassePolyP] using h0
  dsimp
  rw [Derivation.leibniz_div]
  simp only [smul_eq_mul]
  unfold hassePotentialRational
  field_simp
  linear_combination hasseGammaRational_clearedRiccati p hp

theorem hasseOperatorRational_factor (hp : 11 ≤ p) (f : RatFunc (ZMod p)) :
    let u := rationalD (hasseGammaRational p (by omega))/hasseGammaRational p (by omega)
    hasseOperatorRational p f =
      rationalD (rationalD (rationalD f-u*f))+u*rationalD (rationalD f-u*f) := by
  dsimp
  let u := rationalD (hasseGammaRational p (by omega))/hasseGammaRational p (by omega)
  have hV : 2*rationalD u+u^2=hassePotentialRational p := hasseGammaRational_riccati p (by omega)
  have hDV := congrArg rationalD hV
  have h2 : rationalD (2 : RatFunc (ZMod p))=0 := Derivation.map_natCast _ 2
  simp only [map_add,Derivation.leibniz,Derivation.leibniz_pow,smul_eq_mul,
    h2,mul_zero,add_zero,pow_one,nsmul_eq_mul] at hDV
  change hasseOperatorRational p f = rationalD (rationalD (rationalD f-u*f))+
    u*rationalD (rationalD f-u*f)
  simp only [hasseOperatorRational,map_sub,map_add,Derivation.leibniz,smul_eq_mul]
  have htwo : (2:RatFunc (ZMod p))≠0 :=
    small_natCast_ne_zero (K := RatFunc (ZMod p)) p 2 (by omega) (by omega)
  field_simp
  linear_combination 2*rationalD f*hV+f*hDV

/-- The exact rational kernel, specialized to the original Hasse quotient. -/
theorem hasseOperatorRational_kernel (hp : 11 ≤ p) (f : RatFunc (ZMod p)) :
    hasseOperatorRational p f=0 ↔
      ∃ g : RatFunc (ZMod p), f=hasseGammaRational p (by omega)*g^p := by
  let G := hasseGammaRational p (by omega)
  let u := rationalD G/G
  have hG : G≠0 := hasseGammaRational_ne_zero p (by omega)
  have hC : cartierRational p G⁻¹=1 := cartierRational_hasseGamma_inverse p hp
  have hprod (v : RatFunc (ZMod p)) : rationalD (G*v)=G*(rationalD v+u*v) := by
    rw [Derivation.leibniz]
    simp only [smul_eq_mul]
    dsimp [u]
    field_simp
    <;> ring
  have hquot (v : RatFunc (ZMod p)) : rationalD (v/G)=(rationalD v-u*v)/G := by
    rw [Derivation.leibniz_div]
    simp only [smul_eq_mul]
    dsimp [u]
    field_simp
    <;> ring
  rw [hasseOperatorRational_factor p hp]
  change rationalD (rationalD (rationalD f-u*f))+u*rationalD (rationalD f-u*f)=0 ↔ _
  constructor
  · intro hf
    have hz : rationalD (G*rationalD (rationalD f-u*f))=0 := by rw [hprod,hf,mul_zero]
    obtain ⟨a,ha⟩ := (rationalD_zero_iff_frobenius p _).mp hz
    have he : rationalD (rationalD f-u*f)=a^p*G⁻¹ := by
      apply (mul_left_cancel₀ hG)
      rw [ha]
      field_simp
    have hc := congrArg (cartierRational p) he
    rw [cartierRational_euler,cartierRational_frobenius_mul,hC,mul_one] at hc
    have hz' : rationalD (rationalD f-u*f)=0 := by rw [he,← hc,zero_pow (Fact.out : p.Prime).ne_zero,zero_mul]
    obtain ⟨b,hb⟩ := (rationalD_zero_iff_frobenius p _).mp hz'
    have he' : rationalD (f/G)=b^p*G⁻¹ := by rw [hquot,hb,div_eq_mul_inv]
    have hc' := congrArg (cartierRational p) he'
    rw [cartierRational_euler,cartierRational_frobenius_mul,hC,mul_one] at hc'
    have hz'' : rationalD (f/G)=0 := by rw [he',← hc',zero_pow (Fact.out : p.Prime).ne_zero,zero_mul]
    obtain ⟨g,hg⟩ := (rationalD_zero_iff_frobenius p _).mp hz''
    exact ⟨g, by rw [div_eq_iff hG] at hg; simpa only [mul_comm] using hg⟩
  · rintro ⟨g,hg⟩
    have hz : rationalD f-u*f=0 := by
      rw [hg,Derivation.leibniz,rationalD_frobenius]
      simp only [smul_eq_mul,mul_zero,zero_add]
      dsimp [u]
      field_simp
      simp [G]
    rw [hz,map_zero,map_zero,mul_zero,add_zero]

end Zeta7Auxiliary
end


/- Source section: HassePolynomialKernel. -/

/-! Degree obstruction for polynomial elements of the actual rational kernel. -/
noncomputable section
set_option autoImplicit false
namespace Zeta7Auxiliary
open Polynomial Zeta7FiniteCalculus

theorem isUnit_of_cube_dvd_squarefree_square {K : Type*} [Field K]
    (Q b : Polynomial K) (hQ : Squarefree Q) (hb : b≠0) (h : b^3 ∣ Q^2) : IsUnit b := by
  by_contra hu
  obtain ⟨r,hr,hrb⟩ := WfDvdMonoid.exists_irreducible_factor hu hb
  have hr3 : r^3 ∣ Q*Q := by
    rw [← pow_two]
    exact (pow_dvd_pow_of_dvd hrb 3).trans h
  have hr2 : r^2 ∣ Q := hQ.pow_dvd_of_squarefree_of_pow_succ_dvd_mul_right hr.prime hr3
  exact hr.not_isUnit (hQ r (by simpa only [pow_two] using hr2))

variable (p : ℕ) [Fact p.Prime]

theorem hassePolyP_natDegree (hp : 11 ≤ p) :
    (hassePolyP : Polynomial (ZMod p)).natDegree=2 := by
  have h7 : (7:ZMod p)≠0 := small_natCast_ne_zero p 7 (by omega) (by omega)
  have h49 : (49:ZMod p)≠0 := by
    rw [show (49:ZMod p)=7^2 by ring]
    exact pow_ne_zero _ h7
  unfold hassePolyP
  compute_degree!

/-- A rational multiplier cannot hide a pole in the order-two zeros of Gamma. -/
theorem hasse_polynomial_kernel_multiplier (hp : 11 ≤ p)
    (F : Polynomial (ZMod p)) (g : RatFunc (ZMod p))
    (he : primePolynomialMap p F=hasseGammaRational p (by omega)*g^p) :
    ∃ a : Polynomial (ZMod p), g=primePolynomialMap p a := by
  let Q := reducedQuotient p (by omega)
  let P : Polynomial (ZMod p) := hassePolyP
  let k := 2*((p-1)/3)
  have hP : P≠0 := by
    intro h
    have hh := congrArg (fun f : Polynomial (ZMod p) => f.coeff 0) h
    simpa [P,hassePolyP] using hh
  have hPr := primePolynomialMap_ne_zero p P hP
  have hbr := primePolynomialMap_ne_zero p _ g.denom_ne_zero
  have hid : F*P^k*g.denom^p=Q^2*g.num^p := by
    apply (RatFunc.algebraMap_injective (ZMod p))
    simp only [map_mul,map_pow]
    have h := he
    rw [hasseGammaRational,← g.num_div_denom,div_pow] at h
    change primePolynomialMap p F=(primePolynomialMap p Q)^2 /
      (primePolynomialMap p P)^k *
      ((primePolynomialMap p g.num)^p/(primePolynomialMap p g.denom)^p) at h
    field_simp at h
    linear_combination h
  have hbpow : g.denom^p ∣ Q^2 := by
    apply ((g.isCoprime_num_denom.symm.pow_left).pow_right).dvd_of_dvd_mul_right
    rw [← hid]
    exact dvd_mul_left _ _
  have hb3 : g.denom^3 ∣ Q^2 := (pow_dvd_pow _ (by omega : 3 ≤ p)).trans hbpow
  have hbunit := isUnit_of_cube_dvd_squarefree_square Q g.denom
    (reducedQuotient_squarefree p hp) g.denom_ne_zero hb3
  have hb1 : g.denom=1 := g.monic_denom.eq_one_of_isUnit hbunit
  exact ⟨g.num, by simpa only [hb1,map_one,div_one] using g.num_div_denom.symm⟩

/-- Every nonzero polynomial in the actual characteristic-p kernel has degree at least 2p. -/
theorem hasseOperatorRational_polynomial_degree (hp : 11 ≤ p)
    (F : Polynomial (ZMod p)) (hF : F≠0)
    (he : hasseOperatorRational p (primePolynomialMap p F)=0) : 2*p ≤ F.natDegree := by
  obtain ⟨g,hg⟩ := (hasseOperatorRational_kernel p hp _).mp he
  obtain ⟨a,rfl⟩ := hasse_polynomial_kernel_multiplier p hp F g hg
  let Q := reducedQuotient p (by omega)
  let P : Polynomial (ZMod p) := hassePolyP
  let k := 2*((p-1)/3)
  have hk : 0 < k := by dsimp [k]; omega
  have hPd : P.natDegree=2 := hassePolyP_natDegree p hp
  have hP : P≠0 := by intro h; simpa [h] using hPd
  have hQ : Q≠0 := by
    intro h
    have hc := reducedQuotient_constant p (by omega)
    change Q.coeff 0=1 at hc
    simpa [h] using hc
  have ha : a≠0 := by
    intro h
    rw [h,map_zero,zero_pow (Fact.out : p.Prime).ne_zero,mul_zero] at hg
    exact primePolynomialMap_ne_zero p F hF hg
  have hid : P^k*F=Q^2*a^p := by
    apply (RatFunc.algebraMap_injective (ZMod p))
    simp only [map_mul,map_pow]
    have h := hg
    rw [hasseGammaRational] at h
    change primePolynomialMap p F=(primePolynomialMap p Q)^2 /
      (primePolynomialMap p P)^k * (primePolynomialMap p a)^p at h
    have hPr := primePolynomialMap_ne_zero p P hP
    field_simp at h
    linear_combination h
  have hPa : P ∣ a := by
    apply (hassePolyP_separable p hp).squarefree.isRadical p a
    apply (reducedQuotient_coprime p hp).symm.pow_right.dvd_of_dvd_mul_left
    rw [← hid]
    exact dvd_mul_of_dvd_left (dvd_pow_self P hk.ne') F
  have had : 2 ≤ a.natDegree := by
    rw [← hPd]
    exact natDegree_le_of_dvd hPa ha
  have hd := congrArg Polynomial.natDegree hid
  rw [natDegree_mul (pow_ne_zero _ hP) hF,
    natDegree_mul (pow_ne_zero _ hQ) (pow_ne_zero _ ha),natDegree_pow,natDegree_pow,
    natDegree_pow,hPd,reducedQuotient_degree p hp] at hd
  dsimp [k] at hd
  nlinarith

/-- The numerator used for the primitive carries in the paper's P3. -/
def hasseCarryPolynomial (hp : 11 ≤ p) : Polynomial (ZMod p) :=
  X*(1+10*X)*(reducedQuotient p (by omega))^2 *
    hassePolyP^(p-2*((p-1)/3)-1)

theorem hasseCarryPolynomial_constant (hp : 11 ≤ p) :
    (hasseCarryPolynomial p hp).coeff 0=0 := by
  rw [coeff_zero_eq_eval_zero]
  simp [hasseCarryPolynomial]

theorem hasseCarryPolynomial_degree (hp : 11 ≤ p) :
    (hasseCarryPolynomial p hp).natDegree ≤ 2*p := by
  have hn : 2*((p-1)/3)+1 ≤ p := by omega
  have h₁ : ((X*(1+10*X)) : Polynomial (ZMod p)).natDegree ≤ 2 := by compute_degree!
  have h₂ := natDegree_mul_le (p := (X*(1+10*X) : Polynomial (ZMod p)))
    (q := (reducedQuotient p (by omega))^2)
  have h₃ := natDegree_mul_le
    (p := (X*(1+10*X)*(reducedQuotient p (by omega))^2 : Polynomial (ZMod p)))
    (q := (hassePolyP : Polynomial (ZMod p))^(p-2*((p-1)/3)-1))
  rw [natDegree_pow,reducedQuotient_degree p hp] at h₂
  rw [natDegree_pow,hassePolyP_natDegree p hp] at h₃
  change _ ≤ 2*p
  dsimp [hasseCarryPolynomial]
  omega

/-- Exact denominator clearing for R Gamma, prior to any carry extraction. -/
theorem hasseCarryPolynomial_fraction (hp : 11 ≤ p) :
    (primePolynomialMap p (X*(1+10*X)) / primePolynomialMap p hassePolyP) *
      hasseGammaRational p (by omega) =
    primePolynomialMap p (hasseCarryPolynomial p hp) /
      (primePolynomialMap p hassePolyP)^p := by
  let P := primePolynomialMap p (hassePolyP : Polynomial (ZMod p))
  let Q := primePolynomialMap p (reducedQuotient p (by omega))
  let U := primePolynomialMap p (X*(1+10*X) : Polynomial (ZMod p))
  let k := 2*((p-1)/3)
  let m := p-2*((p-1)/3)-1
  have hP : P≠0 := by
    apply primePolynomialMap_ne_zero
    intro h
    have hd := hassePolyP_natDegree p hp
    simpa [h] using hd
  have hnum : primePolynomialMap p (hasseCarryPolynomial p hp)=U*Q^2*P^m := by
    simp only [hasseCarryPolynomial,U,Q,P,m,map_mul,map_pow]
  rw [hnum]
  change U/P*(Q^2/P^k)=(U*Q^2*P^m)/P^p
  have hden : P*P^k*P^m=P^p := by
    rw [← pow_succ',← pow_add]
    congr 1
    dsimp [k,m]
    omega
  calc
    U/P*(Q^2/P^k) = (U*Q^2)/(P*P^k) := div_mul_div_comm _ _ _ _
    _ = (U*Q^2*P^m)/(P*P^k*P^m) := (mul_div_mul_right _ _ (pow_ne_zero _ hP)).symm
    _ = (U*Q^2*P^m)/P^p := by rw [hden]
end Zeta7Auxiliary
end

import Zeta7Proof.HassePolynomialEquation
import Zeta7Proof.HasseResidueArithmetic

/-! Root multiplicities for the actual Hasse differential equation. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
namespace Zeta7Auxiliary
open Polynomial
variable {K : Type*} [Field K]

theorem hassePolyP_eval (a : K) : (hassePolyP : Polynomial K).eval a = 1+13*a+49*a^2 := by
  simp [hassePolyP]
theorem hassePolyP_derivative_eval (a : K) :
    (hassePolyP : Polynomial K).derivative.eval a = 13+98*a := by
  simp [hassePolyP, derivative_add, derivative_mul, derivative_pow]; ring

theorem hasse_P_root_nonzero (a : K) (ha : (hassePolyP : Polynomial K).eval a=0) : a≠0 := by
  intro h; simpa [hassePolyP,h] using ha

theorem hasse_P_discriminant (a : K) (ha : (hassePolyP : Polynomial K).eval a=0) :
    (13+98*a)^2 = -27 := by
  rw [hassePolyP_eval] at ha
  linear_combination 196*ha

theorem hasse_P_root_W (a : K) (ha : (hassePolyP : Polynomial K).eval a=0) :
    (hassePolyW : Polynomial K).eval a=24*a^2 := by
  rw [hassePolyP_eval] at ha
  simp only [hassePolyW, eval_mul, eval_add, eval_pow, eval_natCast, eval_ofNat, eval_X, eval_one]
  linear_combination 8*a*ha

def hasseRootLinear (a : K) : Polynomial K := 49*X+C (13+49*a)

theorem hasseRootLinear_eval (a : K) : (hasseRootLinear a).eval a=13+98*a := by
  simp [hasseRootLinear]; ring

theorem hasse_P_root_factor (a : K) (ha : (hassePolyP : Polynomial K).eval a=0) :
    hassePolyP=(X-C a)*hasseRootLinear a := by
  rw [hassePolyP_eval] at ha
  have h := congrArg (Polynomial.C (R := K)) ha
  simp only [map_add,map_mul,map_pow,map_one,map_ofNat,map_zero] at h
  unfold hassePolyP hasseRootLinear
  simp only [map_add, map_mul, map_ofNat]
  linear_combination h

theorem hasse_singular_indicial (a : K) (n : ℕ) (f : Polynomial K)
    (hf : f ≠ 0) (he : hassePolynomialODE n f=0)
    (ha : (hassePolyP : Polynomial K).eval a=0) (h12 : (12:K)≠0) :
    9*((f.rootMultiplicity a:K)-n)^2-9*((f.rootMultiplicity a:K)-n)+2=0 := by
  let L := hasseRootLinear a
  let A : Polynomial K := 4*X^2*L^2
  let B : Polynomial K := 4*X*(X-C a)*L^2-8*(n:Polynomial K)*X^2*L*hassePolyP.derivative
  have hA : (hassePolyA : Polynomial K)=(X-C a)^2*A := by
    unfold hassePolyA A
    linear_combination 4*X^2*(hassePolyP+(X-C a)*L)*hasse_P_root_factor a ha
  have hB : (hassePolyB n : Polynomial K)=(X-C a)*B := by
    unfold hassePolyB B
    linear_combination (4*X*(hassePolyP+(X-C a)*L)-8*(n:Polynomial K)*X^2*hassePolyP.derivative)*
      hasse_P_root_factor a ha
  have h := polynomial_indicial a f A B (hassePolyC n) hf (by
    rw [centeredEuler_second]
    unfold centeredEuler
    unfold hassePolynomialODE at he
    rw [hA,hB] at he
    linear_combination he)
  simp only [A,B,L,hassePolyC,eval_add,eval_sub,eval_mul,eval_pow,eval_natCast,eval_ofNat,
    eval_X,eval_C,eval_one,hasseRootLinear_eval,hassePolyP_derivative_eval,ha,
    zero_mul,mul_zero,add_zero,sub_zero,sub_self,hasse_P_root_W a ha] at h
  have hd := hasse_P_discriminant a ha
  have h0 : (-12:K)*a^2*(9*((f.rootMultiplicity a:K)-n)^2-
      9*((f.rootMultiplicity a:K)-n)+2)=0 := by
    linear_combination h-4*a^2*((f.rootMultiplicity a:K)^2-
      (f.rootMultiplicity a:K)-2*n*(f.rootMultiplicity a:K)+n*(n+1))*hd
  exact (mul_eq_zero.mp h0).resolve_left
    (mul_ne_zero (neg_ne_zero.mpr h12) (pow_ne_zero _ (hasse_P_root_nonzero a ha)))

variable (p : ℕ) [Fact p.Prime] [CharP K p]

theorem hasse_rootMultiplicity_le_degree (f : Polynomial K) (hf : f≠0) (a : K) :
    f.rootMultiplicity a ≤ f.natDegree := by
  have h := Polynomial.natDegree_le_of_dvd (f.pow_rootMultiplicity_dvd a) hf
  simpa only [natDegree_pow,natDegree_X_sub_C,mul_one] using h

theorem hasse_equation_root_not_P (hp : 11 ≤ p) (f : Polynomial K) (hf : f≠0)
    (hdeg : f.natDegree ≤ 2*((p-1)/3)) (he : hassePolynomialODE ((p-1)/3) f=0)
    (a : K) (ha : f.eval a=0) : (hassePolyP : Polynomial K).eval a≠0 := by
  intro hP
  have hm : 0 < f.rootMultiplicity a := (Polynomial.rootMultiplicity_pos hf).mpr ha
  have hm' : f.rootMultiplicity a ≤ 2*((p-1)/3) :=
    (hasse_rootMultiplicity_le_degree f hf a).trans hdeg
  have h12 : (12:K)≠0 := by
    have h2 := small_natCast_ne_zero (K := K) p 2 (by omega) (by omega)
    have h3 := small_natCast_ne_zero (K := K) p 3 (by omega) (by omega)
    rw [show (12:K)=3*2^2 by ring]
    exact mul_ne_zero h3 (pow_ne_zero _ h2)
  exact singular_multiplicity_impossible (K := K) p (f.rootMultiplicity a) hp hm hm'
    (hasse_singular_indicial a ((p-1)/3) f hf he hP h12)

theorem hasse_equation_root_simple (hp : 11 ≤ p) (f : Polynomial K) (hf : f≠0)
    (hdeg : f.natDegree ≤ 2*((p-1)/3)) (h0 : f.coeff 0=1)
    (he : hassePolynomialODE ((p-1)/3) f=0) (a : K) (ha : f.eval a=0) :
    f.rootMultiplicity a=1 := by
  have hP := hasse_equation_root_not_P p hp f hf hdeg he a ha
  have ha0 : a≠0 := by
    intro hz
    subst a
    rw [← Polynomial.coeff_zero_eq_eval_zero, h0] at ha
    exact one_ne_zero ha
  have h := ordinary_indicial a f hassePolyA (hassePolyB ((p-1)/3))
    (hassePolyC ((p-1)/3)) hf he
  have hA : (hassePolyA : Polynomial K).eval a≠0 := by
    simp only [hassePolyA,eval_mul,eval_pow,eval_X,eval_ofNat]
    have h2 := small_natCast_ne_zero (K := K) p 2 (by omega) (by omega)
    have h4 : (4:K)≠0 := by rw [show (4:K)=2^2 by ring]; exact pow_ne_zero _ h2
    exact mul_ne_zero (mul_ne_zero h4 (pow_ne_zero _ ha0)) (pow_ne_zero _ hP)
  apply ordinary_multiplicity_one (K := K) p (f.rootMultiplicity a) (by omega)
    ((Polynomial.rootMultiplicity_pos hf).mpr ha)
    (lt_of_le_of_lt ((hasse_rootMultiplicity_le_degree f hf a).trans hdeg) (by omega))
  exact (mul_eq_zero.mp h).resolve_left hA

end Zeta7Auxiliary

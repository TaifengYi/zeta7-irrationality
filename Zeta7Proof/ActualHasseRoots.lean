import Zeta7Proof.HassePolynomialRoots

/-! Squarefreeness and coprimality for the original constructed Hasse quotient. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
namespace Zeta7Auxiliary
open Polynomial
variable (p : ℕ) [Fact p.Prime]

theorem reducedQuotient_map_constant {K : Type*} [Field K] (φ : ZMod p →+* K)
    (hp : 5 ≤ p) : ((reducedQuotient p hp).map φ).coeff 0=1 := by
  rw [coeff_map,reducedQuotient_constant,map_one]

theorem reducedQuotient_map_ne_zero {K : Type*} [Field K] (φ : ZMod p →+* K)
    (hp : 5 ≤ p) : (reducedQuotient p hp).map φ≠0 := by
  intro h
  have hh := reducedQuotient_map_constant p φ hp
  rw [h,coeff_zero] at hh
  exact zero_ne_one hh

theorem reducedQuotient_root_not_P {K : Type*} [Field K] [CharP K p]
    (φ : ZMod p →+* K) (hp : 11 ≤ p) (a : K)
    (ha : ((reducedQuotient p (by omega)).map φ).eval a=0) :
    (hassePolyP : Polynomial K).eval a≠0 := by
  apply hasse_equation_root_not_P p hp _ (reducedQuotient_map_ne_zero p φ (by omega))
    (by rw [natDegree_map,reducedQuotient_degree p hp])
    (reducedQuotient_polynomialODE_map p φ (by omega)) a ha

theorem reducedQuotient_root_simple {K : Type*} [Field K] [CharP K p]
    (φ : ZMod p →+* K) (hp : 11 ≤ p) (a : K)
    (ha : ((reducedQuotient p (by omega)).map φ).eval a=0) :
    ((reducedQuotient p (by omega)).map φ).rootMultiplicity a=1 := by
  apply hasse_equation_root_simple p hp _ (reducedQuotient_map_ne_zero p φ (by omega))
    (by rw [natDegree_map,reducedQuotient_degree p hp])
    (reducedQuotient_map_constant p φ (by omega))
    (reducedQuotient_polynomialODE_map p φ (by omega)) a ha

theorem reducedQuotient_coprime (hp : 11 ≤ p) :
    IsCoprime (reducedQuotient p (by omega)) (hassePolyP : Polynomial (ZMod p)) := by
  apply (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed
    (k := ZMod p) (AlgebraicClosure (ZMod p)) _ _).mpr
  intro a
  by_cases ha : aeval a (reducedQuotient p (by omega))=0
  · right
    have hh := reducedQuotient_root_not_P p (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))
      hp a (by simpa only [eval_map_algebraMap] using ha)
    simpa [hassePolyP, map_ofNat] using hh
  · exact Or.inl ha

theorem reducedQuotient_separable (hp : 11 ≤ p) :
    (reducedQuotient p (by omega)).Separable := by
  rw [separable_def]
  apply (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed
    (k := ZMod p) (AlgebraicClosure (ZMod p)) _ _).mpr
  intro a
  by_cases ha : aeval a (reducedQuotient p (by omega))=0
  · right
    intro hd
    let φ := algebraMap (ZMod p) (AlgebraicClosure (ZMod p))
    let f := (reducedQuotient p (by omega)).map φ
    have hfa : f.IsRoot a := by simpa only [f,φ,Polynomial.IsRoot,eval_map_algebraMap] using ha
    have hfd : f.derivative.IsRoot a := by
      simpa only [f,φ,Polynomial.IsRoot,derivative_map,eval_map_algebraMap] using hd
    have hm := (one_lt_rootMultiplicity_iff_isRoot
      (reducedQuotient_map_ne_zero p φ (by omega))).mpr ⟨hfa,hfd⟩
    have h1 := reducedQuotient_root_simple p φ hp a hfa
    omega
  · exact Or.inl ha

theorem reducedQuotient_squarefree (hp : 11 ≤ p) :
    Squarefree (reducedQuotient p (by omega)) := (reducedQuotient_separable p hp).squarefree

theorem hassePolyP_separable (hp : 11 ≤ p) : (hassePolyP : Polynomial (ZMod p)).Separable := by
  rw [separable_def]
  apply (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed
    (k := ZMod p) (AlgebraicClosure (ZMod p)) _ _).mpr
  intro a
  by_cases ha : (hassePolyP : Polynomial (AlgebraicClosure (ZMod p))).eval a=0
  · right
    intro hd
    have hd' : ((hassePolyP : Polynomial (AlgebraicClosure (ZMod p))).derivative).eval a=0 := by
      simpa [hassePolyP,derivative_add,derivative_mul,derivative_pow,map_ofNat] using hd
    rw [hassePolyP_derivative_eval] at hd'
    have hdisc := hasse_P_discriminant a ha
    have h3 := small_natCast_ne_zero (K := AlgebraicClosure (ZMod p)) p 3 (by omega) (by omega)
    have h27 : (27:AlgebraicClosure (ZMod p))≠0 := by
      rw [show (27:AlgebraicClosure (ZMod p))=3^3 by ring]
      exact pow_ne_zero _ h3
    rw [hd',zero_pow (by decide),eq_neg_iff_add_eq_zero,zero_add] at hdisc
    exact h27 hdisc
  · left
    simpa [hassePolyP, map_ofNat] using ha

end Zeta7Auxiliary

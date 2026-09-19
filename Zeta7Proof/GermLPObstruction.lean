import Zeta7Proof.GermIndicialAlgebra

/-! Exact rational calculation at the final degree-reduced step of N1. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
open scoped RatFunc
namespace Zeta7Germ

@[simp] theorem rationalD_ofNat (n : ℕ) [n.AtLeastTwo] :
    rationalD (OfNat.ofNat n : RatFunc ℂ) = 0 := rationalD.map_natCast n

@[simp] theorem rationalD_constant (a : ℂ) : rationalD (RatFunc.C a) = 0 :=
  rationalD.map_algebraMap a

@[simp] theorem rationalD_X : rationalD (RatFunc.X : RatFunc ℂ) = RatFunc.X := by
  have h := rationalD_polynomial (Polynomial.X : Polynomial ℂ)
  simpa [RatFunc.coePolynomial_eq_algebraMap] using h

theorem rationalD_P : rationalD P = 13 * RatFunc.X + 98 * RatFunc.X ^ 2 := by
  simp only [P, map_add, Derivation.map_one_eq_zero, Derivation.leibniz,
    Derivation.leibniz_pow, smul_eq_mul, rationalD_X, rationalD_ofNat,
    Derivation.map_natCast, map_zero]
  have h13 : rationalD (13 : RatFunc ℂ) = 0 := rationalD.map_natCast 13
  have h49 : rationalD (49 : RatFunc ℂ) = 0 := rationalD.map_natCast 49
  simp only [h13, h49]
  ring

theorem LP_cleared : P * L P = RatFunc.X * (obstructionPolynomial : RatFunc ℂ) := by
  have hp : (1 + 13 * RatFunc.X + 49 * RatFunc.X ^ 2 : RatFunc ℂ) ≠ 0 := P_ne_zero
  have h2 : rationalD (2 : RatFunc ℂ) = 0 := rationalD.map_natCast 2
  have h8 : rationalD (8 : RatFunc ℂ) = 0 := rationalD.map_natCast 8
  have h13 : rationalD (13 : RatFunc ℂ) = 0 := rationalD.map_natCast 13
  have h16 : rationalD (16 : RatFunc ℂ) = 0 := rationalD.map_natCast 16
  have h49 : rationalD (49 : RatFunc ℂ) = 0 := rationalD.map_natCast 49
  have h98 : rationalD (98 : RatFunc ℂ) = 0 := rationalD.map_natCast 98
  have h196 : rationalD (196 : RatFunc ℂ) = 0 := rationalD.map_natCast 196
  have hx2 : rationalD (RatFunc.X ^ 2 : RatFunc ℂ) = 2 * RatFunc.X ^ 2 := by
    simp only [Derivation.leibniz_pow, rationalD_X, smul_eq_mul]
    ring
  have hd2 : rationalD (rationalD P) = 13 * RatFunc.X + 196 * RatFunc.X ^ 2 := by
    rw [rationalD_P]
    simp only [map_add, Derivation.leibniz, smul_eq_mul, h13, h98, rationalD_X, hx2]
    ring
  have hd3 : rationalD (rationalD (rationalD P)) = 13 * RatFunc.X + 392 * RatFunc.X ^ 2 := by
    rw [hd2]
    simp only [map_add, Derivation.leibniz, smul_eq_mul, h13, h196, rationalD_X, hx2]
    ring
  let W : RatFunc ℂ := 8 * RatFunc.X * (1 + 16 * RatFunc.X + 49 * RatFunc.X ^ 2)
  have hW : P ^ 2 * V = W := by
    rw [V]
    dsimp [W]
    field_simp [P_ne_zero]
  have hDW : rationalD W = 8 * RatFunc.X + 256 * RatFunc.X ^ 2 + 1176 * RatFunc.X ^ 3 := by
    dsimp [W]
    simp only [map_add, Derivation.leibniz, smul_eq_mul, h8, h16, h49,
      rationalD_X, hx2, Derivation.map_one_eq_zero]
    ring
  have hd := congrArg rationalD hW
  simp only [Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul] at hd
  have hpcalc : 2 * P * rationalD (rationalD (rationalD P)) - rationalD W =
      2 * RatFunc.X * (obstructionPolynomial : RatFunc ℂ) := by
    rw [hd3, hDW]
    simp only [P, obstructionPolynomial, RatFunc.coePolynomial_eq_algebraMap,
      map_add, map_mul, map_pow, map_ofNat, RatFunc.algebraMap_X]
    ring
  apply mul_left_cancel₀ (show (2 : RatFunc ℂ) ≠ 0 by norm_num)
  simp only [RatFunc.coePolynomial_eq_algebraMap] at hpcalc ⊢
  dsimp [L]
  linear_combination hpcalc - hd

theorem no_scalar_P_solution (a : ℂ) (h : Polynomial ℂ) (hh : h ≠ 0) :
    L (RatFunc.C a * P) ≠ (h : RatFunc ℂ) * R := by
  intro he
  have hc : rationalD (RatFunc.C a) = 0 := by
    change rationalD ((algebraMap ℂ (RatFunc ℂ)) a) = 0
    exact rationalD.map_algebraMap a
  have hL : L (RatFunc.C a * P) = RatFunc.C a * L P := by
    simp [L, Derivation.leibniz, smul_eq_mul, hc]
    ring
  rw [hL] at he
  have he' := congrArg (fun f : RatFunc ℂ => P * f) he
  have hr : P * R = RatFunc.X * (1 + 10 * RatFunc.X) := by
    rw [R]
    field_simp [P_ne_zero]
  have hx : (RatFunc.X : RatFunc ℂ) ≠ 0 := RatFunc.X_ne_zero
  have ht : RatFunc.C a * (obstructionPolynomial : RatFunc ℂ) =
      (h : RatFunc ℂ) * (1 + 10 * RatFunc.X) := by
    apply mul_left_cancel₀ hx
    linear_combination he' - RatFunc.C a * LP_cleared + (h : RatFunc ℂ) * hr
  have hpoly : Polynomial.C a * obstructionPolynomial = (1 + 10 * Polynomial.X) * h := by
    apply (IsFractionRing.injective (Polynomial ℂ) (RatFunc ℂ))
    simpa [map_mul, map_add, RatFunc.algebraMap_C, RatFunc.algebraMap_X, mul_comm,
      RatFunc.coePolynomial_eq_algebraMap, map_ofNat] using ht
  have ha := obstruction_cleared_implies_zero h a hpoly.symm
  subst a
  simp only [Polynomial.C_0, zero_mul] at hpoly
  have hz : h = 0 := by
    apply (mul_eq_zero.mp hpoly.symm).resolve_left
    · intro hlin
      have hz := congrArg (Polynomial.eval (0 : ℂ)) hlin
      norm_num at hz
  exact hh hz

end Zeta7Germ

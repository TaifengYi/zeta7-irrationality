import Zeta7Proof.ActualSevenAdicRoots
import Zeta7Proof.ActualTargetClearedEquation
import Zeta7Proof.SevenAdicSeriesEvaluation

/-! Actual cancellation obtained by evaluating the cleared target equation at the inner root. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
open PowerSeries
namespace Zeta7Common
open Zeta7Main
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

abbrev UnitDiscSeries := IsRestricted.subring (R := ℚ_[7]) 1

def unitDiscValue (a : ℚ_[7]) (ha : ‖a‖ ≤ 1) : UnitDiscSeries →+* ℚ_[7] where
  toFun f := seriesValue f.val a
  map_zero' := by simpa using seriesValue_C 0 a
  map_one' := by simpa using seriesValue_C 1 a
  map_add' f g := seriesValue_add (by norm_num) _ _ f.property g.property a ha
  map_mul' f g := seriesValue_mul (by norm_num) _ _ f.property g.property a ha

def unitDiscEuler (f : UnitDiscSeries) : UnitDiscSeries :=
  ⟨euler f.val, restricted_euler (by norm_num) f.property⟩

def unitDiscPolynomial (p : Polynomial ℚ_[7]) : UnitDiscSeries :=
  ⟨p, restricted_polynomial p 1⟩

theorem unitDisc_sub_val (f g : UnitDiscSeries) :
    (f - g).val = f.val - g.val := rfl

theorem unitDiscEuler_val (f : UnitDiscSeries) :
    (unitDiscEuler f).val = euler f.val := rfl

theorem unitDiscValue_polynomial (a : ℚ_[7]) (ha : ‖a‖ ≤ 1) (p : Polynomial ℚ_[7]) :
    unitDiscValue a ha (unitDiscPolynomial p) = p.eval a := seriesValue_polynomial p a

theorem polynomial_euler_seven (p : Polynomial ℚ_[7]) :
    euler (p : ℚ_[7]⟦X⟧) = ((Polynomial.X * p.derivative : Polynomial ℚ_[7]) : ℚ_[7]⟦X⟧) := by
  simp [euler, Polynomial.coe_mul, Polynomial.coe_X, derivative_coe]

theorem polynomial_natCast_seven (n : ℕ) :
    ((n : Polynomial ℚ_[7]) : ℚ_[7]⟦X⟧) = n :=
  map_natCast Polynomial.coeToPowerSeries.ringHom n

theorem unitDiscValue_euler_polynomial (a : ℚ_[7]) (ha : ‖a‖ ≤ 1)
    (p : Polynomial ℚ_[7]) :
    unitDiscValue a ha (unitDiscEuler (unitDiscPolynomial p)) =
      (Polynomial.X * p.derivative).eval a := by
  exact (congrArg (fun f => seriesValue f a) (polynomial_euler_seven p)).trans
    (seriesValue_polynomial _ a)

set_option maxHeartbeats 200000 in
theorem HSeries_inner_root_zero : seriesValue HSeries innerPotentialRoot = 0 := by
  let p : UnitDiscSeries := unitDiscPolynomial (1 + 13 * Polynomial.X + 49 * Polynomial.X ^ 2)
  let w : UnitDiscSeries := unitDiscPolynomial
    (8 * Polynomial.X * (1 + 16 * Polynomial.X + 49 * Polynomial.X ^ 2))
  let s : UnitDiscSeries := unitDiscPolynomial (Polynomial.X * (1 + 10 * Polynomial.X))
  let h : UnitDiscSeries := ⟨HSeries, HSeries_isRestricted 1 (by norm_num) (by norm_num)⟩
  let half : UnitDiscSeries := unitDiscPolynomial (Polynomial.C (1 / 2 : ℚ_[7]))
  have hx : Polynomial.coeToPowerSeries.ringHom (Polynomial.X : Polynomial ℚ_[7]) = X :=
    Polynomial.coe_X
  have hp : p.val = targetP := by
    norm_num [p, unitDiscPolynomial, targetP, ← Polynomial.coeToPowerSeries.ringHom_apply, map_ofNat, hx]
  have hw : w.val = targetW := by
    norm_num [w, unitDiscPolynomial, targetW, ← Polynomial.coeToPowerSeries.ringHom_apply, map_ofNat, hx]
  have hs : s.val = targetS := by
    norm_num [s, unitDiscPolynomial, targetS, ← Polynomial.coeToPowerSeries.ringHom_apply, map_ofNat, hx]
  have he : p ^ 3 * unitDiscEuler (unitDiscEuler (unitDiscEuler h)) -
      p * w * unitDiscEuler h +
      (w * unitDiscEuler p - half * p * unitDiscEuler w) * h = p ^ 2 * s := by
    apply Subtype.ext
    simp only [unitDisc_sub_val, Subring.coe_add, Subring.coe_mul, Subring.coe_pow,
      unitDiscEuler_val, hp, hw, hs]
    simpa only [h, half, unitDiscPolynomial, Polynomial.coe_C] using
      HSeries_cleared_differential_equation
  let ev := unitDiscValue innerPotentialRoot innerPotentialRoot_norm.le
  have ep : ev p = 0 := by
    rw [unitDiscValue_polynomial]
    simpa [map_ofNat] using innerPotentialRoot_equation
  have ew : ev w = 24 * innerPotentialRoot ^ 2 := by
    rw [unitDiscValue_polynomial]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_one, Polynomial.eval_X, Polynomial.eval_ofNat]
    linear_combination 8 * innerPotentialRoot * innerPotentialRoot_equation
  have edp : ev (unitDiscEuler p) = innerPotentialRoot * (13 + 98 * innerPotentialRoot) := by
    rw [unitDiscValue_euler_polynomial]
    simp [Polynomial.derivative_mul, map_ofNat]
    ring_nf
    simp
  have en : ev w * ev (unitDiscEuler p) ≠ 0 := by
    rw [ew, edp]
    exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ innerPotentialRoot_ne_zero))
      (mul_ne_zero innerPotentialRoot_ne_zero (potential_root_simple _ innerPotentialRoot_equation))
  have hh := congrArg ev he
  simp only [map_add, map_sub, map_mul, map_pow, ep, zero_pow (by decide : 3 ≠ 0),
    zero_pow (by decide : 2 ≠ 0), zero_mul, mul_zero, sub_zero, zero_sub, neg_zero, zero_add] at hh
  exact (mul_eq_zero.mp hh).resolve_left en

end Zeta7Common

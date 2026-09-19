import Zeta7Proof.HasseClearingCalculus
import Zeta7Proof.HasseIndicial

/-! The exact polynomial ODE satisfied by the actual reduced Hasse quotient. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
namespace Zeta7Auxiliary
open Polynomial Zeta7Common
variable {K : Type*} [CommRing K]

@[simp] theorem hassePolynomial_coe_natCast (n : ℕ) :
    ((n : Polynomial K) : PowerSeries K) = (n : PowerSeries K) :=
  map_natCast coeToPowerSeries.ringHom n

@[simp] theorem hassePolynomial_coe_ofNat (n : ℕ) [n.AtLeastTwo] :
    ((ofNat(n) : Polynomial K) : PowerSeries K) = (ofNat(n) : PowerSeries K) :=
  map_ofNat coeToPowerSeries.ringHom n

def hassePolyP : Polynomial K := 1+13*X+49*X^2
def hassePolyW : Polynomial K := 8*X*(1+16*X+49*X^2)
def hassePolyA : Polynomial K := 4*X^2*hassePolyP^2
def hassePolyB (n : ℕ) : Polynomial K :=
  4*X*hassePolyP^2-8*(n:Polynomial K)*X^2*hassePolyP*hassePolyP.derivative
def hassePolyC (n : ℕ) : Polynomial K :=
  4*(n:Polynomial K)*((n:Polynomial K)+1)*X^2*hassePolyP.derivative^2 -
    4*(n:Polynomial K)*hassePolyP*(X*hassePolyP.derivative+
      X^2*hassePolyP.derivative.derivative)-hassePolyW
def hassePolynomialODE (n : ℕ) (f : Polynomial K) : Polynomial K :=
  hassePolyA*f.derivative.derivative+hassePolyB n*f.derivative+hassePolyC n*f

theorem hassePolyP_coe : ((hassePolyP : Polynomial K) : PowerSeries K) = hasseP := by
  simp [hassePolyP, hasseP, map_ofNat]
theorem hassePolyW_coe : ((hassePolyW : Polynomial K) : PowerSeries K) = hasseW := by
  simp [hassePolyW, hasseW, map_ofNat]

theorem hassePolynomialODE_coe (n : ℕ) (f : Polynomial K) :
    (hassePolynomialODE n f : PowerSeries K) = hasseSeriesODE n (f:PowerSeries K) := by
  have hP : PowerSeries.derivative K hasseP =
      ((hassePolyP : Polynomial K).derivative : PowerSeries K) := by
    rw [← hassePolyP_coe, PowerSeries.derivative_coe]
  simp only [hassePolynomialODE, hassePolyA, hassePolyB, hassePolyC, hasseSeriesODE,
    coe_add, coe_sub, coe_mul, coe_pow, hassePolynomial_coe_natCast,
    hassePolynomial_coe_ofNat, coe_one, coe_X,
    hassePolyP_coe, hassePolyW_coe, euler, Derivation.leibniz, smul_eq_mul,
    PowerSeries.derivative_X, one_mul, mul_one, hP, PowerSeries.derivative_coe]
  ring

theorem map_hassePolynomialODE {L : Type*} [CommRing L] (φ : K →+* L)
    (n : ℕ) (f : Polynomial K) :
    (hassePolynomialODE n f).map φ = hassePolynomialODE n (f.map φ) := by
  simp [hassePolynomialODE, hassePolyA, hassePolyB, hassePolyC, hassePolyP, hassePolyW,
    derivative_map, Polynomial.map_mul, map_ofNat]

variable (p : ℕ) [Fact p.Prime]

theorem reducedQuotient_polynomialODE (hp : 5 ≤ p) :
    hassePolynomialODE ((p-1)/3) (reducedQuotient p hp)=0 := by
  apply Polynomial.coe_injective (ZMod p)
  rw [hassePolynomialODE_coe, Polynomial.coe_zero]
  exact reducedQuotient_seriesODE p hp

theorem reducedQuotient_polynomialODE_map {L : Type*} [CommRing L]
    (φ : ZMod p →+* L) (hp : 5 ≤ p) :
    hassePolynomialODE ((p-1)/3) ((reducedQuotient p hp).map φ)=0 := by
  rw [← map_hassePolynomialODE, reducedQuotient_polynomialODE, Polynomial.map_zero]

end Zeta7Auxiliary

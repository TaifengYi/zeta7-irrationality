import Zeta7Proof.HasseReducedRiccati

/-! Exact power clearing for the actual second-order equation. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
namespace Zeta7Auxiliary
open PowerSeries Zeta7Common
variable {K : Type*} [CommRing K]

theorem euler_natCast (n : ℕ) : euler (n : PowerSeries K) = 0 := by
  rw [← map_natCast (C (R := K)) n]
  simp [euler]

theorem euler_pow_cleared (P : PowerSeries K) (n : ℕ) :
    P*euler (P^n) = (n:PowerSeries K)*P^n*euler P := by
  induction n with
  | zero => simp [euler]
  | succ n ih =>
    rw [pow_succ, euler_mul_general, Nat.cast_add, Nat.cast_one]
    linear_combination P*ih

theorem euler_pow_twice_cleared (P : PowerSeries K) (n : ℕ) :
    P^2*euler (euler (P^n)) =
      (n:PowerSeries K)*(n-1)*P^n*(euler P)^2 + n*P*P^n*euler (euler P) := by
  have h := congrArg euler (euler_pow_cleared P n)
  simp only [euler_mul_general, euler_natCast, zero_mul, zero_add] at h
  linear_combination P*h + ((n:PowerSeries K)-1)*euler P*euler_pow_cleared P n

def hasseSeriesODE (n : ℕ) (f : PowerSeries K) : PowerSeries K :=
  4*hasseP^2*euler (euler f) - 8*(n:PowerSeries K)*hasseP*euler hasseP*euler f +
    (4*(n:PowerSeries K)*((n:PowerSeries K)+1)*(euler hasseP)^2 -
      4*(n:PowerSeries K)*hasseP*euler (euler hasseP)-hasseW)*f

theorem hasseSeriesODE_clearing (n : ℕ) (Y : PowerSeries K)
    (hY : 4*hasseP^2*euler (euler Y)=hasseW*Y) :
    hasseSeriesODE n (hasseP^n*Y)=0 := by
  unfold hasseSeriesODE
  have hadd (a b : PowerSeries K) : euler (a+b)=euler a+euler b :=
    eulerLinear.map_add a b
  simp only [euler_mul_general, hadd]
  linear_combination 4*Y*euler_pow_twice_cleared (K := K) hasseP n +
    (8*hasseP*euler Y-8*(n:PowerSeries K)*euler hasseP*Y)*euler_pow_cleared (K := K) hasseP n +
    hasseP^n*hY

variable (p : ℕ) [Fact p.Prime]

theorem hasseRootSeries_clearing (hp : 5 ≤ p) :
    (reducedP p)^((p-1)/3)*hasseRootSeries p hp =
      (reducedQuotient p hp : PowerSeries (ZMod p)) := by
  unfold hasseRootSeries
  calc
    _ = (reducedP p*(reducedP p)⁻¹)^((p-1)/3)*
        (reducedQuotient p hp : PowerSeries (ZMod p)) := by rw [mul_pow]; ring
    _ = _ := by rw [reducedP_mul_inv, one_pow, one_mul]

theorem reducedQuotient_seriesODE (hp : 5 ≤ p) :
    hasseSeriesODE ((p-1)/3) (reducedQuotient p hp : PowerSeries (ZMod p))=0 := by
  rw [← hasseRootSeries_clearing p hp, reducedP_value]
  apply hasseSeriesODE_clearing
  simpa only [reducedP_value, hasseP] using hasseRootSeries_equation p hp

end Zeta7Auxiliary

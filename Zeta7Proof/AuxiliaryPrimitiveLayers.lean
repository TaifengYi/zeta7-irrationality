import Zeta7Proof.AuxiliaryResidueCalculus
import Zeta7Proof.AuxiliaryPrimitiveCaps

/-! Actual fourth-layer coefficients, including the exceptional integration classes.
All ranges are strict: a cap at N controls precisely the coefficients n < N. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
namespace Zeta7Auxiliary
open PowerSeries Zeta7Common
variable {p : ℕ} [Fact p.Prime]

def layerAt {N e : ℕ} {F : PowerSeries ℚ_[p]} (h : Cap N e F)
    (n : ℕ) (hn : n < N) : ZMod p := layerCoefficient h ⟨n, hn⟩

theorem layerAt_euler {N e : ℕ} {F : PowerSeries ℚ_[p]}
    (h : Cap N e F) (n : ℕ) (hn : n < N) :
    layerAt h.euler n hn = (n : ZMod p)*layerAt h n hn :=
  layerCoefficient_euler h ⟨n, hn⟩

theorem layerAt_zero_of_euler_cap {N e : ℕ} {F : PowerSeries ℚ_[p]}
    (hF : Cap N (e+1) F) (hD : Cap N e (euler F))
    (n : ℕ) (hn : n < N) (hpn : ¬p ∣ n) : layerAt hF n hn = 0 := by
  have hz := layerCoefficient_mono_succ hD hF.euler ⟨n, hn⟩
  rw [layerCoefficient_euler] at hz
  exact (mul_eq_zero.mp hz).resolve_left ((ZMod.natCast_eq_zero_iff n p).not.mpr hpn)

theorem primitive_layer_regular {N e : ℕ} {F : PowerSeries ℚ_[p]}
    (hF : Cap N e F) (hJ : Cap N e (primitive F))
    (n : ℕ) (hn : n < N) (hpn : ¬p ∣ n) :
    layerAt hJ n hn = layerAt hF (n-1) (by omega) / (n : ZMod p) := by
  have hn0 : n ≠ 0 := fun h => hpn (h ▸ dvd_zero p)
  have hnQ : (n : ℚ_[p]) ≠ 0 := by exact_mod_cast hn0
  apply (eq_div_iff ((ZMod.natCast_eq_zero_iff n p).not.mpr hpn)).mpr
  rw [mul_comm]
  apply integralResidue_nat_mul_eq (hJ n hn) (hF (n-1) (by omega)) n
  simp only [primitive, coeff_mk, if_neg hn0]
  field_simp

theorem primitive_layer_exceptional {N e : ℕ} {F : PowerSeries ℚ_[p]}
    (hJ : Cap N (e+1) (primitive F)) (hD : Cap N e (euler F))
    (m : ℕ) (hm : 0 < m) (hn : m*p < N) :
    (m : ZMod p)*layerAt hJ (m*p) hn =
      -layerAt hD (m*p-1) (by omega) := by
  have hp0 := (Fact.out : p.Prime).pos
  have hn0 : m*p ≠ 0 := by positivity
  have hnQ : (m*p : ℚ_[p]) ≠ 0 := by exact_mod_cast hn0
  have hmQ : (m : ℚ_[p]) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hpQ : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hp0)
  have h := integralResidue_nat_mul_eq (hJ (m*p) hn) (hD (m*p-1) (by omega))
    ((m*p-1)*m) (by
      simp only [primitive, coeff_mk, if_neg hn0, euler_coeff]
      push_cast
      field_simp [hmQ, hpQ, pow_succ]
      ring)
  have hcast : ((m*p-1 : ℕ) : ZMod p) = -1 := by
    rw [Nat.cast_sub (by nlinarith : 1 ≤ m*p)]
    simp
  simp only [Nat.cast_mul, hcast, neg_one_mul] at h
  simpa only [neg_mul, neg_eq_iff_eq_neg, layerAt, layerCoefficient, integralResidue] using h

theorem primitive_twice_layer_regular {N e : ℕ} {F : PowerSeries ℚ_[p]}
    (hF : Cap N e F) (hJ : Cap N e (primitive F))
    (hJJ : Cap N e (primitive (primitive F)))
    (n : ℕ) (hn : n < N) (hpn : ¬p ∣ n) (hpm : ¬p ∣ n-1) :
    layerAt hJJ n hn = layerAt hF (n-2) (by omega) /
      ((n : ZMod p)*((n-1 : ℕ) : ZMod p)) := by
  rw [primitive_layer_regular hJ hJJ n hn hpn,
    primitive_layer_regular hF hJ (n-1) (by omega) hpm]
  simp only [Nat.sub_sub, div_div, mul_comm]

theorem primitive_twice_layer_exceptional {N e : ℕ} {F : PowerSeries ℚ_[p]}
    (hJJ : Cap N (e+1) (primitive (primitive F))) (hD : Cap N e (euler F))
    (m : ℕ) (hm : 0 < m) (hp : 2 < p) (hn : m*p < N) :
    (2 : ZMod p)*m*layerAt hJJ (m*p) hn =
      layerAt hD (m*p-2) (by omega) := by
  have hmp : 3 ≤ m*p := by nlinarith
  have hn0 : m*p ≠ 0 := by omega
  have hm0 : m*p-1 ≠ 0 := by omega
  have hnQ : (m*p : ℚ_[p]) ≠ 0 := by exact_mod_cast hn0
  have hmQ' : (m : ℚ_[p]) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hpQ : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
  have hmQ : ((m*p-1 : ℕ) : ℚ_[p]) ≠ 0 := by exact_mod_cast hm0
  have h := integralResidue_nat_mul_eq (hJJ (m*p) hn) (hD (m*p-2) (by omega))
    ((m*p-2)*(m*p-1)*m) (by
      simp only [primitive, coeff_mk, if_neg hn0, if_neg hm0, Nat.sub_sub, euler_coeff]
      push_cast
      field_simp [hmQ', hpQ, hmQ, pow_succ]
      ring)
  have hc1 : ((m*p-1 : ℕ) : ZMod p) = -1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ m*p)]; simp
  have hc2 : ((m*p-2 : ℕ) : ZMod p) = -2 := by
    rw [Nat.cast_sub (by omega : 2 ≤ m*p)]; simp
  simpa only [Nat.cast_mul, hc1, hc2, neg_mul_neg, mul_one,
    layerAt, layerCoefficient, integralResidue] using h

theorem primitive_twice_layer_exceptional_succ {N e : ℕ} {F : PowerSeries ℚ_[p]}
    (hJ : Cap N (e+1) (primitive F))
    (hJJ : Cap N (e+1) (primitive (primitive F))) (hD : Cap N e (euler F))
    (m : ℕ) (hm : 0 < m) (hn : m*p+1 < N) :
    (m : ZMod p)*layerAt hJJ (m*p+1) hn =
      -layerAt hD (m*p-1) (by omega) := by
  have hpn : ¬p ∣ m*p+1 := by
    intro h
    have := Nat.dvd_sub h (dvd_mul_left p m)
    simp only [Nat.add_sub_cancel_left] at this
    exact (Fact.out : p.Prime).not_dvd_one this
  rw [primitive_layer_regular hJ hJJ (m*p+1) hn hpn]
  simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_mul, ZMod.natCast_self,
    mul_zero, Nat.cast_one, zero_add, div_one]
  exact primitive_layer_exceptional hJ hD m hm (by omega)

/-- All residues outside 0 and 1 vanish for the first primitive. -/
theorem primitive_layer_support {N e : ℕ} {F : PowerSeries ℚ_[p]}
    (hF : Cap N (e+1) F) (hJ : Cap N (e+1) (primitive F))
    (hD : Cap N e (euler F)) (n : ℕ) (hn : n < N)
    (hpn : ¬p ∣ n) (hpm : ¬p ∣ n-1) : layerAt hJ n hn = 0 := by
  rw [primitive_layer_regular hF hJ n hn hpn,
    layerAt_zero_of_euler_cap hF hD (n-1) (by omega) hpm, zero_div]

/-- All residues outside 0, 1 and 2 vanish for the second primitive. -/
theorem primitive_twice_layer_support {N e : ℕ} {F : PowerSeries ℚ_[p]}
    (hF : Cap N (e+1) F) (hJ : Cap N (e+1) (primitive F))
    (hJJ : Cap N (e+1) (primitive (primitive F)))
    (hD : Cap N e (euler F)) (n : ℕ) (hn : n < N)
    (hpn : ¬p ∣ n) (hpm : ¬p ∣ n-1) (hpl : ¬p ∣ n-2) : layerAt hJJ n hn = 0 := by
  rw [primitive_twice_layer_regular hF hJ hJJ n hn hpn hpm,
    layerAt_zero_of_euler_cap hF hD (n-2) (by omega) hpl, zero_div]

abbrev actualPrimeK (p : ℕ) [Fact p.Prime] (c : ℚ) : PowerSeries ℚ_[p] :=
  (quadratic rationalPotential (rationalH c)).map (algebraMap ℚ ℚ_[p])

def actualKFourth (c : ℚ) (hc : ¬p ∣ c.den) (N : ℕ) (hN : N ≤ p^2)
    (n : ℕ) (hn : n < N) : ZMod p := layerAt (rationalK_cap_four c hc N hN) n hn

def actualJ1Fourth (c : ℚ) (hc : ¬p ∣ c.den) (N : ℕ) (hN : N ≤ p^2)
    (n : ℕ) (hn : n < N) : ZMod p := layerAt (rationalJ1_cap_four c hc N hN) n hn

def actualJ2Fourth (hp : 2 < p) (c : ℚ) (hc : ¬p ∣ c.den) (N : ℕ) (hN : N ≤ p^2)
    (n : ℕ) (hn : n < N) : ZMod p := layerAt (rationalJ2_cap_four hp c hc N hN) n hn

def actualDKThird (c : ℚ) (hc : ¬p ∣ c.den) (N : ℕ) (hN : N ≤ p^2)
    (n : ℕ) (hn : n < N) : ZMod p := layerAt (rationalK_euler_cap_three c hc N hN) n hn

theorem actualK_fourth_support (c : ℚ) (hc : ¬p ∣ c.den) (N : ℕ) (hN : N ≤ p^2)
    (n : ℕ) (hn : n < N) (hpn : ¬p ∣ n) : actualKFourth c hc N hN n hn = 0 :=
  layerAt_zero_of_euler_cap (rationalK_cap_four c hc N hN)
    (rationalK_euler_cap_three c hc N hN) n hn hpn

theorem actualJ1_fourth_regular (c : ℚ) (hc : ¬p ∣ c.den) (N : ℕ) (hN : N ≤ p^2)
    (n : ℕ) (hn : n < N) (hpn : ¬p ∣ n) :
    actualJ1Fourth c hc N hN n hn = actualKFourth c hc N hN (n-1) (by omega) / (n : ZMod p) := by
  have hJ : Cap N 4 (primitive (actualPrimeK p c)) := by
    simpa only [map_primitive] using rationalJ1_cap_four c hc N hN
  simpa only [actualJ1Fourth, actualKFourth, map_primitive] using
    primitive_layer_regular (rationalK_cap_four c hc N hN) hJ n hn hpn

theorem actualJ2_fourth_regular (hp : 2 < p) (c : ℚ) (hc : ¬p ∣ c.den)
    (N : ℕ) (hN : N ≤ p^2) (n : ℕ) (hn : n < N)
    (hpn : ¬p ∣ n) (hpm : ¬p ∣ n-1) :
    actualJ2Fourth hp c hc N hN n hn = actualKFourth c hc N hN (n-2) (by omega) /
      ((n : ZMod p)*((n-1 : ℕ) : ZMod p)) := by
  have hJ : Cap N 4 (primitive (actualPrimeK p c)) := by
    simpa only [map_primitive] using rationalJ1_cap_four c hc N hN
  have hJJ : Cap N 4 (primitive (primitive (actualPrimeK p c))) := by
    simpa only [map_primitive] using rationalJ2_cap_four hp c hc N hN
  simpa only [actualJ2Fourth, actualKFourth, map_primitive] using
    primitive_twice_layer_regular (rationalK_cap_four c hc N hN) hJ hJJ n hn hpn hpm

theorem layerAt_eq_zero {N e : ℕ} {F : PowerSeries ℚ_[p]} (h : Cap N e F)
    (n : ℕ) (hn : n < N) (hz : coeff n F = 0) : layerAt h n hn = 0 := by
  let a : ℤ_[p] := ⟨(p : ℚ_[p])^e*coeff n F, h n hn⟩
  have he : a = (0 : ℤ_[p]) := by
    apply Subtype.ext
    change (p : ℚ_[p])^e*coeff n F = 0
    rw [hz, mul_zero]
  change PadicInt.toZMod a = 0
  rw [he, map_zero]

/-- The prescribed integration constants handle all initial indices. -/
theorem actual_primitive_fourth_initial (hp : 2 < p) (c : ℚ) (hc : ¬p ∣ c.den)
    (N : ℕ) (hN : N ≤ p^2) :
    (∀ n, n < 2 → (hn : n < N) → actualJ1Fourth c hc N hN n hn = 0) ∧
    (∀ n, n < 3 → (hn : n < N) → actualJ2Fourth hp c hc N hN n hn = 0) := by
  constructor
  · intro n hsmall hn
    apply layerAt_eq_zero
    interval_cases n <;> simp [coeff_map, primitive, rationalK_constant]
  · intro n hsmall hn
    apply layerAt_eq_zero
    interval_cases n <;> simp [coeff_map, primitive, rationalK_constant]

/-- The original first primitive's carry, with its exact sign and short divisor. -/
theorem actualJ1_fourth_carry (c : ℚ) (hc : ¬p ∣ c.den) (N : ℕ) (hN : N ≤ p^2)
    (m : ℕ) (hm : 0 < m) (hn : m*p < N) :
    actualJ1Fourth c hc N hN (m*p) hn =
      -actualDKThird c hc N hN (m*p-1) (by omega) / (m : ZMod p) := by
  have hmp : m < p := by have := (Fact.out : p.Prime).pos; nlinarith
  have hmZ := (ZMod.natCast_eq_zero_iff m p).not.mpr (Nat.not_dvd_of_pos_of_lt hm hmp)
  have hJ : Cap N 4 (primitive (actualPrimeK p c)) := by
    simpa only [map_primitive] using rationalJ1_cap_four c hc N hN
  have h := primitive_layer_exceptional hJ (rationalK_euler_cap_three c hc N hN) m hm hn
  apply (eq_div_iff hmZ).mpr
  simpa only [actualJ1Fourth, actualDKThird, map_primitive, mul_comm] using h

/-- The original second primitive's carry at mp. -/
theorem actualJ2_fourth_carry (hp : 2 < p) (c : ℚ) (hc : ¬p ∣ c.den)
    (N : ℕ) (hN : N ≤ p^2) (m : ℕ) (hm : 0 < m) (hn : m*p < N) :
    actualJ2Fourth hp c hc N hN (m*p) hn =
      actualDKThird c hc N hN (m*p-2) (by omega) / ((2 : ZMod p)*m) := by
  have hmp : m < p := by nlinarith
  have hmZ := (ZMod.natCast_eq_zero_iff m p).not.mpr (Nat.not_dvd_of_pos_of_lt hm hmp)
  have h2Z : (2 : ZMod p) ≠ 0 := by
    exact_mod_cast (ZMod.natCast_eq_zero_iff 2 p).not.mpr (Nat.not_dvd_of_pos_of_lt (by omega) hp)
  have hJJ : Cap N 4 (primitive (primitive (actualPrimeK p c))) := by
    simpa only [map_primitive] using rationalJ2_cap_four hp c hc N hN
  have h := primitive_twice_layer_exceptional hJJ (rationalK_euler_cap_three c hc N hN) m hm hp hn
  apply (eq_div_iff (mul_ne_zero h2Z hmZ)).mpr
  simpa only [actualJ2Fourth, actualDKThird, map_primitive, mul_assoc, mul_comm, mul_left_comm] using h

/-- The other exceptional class of the original second primitive. -/
theorem actualJ2_fourth_carry_succ (hp : 2 < p) (c : ℚ) (hc : ¬p ∣ c.den)
    (N : ℕ) (hN : N ≤ p^2) (m : ℕ) (hm : 0 < m) (hn : m*p+1 < N) :
    actualJ2Fourth hp c hc N hN (m*p+1) hn =
      -actualDKThird c hc N hN (m*p-1) (by omega) / (m : ZMod p) := by
  have hmp : m < p := by nlinarith
  have hmZ := (ZMod.natCast_eq_zero_iff m p).not.mpr (Nat.not_dvd_of_pos_of_lt hm hmp)
  have hJ : Cap N 4 (primitive (actualPrimeK p c)) := by
    simpa only [map_primitive] using rationalJ1_cap_four c hc N hN
  have hJJ : Cap N 4 (primitive (primitive (actualPrimeK p c))) := by
    simpa only [map_primitive] using rationalJ2_cap_four hp c hc N hN
  have h := primitive_twice_layer_exceptional_succ hJ hJJ
    (rationalK_euler_cap_three c hc N hN) m hm hn
  apply (eq_div_iff hmZ).mpr
  simpa only [actualJ2Fourth, actualDKThird, map_primitive, mul_comm] using h

end Zeta7Auxiliary

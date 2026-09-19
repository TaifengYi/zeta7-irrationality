import Zeta7Proof.ActualHasseCartier
import Zeta7Proof.AuxiliaryActualGermCaps
import Zeta7Proof.AuxiliaryActualLowRows

/-! Sharp cap four for the two original ordinary primitives below p squared. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
namespace Zeta7Auxiliary
open PowerSeries Zeta7Common
variable {p : ℕ} [Fact p.Prime]

theorem not_dvd_sub_of_dvd {n k : ℕ} (hk : 0 < k) (hkp : k < p)
    (hkn : k ≤ n) (hn : p ∣ n) : ¬ p ∣ n-k := by
  intro h
  have hd := Nat.dvd_sub hn h
  have he : n-(n-k)=k := by omega
  rw [he] at hd
  exact (Nat.not_dvd_of_pos_of_lt hk hkp) hd

theorem integral_prime_div_consecutive {n : ℕ} (hn : 2 ≤ n) (hnp : n < p^2) :
    Integral ((p:ℚ_[p])/((n:ℚ_[p])*((n-1:ℕ):ℚ_[p]))) := by
  have hn0 : (n:ℚ_[p])≠0 := by exact_mod_cast (by omega : n≠0)
  have hm0 : ((n-1:ℕ):ℚ_[p])≠0 := by exact_mod_cast (by omega : n-1≠0)
  by_cases h : p ∣ n
  · have hm := not_dvd_sub_of_dvd (by omega : 0 < 1) (Fact.out : p.Prime).one_lt (by omega) h
    have hi := (integral_prime_div_nat (by omega : n≠0) hnp).mul (integral_nat_inv hm)
    convert hi using 1 <;> field_simp <;> ring
  · have hi := (integral_nat_inv h).mul
      (integral_prime_div_nat (by omega : n-1≠0) (by omega : n-1<p^2))
    convert hi using 1 <;> field_simp <;> ring

theorem integral_prime_div_three_consecutive (hp : 2 < p) {n : ℕ}
    (hn : 3 ≤ n) (hnp : n < p^2) :
    Integral ((p:ℚ_[p])/((n:ℚ_[p])*((n-1:ℕ):ℚ_[p])*((n-2:ℕ):ℚ_[p]))) := by
  have hn0 : (n:ℚ_[p])≠0 := by exact_mod_cast (by omega : n≠0)
  have hm0 : ((n-1:ℕ):ℚ_[p])≠0 := by exact_mod_cast (by omega : n-1≠0)
  have hl0 : ((n-2:ℕ):ℚ_[p])≠0 := by exact_mod_cast (by omega : n-2≠0)
  by_cases h : p ∣ n
  · have hm := not_dvd_sub_of_dvd (by omega : 0 < 1) (by omega : 1 < p) (by omega) h
    have hl := not_dvd_sub_of_dvd (by omega : 0 < 2) hp (by omega) h
    have hi := ((integral_prime_div_nat (by omega : n≠0) hnp).mul
      (integral_nat_inv hm)).mul (integral_nat_inv hl)
    convert hi using 1 <;> field_simp <;> ring
  · by_cases hm : p ∣ n-1
    · have hl : ¬p ∣ n-2 := by
        have hh := not_dvd_sub_of_dvd (by omega : 0 < 1) (by omega : 1 < p)
          (by omega : 1 ≤ n-1) hm
        simpa only [Nat.sub_sub] using hh
      have hi := ((integral_nat_inv h).mul
        (integral_prime_div_nat (by omega : n-1≠0) (by omega : n-1<p^2))).mul
        (integral_nat_inv hl)
      convert hi using 1 <;> field_simp <;> ring
    · have hi := ((integral_nat_inv h).mul (integral_nat_inv hm)).mul
        (integral_prime_div_nat (by omega : n-2≠0) (by omega : n-2<p^2))
      convert hi using 1 <;> field_simp <;> ring

theorem Cap.primitive_of_euler {N e : ℕ} {F : PowerSeries ℚ_[p]}
    (hF : Cap N e (Zeta7Common.euler F)) (h0 : constantCoeff F=0) (hN : N ≤ p^2) :
    Cap N (e+1) (primitive F) := by
  intro n hn
  by_cases hn0 : n=0
  · subst n
    simp [primitive,Integral]
  by_cases hn1 : n=1
  · subst n
    simp [primitive,h0,Integral]
  have hn2 : 2 ≤ n := by omega
  have hm0 : ((n-1:ℕ):ℚ_[p])≠0 := by exact_mod_cast (by omega : n-1≠0)
  have hnQ : (n:ℚ_[p])≠0 := by exact_mod_cast hn0
  have hi := (integral_prime_div_consecutive hn2 (hn.trans_le hN)).mul
    (hF (n-1) (by omega))
  rw [euler_coeff] at hi
  simp only [primitive,coeff_mk,if_neg hn0]
  convert hi using 1 <;> rw [pow_succ] <;> field_simp <;> ring

theorem Cap.primitive_twice_of_euler {N e : ℕ} {F : PowerSeries ℚ_[p]}
    (hF : Cap N e (Zeta7Common.euler F)) (h0 : constantCoeff F=0) (hN : N ≤ p^2) (hp : 2 < p) :
    Cap N (e+1) (primitive (primitive F)) := by
  intro n hn
  by_cases hn3 : n < 3
  · interval_cases n <;> simp [primitive,h0,Integral]
  have hn0 : n≠0 := by omega
  have hm : n-1≠0 := by omega
  have hnQ : (n:ℚ_[p])≠0 := by exact_mod_cast hn0
  have hmQ : ((n-1:ℕ):ℚ_[p])≠0 := by exact_mod_cast hm
  have hlQ : ((n-2:ℕ):ℚ_[p])≠0 := by exact_mod_cast (by omega : n-2≠0)
  have hi := (integral_prime_div_three_consecutive hp (by omega : 3 ≤ n) (hn.trans_le hN)).mul
    (hF (n-2) (by omega))
  rw [euler_coeff] at hi
  simp only [primitive,coeff_mk,if_neg hn0,if_neg hm,Nat.sub_sub]
  convert hi using 1 <;> rw [pow_succ] <;> field_simp <;> ring

theorem rationalK_euler_cap_three (c : ℚ) (hc : ¬p ∣ c.den) (N : ℕ) (hN : N ≤ p^2) :
    Cap N 3 (euler ((quadratic rationalPotential (rationalH c)).map (algebraMap ℚ ℚ_[p]))) := by
  rw [← map_euler,rationalH_quadratic_derivative,map_mul]
  simpa only [Nat.zero_add] using
    (rationalForcing_integer.cap_zero N).mul (rationalH_cap_three c hc N hN)

theorem rationalJ1_cap_four (c : ℚ) (hc : ¬p ∣ c.den) (N : ℕ) (hN : N ≤ p^2) :
    Cap N 4 ((primitive (quadratic rationalPotential (rationalH c))).map (algebraMap ℚ ℚ_[p])) := by
  rw [map_primitive]
  apply (rationalK_euler_cap_three c hc N hN).primitive_of_euler ?_ hN
  change (algebraMap ℚ ℚ_[p]) (constantCoeff (quadratic rationalPotential (rationalH c)))=0
  rw [rationalK_constant,map_zero]

theorem rationalJ2_cap_four (hp : 2 < p) (c : ℚ) (hc : ¬p ∣ c.den)
    (N : ℕ) (hN : N ≤ p^2) :
    Cap N 4 ((primitive (primitive (quadratic rationalPotential (rationalH c)))).map
      (algebraMap ℚ ℚ_[p])) := by
  rw [map_primitive,map_primitive]
  apply (rationalK_euler_cap_three c hc N hN).primitive_twice_of_euler ?_ hN hp
  change (algebraMap ℚ ℚ_[p]) (constantCoeff (quadratic rationalPotential (rationalH c)))=0
  rw [rationalK_constant,map_zero]

theorem actual_germs_cap_four (hp : 2 < p) (c : ℚ) (hc : ¬p ∣ c.den)
    (N : ℕ) (hN : N ≤ p^2) (j : Fin 6) :
    Cap N 4 ((rationalGerms c j).map (algebraMap ℚ ℚ_[p])) := by
  have hH := (rationalH_cap_three c hc N hN).mono (by omega : 3 ≤ 4)
  have hK := rationalK_cap_four c hc N hN
  have hJ1 := rationalJ1_cap_four c hc N hN
  have hJ2 := rationalJ2_cap_four hp c hc N hN
  fin_cases j
  · simpa [rationalGerms,germs] using hH
  · simpa [rationalGerms,germs,map_euler] using hH.euler
  · simpa [rationalGerms,germs,map_euler] using hH.euler.euler
  · simpa [rationalGerms,germs] using hK
  · simpa [rationalGerms,germs] using hJ1
  · simpa [rationalGerms,germs] using hJ2

def ordinaryGermCap (j : Fin 6) : ℕ := if j.val < 3 then 3 else 4

theorem actual_germs_ordinary_caps (hp : 2 < p) (c : ℚ) (hc : ¬p ∣ c.den)
    (N : ℕ) (hN : N ≤ p^2) (j : Fin 6) :
    Cap N (ordinaryGermCap j) ((rationalGerms c j).map (algebraMap ℚ ℚ_[p])) := by
  have hH := rationalH_cap_three c hc N hN
  have hK := rationalK_cap_four c hc N hN
  have hJ1 := rationalJ1_cap_four c hc N hN
  have hJ2 := rationalJ2_cap_four hp c hc N hN
  fin_cases j
  · simpa [ordinaryGermCap,rationalGerms,germs] using hH
  · simpa [ordinaryGermCap,rationalGerms,germs,map_euler] using hH.euler
  · simpa [ordinaryGermCap,rationalGerms,germs,map_euler] using hH.euler.euler
  · simpa [ordinaryGermCap,rationalGerms,germs] using hK
  · simpa [ordinaryGermCap,rationalGerms,germs] using hJ1
  · simpa [ordinaryGermCap,rationalGerms,germs] using hJ2

/-- An instantiated local bound for the unchanged canonical determinant and original basis.
This does not assert the sharper resonant compatible-basis profile. -/
theorem actualCommonDeterminant_ordinary_caps (hp : 2 < p) (d : ℕ) (c : ℚ)
    (hc : ¬p ∣ c.den) (hN : 7*d+176 ≤ p^2) :
    -padicValRat p (actualCommonDeterminant d c) ≤
      (thresholdMass (min (6*d) (7*d+176-p))
        (fun j : TailIndex d => ordinaryGermCap j.1) : ℤ) := by
  apply actualCommonDeterminant_bound_of_compatible_caps d c hc
    (1 : Matrix (TailIndex d) (TailIndex d) ℤ_[p]) (by simp)
    (fun j => ordinaryGermCap j.1)
  · intro j
    unfold ordinaryGermCap
    split_ifs <;> omega
  · intro i j
    have h1 : (1 : Matrix (TailIndex d) (TailIndex d) ℤ_[p]).map
        (algebraMap ℤ_[p] ℚ_[p])=1 := Matrix.map_one _ (map_zero _) (map_one _)
    rw [h1,Matrix.mul_one]
    have hh := ((actual_germs_ordinary_caps hp c hc (7*d+176) hN j.1).shift j.2.val)
      (actualTailRow d c i) ((actualTailRow_lt d c i).trans_le (Nat.le_add_right _ _))
    simpa only [actualPrimeMatrix,tailMatrix,actualGerms] using hh

end Zeta7Auxiliary

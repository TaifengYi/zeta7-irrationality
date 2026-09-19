import Zeta7Proof.AuxiliaryIntegralCoordinates
import Zeta7Proof.AuxiliaryLambertCaps

/-! Transport finite caps through the actual integral coordinate and Euler differentiation. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
namespace Zeta7Auxiliary
open PowerSeries Zeta7Main Zeta7Common
variable {p : ℕ} [Fact p.Prime]

theorem integral_finsum {ι : Type*} (f : ι → ℚ_[p]) (hf : ∀ i, Integral (f i)) :
    Integral (∑ᶠ i, f i) := by
  classical
  by_cases hs : (Function.support f).Finite
  · rw [finsum_eq_sum f hs]
    exact integral_sum _ _ (fun i _ => hf i)
  · rw [finsum_of_infinite_support hs]
    exact integral_zero

theorem Cap.C {N e : ℕ} {a : ℚ_[p]} (ha : Integral ((p : ℚ_[p]) ^ e * a)) :
    Cap N e (C a) := by
  intro n _
  rw [coeff_C]
  split_ifs
  · exact ha
  · simpa using (integral_zero (p := p))

theorem Cap.mul {N e f : ℕ} {F G : PowerSeries ℚ_[p]}
    (hF : Cap N e F) (hG : Cap N f G) : Cap N (e + f) (F * G) := by
  intro n hn
  rw [coeff_mul, Finset.mul_sum]
  apply integral_sum
  intro ij hij
  have he : ij.1 + ij.2 = n := by simpa using hij
  have hh := (hF ij.1 (by omega)).mul (hG ij.2 (by omega))
  convert hh using 1 <;> rw [pow_add] <;> ring

theorem IntegerSeries.cap_zero {f : PowerSeries ℚ} (hf : IntegerSeries f) (N : ℕ) :
    Cap N 0 (f.map (algebraMap ℚ ℚ_[p])) := by
  intro n _
  rw [pow_zero, one_mul, coeff_map]
  exact hf.integral_coeff n

theorem Cap.subst_integer {N e : ℕ} {F : PowerSeries ℚ_[p]}
    (hF : Cap N e F) {g : PowerSeries ℚ} (hg : IntegerSeries g)
    (hg0 : constantCoeff g = 0) : Cap N e (F.subst (g.map (algebraMap ℚ ℚ_[p]))) := by
  intro n hn
  have hg0' : constantCoeff (g.map (algebraMap ℚ ℚ_[p])) = 0 := by
    change (algebraMap ℚ ℚ_[p]) (constantCoeff g) = 0
    rw [hg0, map_zero]
  rw [coeff_subst' (HasSubst.of_constantCoeff_zero hg0')]
  simp only [smul_eq_mul]
  rw [mul_finsum]
  apply integral_finsum
  intro k
  by_cases hk : k ≤ n
  · have hgk : Integral (coeff n ((g.map (algebraMap ℚ ℚ_[p])) ^ k)) := by
      rw [← map_pow, coeff_map]
      exact (hg.pow k).integral_coeff n
    simpa only [mul_assoc] using (hF k (hk.trans_lt hn)).mul hgk
  · obtain ⟨v, hv⟩ := X_dvd_iff.mpr hg0'
    rw [hv, mul_pow, coeff_X_pow_mul', if_neg (by omega), mul_zero, mul_zero]
    exact integral_zero

theorem Cap.euler {N e : ℕ} {F : PowerSeries ℚ_[p]} (hF : Cap N e F) :
    Cap N e (euler F) := by
  intro n hn
  rw [euler_coeff, mul_left_comm]
  exact (integral_nat n).mul (hF n hn)

theorem rationalH_cap_three (c : ℚ) (hc : ¬ p ∣ c.den) (N : ℕ) (hN : N ≤ p ^ 2) :
    Cap N 3 ((rationalH c).map (algebraMap ℚ ℚ_[p])) := by
  have hc0 : Cap N 0 (C (c : ℚ_[p])) :=
    Cap.C (by simpa only [Integral, pow_zero, one_mul] using Padic.norm_rat_le_one hc)
  have hG := (lambert_cap_three N hN).subst_integer qSeries_integer qSeries_constant
  have hh := (BSeries_integer.cap_zero N).mul (hG.add (hc0.mono (by omega : 0 ≤ 3)))
  have hsubst : PowerSeries.map (algebraMap ℚ ℚ_[p]) (GSeries.subst qSeries) =
      (GSeries.map (algebraMap ℚ ℚ_[p])).subst (qSeries.map (algebraMap ℚ ℚ_[p])) :=
    map_subst (HasSubst.of_constantCoeff_zero qSeries_constant) GSeries
  have hcast : (algebraMap ℚ ℚ_[p]) c = (c : ℚ_[p]) := rfl
  simpa only [rationalH, map_mul, map_add, map_C, hsubst, hcast, Nat.zero_add] using hh

theorem rationalH_cap_zero (c : ℚ) (hc : ¬ p ∣ c.den) :
    Cap p 0 ((rationalH c).map (algebraMap ℚ ℚ_[p])) := by
  have hc0 : Cap p 0 (C (c : ℚ_[p])) :=
    Cap.C (by simpa only [Integral, pow_zero, one_mul] using Padic.norm_rat_le_one hc)
  have hG := (lambert_cap_zero (p := p)).subst_integer qSeries_integer qSeries_constant
  have hh := (BSeries_integer.cap_zero p).mul (hG.add hc0)
  have hsubst : PowerSeries.map (algebraMap ℚ ℚ_[p]) (GSeries.subst qSeries) =
      (GSeries.map (algebraMap ℚ ℚ_[p])).subst (qSeries.map (algebraMap ℚ ℚ_[p])) :=
    map_subst (HasSubst.of_constantCoeff_zero qSeries_constant) GSeries
  have hcast : (algebraMap ℚ ℚ_[p]) c = (c : ℚ_[p]) := rfl
  simpa only [rationalH, map_mul, map_add, map_C, hsubst, hcast, Nat.zero_add] using hh

theorem actual_first_three_caps (c : ℚ) (hc : ¬ p ∣ c.den) (N : ℕ) (hN : N ≤ p ^ 2)
    (j : Fin 3) : Cap N 3 ((rationalGerms c j.castSucc.castSucc.castSucc).map
      (algebraMap ℚ ℚ_[p])) := by
  have hh := rationalH_cap_three c hc N hN
  fin_cases j
  · simpa [rationalGerms, germs, map_euler] using hh
  · simpa [rationalGerms, germs, map_euler] using hh.euler
  · simpa [rationalGerms, germs, map_euler] using hh.euler.euler

end Zeta7Auxiliary

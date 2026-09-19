import Zeta7Proof.AuxiliaryActualGermCaps
import Zeta7Proof.AuxiliaryActualRows
import Zeta7Proof.AuxiliaryDeterminantBound
import Zeta7Proof.AuxiliaryDerivativeExpansion

/-! P8, milestone 3: the common denominator of the actual determinant entries, at every prime.

For every prime `p`, with `E = ⌊log_p N⌋` and `e_c = ⌊log_p c.den⌋`, every actual germ has
coefficients below `N` with `p^(8E + 2 e_c + 1)`-integral values. This is the local form of the
common denominator `2 b_c² lcm(1, …, N)^8` with `b_c = c.den`, derived from the divisor sums
(`3E`), the constant (`e_c`), the integral substitution and product `B`, the quadratic `K`
(doubling, and the factor `1/2`), and the two primitive integrations (`E` each). Consequently
`-v_p(D_d) ≤ 6d (8E + 2e_c + 1)` for the unchanged determinant and every prime `p`. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
namespace Zeta7Auxiliary
open PowerSeries Zeta7Main Zeta7Common
variable {p : ℕ} [Fact p.Prime]

/-- `p^⌊log_p N⌋ / a` is integral for `1 ≤ a ≤ N`. -/
theorem integral_pow_log_div {a N : ℕ} (ha : a ≠ 0) (haN : a ≤ N) :
    Integral ((p : ℚ_[p]) ^ Nat.log p N / (a : ℚ_[p])) := by
  have hp := (Fact.out : p.Prime)
  obtain ⟨v, b, hb, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd ha p hp.ne_one
  have hb0 : b ≠ 0 := by rintro rfl; simp at hb
  have hv : v ≤ Nat.log p N := by
    apply Nat.le_log_of_pow_le hp.one_lt
    exact le_trans (Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hb0)) haN
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hbQ : (b : ℚ_[p]) ≠ 0 := by exact_mod_cast hb0
  have he : (p : ℚ_[p]) ^ Nat.log p N / ((p ^ v * b : ℕ) : ℚ_[p]) =
      (p : ℚ_[p]) ^ (Nat.log p N - v) * (b : ℚ_[p])⁻¹ := by
    have hsplit : (p : ℚ_[p]) ^ Nat.log p N = (p : ℚ_[p]) ^ (Nat.log p N - v) * (p : ℚ_[p]) ^ v := by
      rw [← pow_add, Nat.sub_add_cancel hv]
    rw [hsplit]
    push_cast
    field_simp
  rw [he]
  exact ((integral_nat p).pow _).mul (integral_nat_inv hb)

/-- The exponent `E = ⌊log_p N⌋`. -/
abbrev logE (p N : ℕ) : ℕ := Nat.log p N

theorem lambert_cap_general (N : ℕ) :
    Cap N (3 * logE p N) (GSeries.map (algebraMap ℚ ℚ_[p])) := by
  intro n hn
  rw [coeff_map, GSeries_coeff]
  simp only [map_sum, map_inv₀, map_pow, map_natCast, Finset.mul_sum]
  apply integral_sum
  intro a ha
  have hd := Nat.mem_divisors.mp (Finset.mem_filter.mp ha).1
  have ha0 := ne_zero_of_dvd_ne_zero hd.2 hd.1
  have han := Nat.le_of_dvd (Nat.pos_of_ne_zero hd.2) hd.1
  have hh := (integral_pow_log_div (p := p) ha0 (han.trans hn.le)).pow 3
  convert hh using 1
  rw [div_pow, ← pow_mul, mul_comm (Nat.log p N) 3, div_eq_mul_inv]

theorem const_cap_general (c : ℚ) (N : ℕ) :
    Cap N (logE p c.den) (C (c : ℚ_[p])) := by
  apply Cap.C
  have h := (integral_pow_log_div (p := p) (a := c.den) c.den_nz le_rfl)
  have hn : Integral ((c.num : ℚ_[p])) := by
    simpa [Integral] using Padic.norm_int_le_one (p := p) c.num
  have hc : ((c : ℚ) : ℚ_[p]) = (c.num : ℚ_[p]) / (c.den : ℚ_[p]) := by
    conv_lhs => rw [← Rat.num_div_den c]
    push_cast; rfl
  rw [hc]
  convert hn.mul h using 1
  ring

/-- The cap exponent of `H, DH, D²H` at a general prime. -/
abbrev capH (p N : ℕ) (c : ℚ) : ℕ := 3 * logE p N + logE p c.den

theorem rationalH_cap_general (c : ℚ) (N : ℕ) :
    Cap N (capH p N c) ((rationalH c).map (algebraMap ℚ ℚ_[p])) := by
  have hc0 := (const_cap_general (p := p) c N).mono (by simp only [capH]; omega : logE p c.den ≤ capH p N c)
  have hG := ((lambert_cap_general (p := p) N).subst_integer qSeries_integer
    qSeries_constant).mono (by simp only [capH]; omega : 3 * logE p N ≤ capH p N c)
  have hh := (BSeries_integer.cap_zero N).mul (hG.add hc0)
  have hsubst : PowerSeries.map (algebraMap ℚ ℚ_[p]) (GSeries.subst qSeries) =
      (GSeries.map (algebraMap ℚ ℚ_[p])).subst (qSeries.map (algebraMap ℚ ℚ_[p])) :=
    map_subst (HasSubst.of_constantCoeff_zero qSeries_constant) GSeries
  have hcast : (algebraMap ℚ ℚ_[p]) c = (c : ℚ_[p]) := rfl
  simpa only [rationalH, map_mul, map_add, map_C, hsubst, hcast, Nat.zero_add] using hh

theorem half_cap_one (N : ℕ) : Cap N 1 (C (1 / 2 : ℚ_[p])) := by
  apply Cap.C
  by_cases h2 : p = 2
  · subst h2
    simpa [Integral] using (integral_one (p := 2))
  · have hnd : ¬ p ∣ 2 := fun h => h2 ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).mp h)
    have := (integral_nat (p := p) p).mul (integral_nat_inv (p := p) hnd)
    simpa [pow_one, one_div] using this

theorem Cap.sub' {N e : ℕ} {F G : PowerSeries ℚ_[p]} (hF : Cap N e F) (hG : Cap N e G) :
    Cap N e (F - G) := by
  rw [sub_eq_add_neg]; exact hF.add hG.neg

/-- The cap exponent of `K`. -/
abbrev capK (p N : ℕ) (c : ℚ) : ℕ := 2 * capH p N c + 1

theorem rationalK_cap_general (c : ℚ) (N : ℕ) :
    Cap N (capK p N c)
      ((quadratic rationalPotential (rationalH c)).map (algebraMap ℚ ℚ_[p])) := by
  rw [map_quadratic]
  unfold quadratic
  have hH := rationalH_cap_general (p := p) c N
  have hV : Cap N 0 (rationalPotential.map (algebraMap ℚ ℚ_[p])) :=
    rationalPotential_integer.cap_zero N
  have h2 := half_cap_one (p := p) N
  have hc : (C (1 / 2 : ℚ)).map (algebraMap ℚ ℚ_[p]) = C (1 / 2 : ℚ_[p]) := by
    rw [map_C]; congr 1; simp
  have t1 : Cap N (capK p N c) ((rationalH c).map (algebraMap ℚ ℚ_[p]) *
      euler (euler ((rationalH c).map (algebraMap ℚ ℚ_[p])))) :=
    (hH.mul hH.euler.euler).mono (by simp only [capK, capH]; omega)
  have t2 : Cap N (capK p N c) (C (1 / 2 : ℚ_[p]) *
      (euler ((rationalH c).map (algebraMap ℚ ℚ_[p]))) ^ 2) := by
    rw [pow_two]
    exact (h2.mul (hH.euler.mul hH.euler)).mono (by simp only [capK, capH]; omega)
  have t3 : Cap N (capK p N c) (C (1 / 2 : ℚ_[p]) * rationalPotential.map (algebraMap ℚ ℚ_[p]) *
      ((rationalH c).map (algebraMap ℚ ℚ_[p])) ^ 2) := by
    rw [pow_two]
    exact ((h2.mul hV).mul (hH.mul hH)).mono (by simp only [capK, capH]; omega)
  simpa only [map_sub, map_mul, map_pow, hc, map_euler] using (t1.sub' t2).sub' t3

/-- The primitive costs `E = ⌊log_p N⌋` at every prime. -/
theorem Cap.primitive_general {N e : ℕ} {F : PowerSeries ℚ_[p]} (hF : Cap N e F) :
    Cap N (e + logE p N) (primitive F) := by
  intro n hn
  simp only [primitive, coeff_mk]
  split_ifs with hn0
  · simpa using (integral_zero (p := p))
  · have hi := integral_pow_log_div (p := p) hn0 hn.le
    have hh := (hF (n - 1) (by omega)).mul hi
    convert hh using 1
    rw [pow_add]; ring

/-- The common local cap exponent `8E + 2e_c + 1`. -/
abbrev capAll (p N : ℕ) (c : ℚ) : ℕ := 8 * logE p N + 2 * logE p c.den + 1

theorem actual_germs_cap_general (c : ℚ) (N : ℕ) (j : Fin 6) :
    Cap N (capAll p N c) ((rationalGerms c j).map (algebraMap ℚ ℚ_[p])) := by
  have hH := rationalH_cap_general (p := p) c N
  have hK := rationalK_cap_general (p := p) c N
  have hJ1 := hK.primitive_general
  have hJ2 := hJ1.primitive_general
  fin_cases j
  · simpa [rationalGerms, germs] using hH.mono (by simp only [capAll, capK, capH]; omega)
  · simpa [rationalGerms, germs, map_euler] using hH.euler.mono (by simp only [capAll, capK, capH]; omega)
  · simpa [rationalGerms, germs, map_euler] using hH.euler.euler.mono (by simp only [capAll, capK, capH]; omega)
  · simpa [rationalGerms, germs] using hK.mono (by simp only [capAll, capK, capH]; omega)
  · simpa [rationalGerms, germs, map_primitive] using hJ1.mono (by simp only [capAll, capK, capH]; omega)
  · simpa [rationalGerms, germs, map_primitive] using hJ2.mono (by simp only [capAll, capK, capH]; omega)

/-- A matrix whose entries are `p^e`-integral has `p^(card·e)`-integral determinant. -/
theorem integral_det_of_entry_caps {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℚ_[p]) (e : ℕ) (h : ∀ i j, Integral ((p : ℚ_[p]) ^ e * A i j)) :
    Integral ((p : ℚ_[p]) ^ (Fintype.card ι * e) * A.det) := by
  let B : Matrix ι ι ℤ_[p] := fun i j => ⟨(p : ℚ_[p]) ^ e * A i j, h i j⟩
  have hB : B.map (PadicInt.Coe.ringHom (p := p)) = ((p : ℚ_[p]) ^ e) • A := by
    ext i j; rfl
  have hdet : PadicInt.Coe.ringHom (p := p) B.det = (((p : ℚ_[p]) ^ e) • A).det := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hB]
  rw [Matrix.det_smul, ← pow_mul, mul_comm e] at hdet
  rw [← hdet]
  exact integral_coe B.det

/-- **Denominator bound at every prime**: `-v_p(D_d) ≤ 6d (8E + 2e_c + 1)`, `N = 7d + 176`. -/
theorem actualCommonDeterminant_general_bound (d : ℕ) (c : ℚ) :
    -padicValRat p (actualCommonDeterminant d c) ≤
      ((6 * d * capAll p (7 * d + 176) c : ℕ) : ℤ) := by
  have hcap : ∀ i j, Integral ((p : ℚ_[p]) ^ capAll p (7 * d + 176) c *
      actualPrimeMatrix p d c i j) := by
    intro i j
    have h := ((actual_germs_cap_general (p := p) c (7 * d + 176) j.1).shift j.2.val)
      (actualTailRow d c i) ((actualTailRow_lt d c i).trans_le (Nat.le_add_right _ _))
    simpa only [actualPrimeMatrix, tailMatrix, actualGerms] using h
  have hdet := integral_det_of_entry_caps _ _ hcap
  rw [actualPrimeMatrix_det] at hdet
  have hcard : Fintype.card (TailIndex d) = 6 * d := by simp [TailIndex]
  rw [hcard] at hdet
  have := scaled_integral_valuation (p := p) (actualCommonDeterminant_ne_zero d c) _ hdet
  simpa [mul_assoc] using this

end Zeta7Auxiliary

import Zeta7Proof.AuxiliaryDenominatorBound

/-! P8, milestone 3 (exact form): the common denominator `2 b_c² lcm(1, …, N)^8`.

The local caps of `AuxiliaryDenominatorBound` are sharpened to the exact exponent
`v_p(2 b_c² lcm(1,…,N)^8) ≥ 8⌊log_p N⌋ + 2 v_p(b_c) + v_p(2)`, where `b_c = c.den`. The
derivation is the same: divisor sums (`3E`), the constant `c` (`v_p(b_c)`), the integral
substitution and `B`, the quadratic `K` (doubling, and `1/2`, costing `v_p(2)`), and two
primitive integrations (`E` each). Since the resulting rational numbers have nonnegative
valuation at every prime, they are integers:

* `actual_germs_common_denominator`: `2 b_c² lcm(1,…,N)^8 · [x^n] g_j ∈ ℤ` for `n < N`;
* `actualCommonDeterminant_common_denominator`: with `N = 7d + 176`,
  `(2 b_c² lcm(1,…,N)^8)^{6d} · D_d ∈ ℤ` for the unchanged determinant. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
namespace Zeta7Auxiliary
open PowerSeries Zeta7Main Zeta7Common

section Local
variable {p : ℕ} [Fact p.Prime]

/-- `p^{v_p(b)} / b` is integral. -/
theorem integral_pow_padicVal_div {b : ℕ} (hb : b ≠ 0) :
    Integral ((p : ℚ_[p]) ^ padicValNat p b / (b : ℚ_[p])) := by
  have hp := (Fact.out : p.Prime)
  obtain ⟨v, b', hb', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hb p hp.ne_one
  have hb'0 : b' ≠ 0 := by rintro rfl; simp at hb'
  have hv : padicValNat p (p ^ v * b') = v := by
    rw [padicValNat.mul (pow_ne_zero _ hp.ne_zero) hb'0, padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd hb', add_zero]
  rw [hv]
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hb0 : (b' : ℚ_[p]) ≠ 0 := by exact_mod_cast hb'0
  have he : (p : ℚ_[p]) ^ v / ((p ^ v * b' : ℕ) : ℚ_[p]) = (b' : ℚ_[p])⁻¹ := by
    push_cast
    field_simp
  rw [he]
  exact integral_nat_inv hb'

theorem const_cap_sharp (c : ℚ) (N : ℕ) :
    Cap N (padicValNat p c.den) (C (c : ℚ_[p])) := by
  apply Cap.C
  have h := integral_pow_padicVal_div (p := p) c.den_nz
  have hn : Integral ((c.num : ℚ_[p])) := by
    simpa [Integral] using Padic.norm_int_le_one (p := p) c.num
  have hc : ((c : ℚ) : ℚ_[p]) = (c.num : ℚ_[p]) / (c.den : ℚ_[p]) := by
    conv_lhs => rw [← Rat.num_div_den c]
    push_cast; rfl
  rw [hc]
  convert hn.mul h using 1
  ring

theorem half_cap_sharp (N : ℕ) : Cap N (padicValNat p 2) (C (1 / 2 : ℚ_[p])) := by
  apply Cap.C
  have h := integral_pow_padicVal_div (p := p) (b := 2) two_ne_zero
  convert h using 1
  push_cast
  ring

/-- The sharp cap exponent of `H, DH, D²H`. -/
abbrev capHs (p N : ℕ) (c : ℚ) : ℕ := 3 * logE p N + padicValNat p c.den

theorem rationalH_cap_sharp (c : ℚ) (N : ℕ) :
    Cap N (capHs p N c) ((rationalH c).map (algebraMap ℚ ℚ_[p])) := by
  have hc0 := (const_cap_sharp (p := p) c N).mono
    (by simp only [capHs]; omega : padicValNat p c.den ≤ capHs p N c)
  have hG := ((lambert_cap_general (p := p) N).subst_integer qSeries_integer
    qSeries_constant).mono (by simp only [capHs]; omega : 3 * logE p N ≤ capHs p N c)
  have hh := (BSeries_integer.cap_zero N).mul (hG.add hc0)
  have hsubst : PowerSeries.map (algebraMap ℚ ℚ_[p]) (GSeries.subst qSeries) =
      (GSeries.map (algebraMap ℚ ℚ_[p])).subst (qSeries.map (algebraMap ℚ ℚ_[p])) :=
    map_subst (HasSubst.of_constantCoeff_zero qSeries_constant) GSeries
  have hcast : (algebraMap ℚ ℚ_[p]) c = (c : ℚ_[p]) := rfl
  simpa only [rationalH, map_mul, map_add, map_C, hsubst, hcast, Nat.zero_add] using hh

/-- The sharp cap exponent of `K`. -/
abbrev capKs (p N : ℕ) (c : ℚ) : ℕ := 2 * capHs p N c + padicValNat p 2

theorem rationalK_cap_sharp (c : ℚ) (N : ℕ) :
    Cap N (capKs p N c)
      ((quadratic rationalPotential (rationalH c)).map (algebraMap ℚ ℚ_[p])) := by
  rw [map_quadratic]
  unfold quadratic
  have hH := rationalH_cap_sharp (p := p) c N
  have hV : Cap N 0 (rationalPotential.map (algebraMap ℚ ℚ_[p])) :=
    rationalPotential_integer.cap_zero N
  have h2 := half_cap_sharp (p := p) N
  have hc : (C (1 / 2 : ℚ)).map (algebraMap ℚ ℚ_[p]) = C (1 / 2 : ℚ_[p]) := by
    rw [map_C]; congr 1; simp
  have t1 : Cap N (capKs p N c) ((rationalH c).map (algebraMap ℚ ℚ_[p]) *
      euler (euler ((rationalH c).map (algebraMap ℚ ℚ_[p])))) :=
    (hH.mul hH.euler.euler).mono (by simp only [capKs, capHs]; omega)
  have t2 : Cap N (capKs p N c) (C (1 / 2 : ℚ_[p]) *
      (euler ((rationalH c).map (algebraMap ℚ ℚ_[p]))) ^ 2) := by
    rw [pow_two]
    exact (h2.mul (hH.euler.mul hH.euler)).mono (by simp only [capKs, capHs]; omega)
  have t3 : Cap N (capKs p N c) (C (1 / 2 : ℚ_[p]) * rationalPotential.map (algebraMap ℚ ℚ_[p]) *
      ((rationalH c).map (algebraMap ℚ ℚ_[p])) ^ 2) := by
    rw [pow_two]
    exact ((h2.mul hV).mul (hH.mul hH)).mono (by simp only [capKs, capHs]; omega)
  simpa only [map_sub, map_mul, map_pow, hc, map_euler] using (t1.sub' t2).sub' t3

/-- The sharp common exponent `8E + 2 v_p(b_c) + v_p(2)`. -/
abbrev capSharp (p N : ℕ) (c : ℚ) : ℕ :=
  8 * logE p N + 2 * padicValNat p c.den + padicValNat p 2

theorem actual_germs_cap_sharp (c : ℚ) (N : ℕ) (j : Fin 6) :
    Cap N (capSharp p N c) ((rationalGerms c j).map (algebraMap ℚ ℚ_[p])) := by
  have hH := rationalH_cap_sharp (p := p) c N
  have hK := rationalK_cap_sharp (p := p) c N
  have hJ1 := hK.primitive_general
  have hJ2 := hJ1.primitive_general
  fin_cases j
  · simpa [rationalGerms, germs] using hH.mono (by simp only [capSharp, capHs]; omega)
  · simpa [rationalGerms, germs, map_euler] using
      hH.euler.mono (by simp only [capSharp, capHs]; omega)
  · simpa [rationalGerms, germs, map_euler] using
      hH.euler.euler.mono (by simp only [capSharp, capHs]; omega)
  · simpa [rationalGerms, germs] using hK.mono (by simp only [capSharp, capKs, capHs]; omega)
  · simpa [rationalGerms, germs, map_primitive] using
      hJ1.mono (by simp only [capSharp, capKs, capHs]; omega)
  · simpa [rationalGerms, germs, map_primitive] using
      hJ2.mono (by simp only [capSharp, capKs, capHs]; omega)

end Local

/-! ### The global common denominator -/

/-- `lcm(1, …, N)`. -/
def lcmUpTo (N : ℕ) : ℕ := (Finset.Icc 1 N).lcm id

theorem lcmUpTo_ne_zero (N : ℕ) : lcmUpTo N ≠ 0 := by
  simp [lcmUpTo, Finset.lcm_eq_zero_iff]

theorem log_le_padicVal_lcmUpTo (p N : ℕ) [Fact p.Prime] :
    Nat.log p N ≤ padicValNat p (lcmUpTo N) := by
  by_cases hN : N = 0
  · subst hN; simp
  have hp := (Fact.out : p.Prime)
  have hmem : p ^ Nat.log p N ∈ Finset.Icc 1 N :=
    Finset.mem_Icc.mpr ⟨Nat.one_le_pow _ _ hp.pos, Nat.pow_log_le_self p hN⟩
  have hpow : p ^ Nat.log p N ∣ lcmUpTo N := Finset.dvd_lcm (f := id) hmem
  exact (padicValNat_dvd_iff_le (lcmUpTo_ne_zero N)).mp hpow

/-- The common denominator `2 b_c² lcm(1, …, N)^8`. -/
def commonDenom (c : ℚ) (N : ℕ) : ℕ := 2 * c.den ^ 2 * lcmUpTo N ^ 8

theorem commonDenom_ne_zero (c : ℚ) (N : ℕ) : commonDenom c N ≠ 0 := by
  unfold commonDenom
  have := lcmUpTo_ne_zero N
  have := c.den_nz
  positivity

theorem padicVal_commonDenom (p : ℕ) [Fact p.Prime] (c : ℚ) (N : ℕ) :
    capSharp p N c ≤ padicValNat p (commonDenom c N) := by
  have hL := lcmUpTo_ne_zero N
  have hd := c.den_nz
  unfold commonDenom
  rw [padicValNat.mul (by positivity) (pow_ne_zero _ hL),
    padicValNat.mul two_ne_zero (pow_ne_zero _ hd), padicValNat.pow c.den 2,
    padicValNat.pow (lcmUpTo N) 8]
  have := log_le_padicVal_lcmUpTo p N
  simp only [capSharp, logE]
  omega

/-- A rational number with nonnegative valuation at every prime is an integer. -/
theorem den_eq_one_of_padicVal_nonneg (q : ℚ) (h : ∀ p : ℕ, p.Prime → 0 ≤ padicValRat p q) :
    q.den = 1 := by
  by_contra hd
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hd
  have := Fact.mk hp
  have hnum : ¬ (p : ℤ) ∣ q.num := by
    intro hn
    have h1 : p ∣ q.num.natAbs := Int.natCast_dvd.mp hn
    have h2 : p ∣ Nat.gcd q.num.natAbs q.den := Nat.dvd_gcd h1 hpd
    rw [q.reduced] at h2
    exact hp.not_dvd_one h2
  have hv := h p hp
  have h0 : padicValInt p q.num = 0 := padicValInt.eq_zero_of_not_dvd hnum
  have h1 : 1 ≤ padicValNat p q.den := one_le_padicValNat_of_dvd q.den_nz hpd
  unfold padicValRat at hv
  omega

/-- **Common denominator of the actual germs.** -/
theorem actual_germs_common_denominator (c : ℚ) (N : ℕ) (j : Fin 6) (n : ℕ) (hn : n < N) :
    ((commonDenom c N : ℚ) * coeff n (rationalGerms c j)).den = 1 := by
  apply den_eq_one_of_padicVal_nonneg
  intro p hp
  have := Fact.mk hp
  by_cases ha : coeff n (rationalGerms c j) = 0
  · simp [ha]
  have hcap := actual_germs_cap_sharp (p := p) c N j n hn
  rw [coeff_map] at hcap
  have hv := scaled_integral_valuation (p := p) ha _ hcap
  have hD : (commonDenom c N : ℚ) ≠ 0 := by exact_mod_cast commonDenom_ne_zero c N
  rw [padicValRat.mul hD ha, padicValRat.of_nat]
  have := padicVal_commonDenom p c N
  omega

theorem actual_germs_common_denominator_int (c : ℚ) (N : ℕ) (j : Fin 6) (n : ℕ)
    (hn : n < N) :
    ∃ z : ℤ, (commonDenom c N : ℚ) * coeff n (rationalGerms c j) = z :=
  ⟨_, (Rat.coe_int_num_of_den_eq_one (actual_germs_common_denominator c N j n hn)).symm⟩

/-- **Common denominator of the unchanged determinant.** -/
theorem actualCommonDeterminant_common_denominator (d : ℕ) (c : ℚ) :
    ∃ z : ℤ, (commonDenom c (7 * d + 176) : ℚ) ^ (6 * d) * actualCommonDeterminant d c = z := by
  classical
  set N := 7 * d + 176
  set M := tailMatrix d (rationalGerms c) (actualTailRow d c)
  have hD : actualCommonDeterminant d c = M.det := by
    rw [actualCommonDeterminant, commonDeterminant_eq_tail]; rfl
  have hent : ∀ i j, ((commonDenom c N : ℚ) * M i j).den = 1 := by
    intro i j
    simp only [M, tailMatrix, coeff_X_pow_mul']
    split_ifs with hm
    · exact actual_germs_common_denominator c N j.1 _
        (lt_of_le_of_lt (Nat.sub_le _ _) (actualTailRow_lt d c i))
    · simp
  let Z : Matrix (TailIndex d) (TailIndex d) ℤ := fun i j => ((commonDenom c N : ℚ) * M i j).num
  have hZ : (Int.castRingHom ℚ).mapMatrix Z = (commonDenom c N : ℚ) • M := by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Z, eq_intCast, Matrix.smul_apply,
      smul_eq_mul]
    exact Rat.coe_int_num_of_den_eq_one (hent i j)
  refine ⟨Z.det, ?_⟩
  have hdet := RingHom.map_det (Int.castRingHom ℚ) Z
  rw [hZ, Matrix.det_smul] at hdet
  have hcard : Fintype.card (TailIndex d) = 6 * d := by simp [TailIndex]
  rw [hcard] at hdet
  rw [hD, ← hdet]
  simp

end Zeta7Auxiliary

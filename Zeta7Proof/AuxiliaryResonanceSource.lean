import Zeta7Proof.AuxiliaryResonanceConcomitant

/-! P5: the actual resonance source vectors `C⁺ = P (Z_{h⁺} - S(v⁺, H))`,
`C⁻ = x^p P (Z_{h⁻} - S(v⁻, H))` and the primitive shifts of `Z_{h⁺}`, as integral polynomial
source vectors of the unchanged determinant, with degrees, caps and primitive reductions. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
namespace Zeta7Auxiliary
open PowerSeries Zeta7Main Zeta7Common

variable {p : ℕ} [Fact p.Prime]

/-! ### Polynomial source vectors -/

/-- The source vector with germ polynomials `Q`. -/
def polySrc (d : ℕ) (Q : Fin 6 → Polynomial ℤ_[p]) : TailIndex d → ℤ_[p] :=
  fun j => (Q j.1).coeff j.2

theorem sourcePoly_polySrc {d : ℕ} (Q : Fin 6 → Polynomial ℤ_[p]) (k : Fin 6)
    (hk : (Q k).degree < d) :
    sourcePoly (polySrc d Q) k = ((Q k : Polynomial ℤ_[p]) : PowerSeries ℤ_[p]) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have h0 : Q k = 0 := by
      rw [Nat.cast_zero] at hk
      by_contra hne
      exact absurd hk (not_lt.mpr (Polynomial.zero_le_degree_iff.mpr hne))
    rw [h0]
    simp [sourcePoly]
  have hdeg : (Q k).natDegree < d := by
    rcases eq_or_ne (Q k) 0 with h | h
    · rw [h, Polynomial.natDegree_zero]; exact hd
    · exact (Polynomial.natDegree_lt_iff_degree_lt h).mpr hk
  unfold sourcePoly polySrc
  conv_rhs => rw [Polynomial.as_sum_range' (Q k) d hdeg]
  rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_sum, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_monomial,
    PowerSeries.monomial_eq_C_mul_X_pow]

/-- **Columns from polynomials**: the actual source series of a polynomial source vector. -/
theorem actualSourceSeries_polySrc (d : ℕ) (c : ℚ) (Q : Fin 6 → Polynomial ℤ_[p])
    (hQ : ∀ k, (Q k).degree < d) :
    actualSourceSeries p d c (polySrc d Q) = ∑ k : Fin 6, zpPoly p (Q k) * actualGerms p c k := by
  rw [actualSourceSeries_eq_polys]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [sourcePoly_polySrc Q k (hQ k)]
  rfl

/-! ### The resonance germ polynomials -/

/-- The twisted Euler operator on integral polynomials. -/
def thetaPoly (s : ℕ) (f : Polynomial ℤ_[p]) : Polynomial ℤ_[p] :=
  Polynomial.X * Polynomial.derivative f - Polynomial.C (s : ℤ_[p]) * f

theorem zpPoly_thetaPoly (s : ℕ) (f : Polynomial ℤ_[p]) :
    zpPoly p (thetaPoly s f) = thetaS (s : ℚ_[p]) (zpPoly p f) := by
  have he : zpPoly p (Polynomial.X * Polynomial.derivative f) = euler (zpPoly p f) := by
    have := zpPoly_eulerPoly (p := p) f
    rwa [eulerPoly] at this
  rw [thetaPoly, map_sub, he, map_mul, zpPoly_C, thetaS]
  simp

/-- The six germ polynomials of `P (x^s Z_h - W_s(H, P A))`. -/
def resQ (s : ℕ) (h A : Polynomial ℤ_[p]) : Fin 6 → Polynomial ℤ_[p] :=
  ![-(intPolyP p * thetaPoly s (thetaPoly s (intPolyP p * A))) + intPolyW p * A,
    intPolyP p * thetaPoly s (intPolyP p * A),
    -(intPolyP p * (intPolyP p * A)),
    intPolyP p * Polynomial.X^s * h,
    -(intPolyP p * Polynomial.X^s * Polynomial.derivative h),
    intPolyP p * Polynomial.X^s * Polynomial.derivative (Polynomial.derivative h)]

theorem bandP_eq_zpPoly : (bandP : PowerSeries ℚ_[p]) = zpPoly p (intPolyP p) := by
  rw [zpPoly_intPolyP, bandP_padic]

theorem bandW_eq_zpPoly : (bandW : PowerSeries ℚ_[p]) = zpPoly p (intPolyW p) := by
  rw [intPolyW]
  simp [bandW, map_ofNat]

theorem actualGerms_six (c : ℚ) :
    actualGerms p c 0 = padicH p c ∧ actualGerms p c 1 = euler (padicH p c) ∧
    actualGerms p c 2 = euler (euler (padicH p c)) ∧ actualGerms p c 3 = padicK p c ∧
    actualGerms p c 4 = primitive (padicK p c) ∧
    actualGerms p c 5 = primitive (primitive (padicK p c)) := by
  simp [actualGerms, rationalGerms, germs, padicH, padicK, padicMap, map_euler, map_primitive]

/-- **The resonance column identity**: the germ polynomials `resQ` realize `P · Y`. -/
theorem resQ_series (c : ℚ) (s : ℕ) (h A : Polynomial ℤ_[p]) :
    ∑ k : Fin 6, zpPoly p (resQ s h A k) * actualGerms p c k =
      bandP * resY c s h (A : PowerSeries ℤ_[p]) := by
  obtain ⟨g0, g1, g2, g3, g4, g5⟩ := actualGerms_six (p := p) c
  have hV := padicV_band (p := p)
  rw [bandP_eq_zpPoly, bandW_eq_zpPoly] at hV
  rw [Fin.sum_univ_six, g0, g1, g2, g3, g4, g5]
  have hX : zpPoly p (Polynomial.X : Polynomial ℤ_[p]) = X := by simp
  have hA : zpMap (p := p) (A : PowerSeries ℤ_[p]) = zpPoly p A := rfl
  have q0 : resQ s h A 0 = -(intPolyP p * thetaPoly s (thetaPoly s (intPolyP p * A))) + intPolyW p * A := rfl
  have q1 : resQ s h A 1 = intPolyP p * thetaPoly s (intPolyP p * A) := rfl
  have q2 : resQ s h A 2 = -(intPolyP p * (intPolyP p * A)) := rfl
  have q3 : resQ s h A 3 = intPolyP p * Polynomial.X^s * h := rfl
  have q4 : resQ s h A 4 = -(intPolyP p * Polynomial.X^s * Polynomial.derivative h) := rfl
  have q5 : resQ s h A 5 =
      intPolyP p * Polynomial.X^s * Polynomial.derivative (Polynomial.derivative h) := rfl
  rw [q0, q1, q2, q3, q4, q5]
  simp only [map_add, map_neg, map_mul, map_pow, zpPoly_thetaPoly, resY, zPart, concomitant,
    bandP_eq_zpPoly, hX, hA]
  linear_combination (-(zpPoly p A) * padicH p c) * hV


/-! ### Polynomial numerators of the resonances -/

/-- The polynomial `a⁺` (degree `p - 2`). -/
def posAPoly (p : ℕ) [Fact p.Prime] : Polynomial ℤ_[p] := PowerSeries.trunc (p - 1) (posA p)

/-- The polynomial `ã⁻ = x^p a⁻` (degree `≤ p`). -/
def negAPoly (p : ℕ) [Fact p.Prime] : Polynomial ℤ_[p] := PowerSeries.trunc (p + 1) (negA p)

theorem posAPoly_coe : (posAPoly p : PowerSeries ℤ_[p]) = posA p := by
  have := (Fact.out : p.Prime).two_le
  ext m
  rw [Polynomial.coeff_coe, posAPoly, PowerSeries.coeff_trunc]
  split_ifs with h
  · rfl
  · rw [coeff_posA_high m (by omega)]

theorem negAPoly_coe : (negAPoly p : PowerSeries ℤ_[p]) = negA p := by
  ext m
  rw [Polynomial.coeff_coe, negAPoly, PowerSeries.coeff_trunc]
  split_ifs with h
  · rfl
  · rw [coeff_negA_high m (by omega)]

theorem posAPoly_natDegree : (posAPoly p).natDegree ≤ p - 2 := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro m hm
  rw [← Polynomial.coeff_coe, posAPoly_coe, coeff_posA_high m (by exact_mod_cast hm)]

theorem negAPoly_natDegree : (negAPoly p).natDegree ≤ p := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro m hm
  rw [← Polynomial.coeff_coe, negAPoly_coe, coeff_negA_high m (by exact_mod_cast hm)]

/-! ### Degrees of the germ polynomials -/

theorem thetaPoly_natDegree (s : ℕ) (f : Polynomial ℤ_[p]) :
    (thetaPoly s f).natDegree ≤ f.natDegree := by
  unfold thetaPoly
  refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · rcases Nat.eq_zero_or_pos f.natDegree with h0 | hpos
    · rw [Polynomial.derivative_of_natDegree_zero h0, mul_zero, Polynomial.natDegree_zero]
      exact Nat.zero_le _
    · refine (Polynomial.natDegree_mul_le).trans ?_
      have h1 := Polynomial.natDegree_X_le (R := ℤ_[p])
      have h2 := Polynomial.natDegree_derivative_le f
      omega
  · exact Polynomial.natDegree_C_mul_le _ _

theorem natDegree_mul_le_of {f g : Polynomial ℤ_[p]} {a b : ℕ} (hf : f.natDegree ≤ a)
    (hg : g.natDegree ≤ b) : (f * g).natDegree ≤ a + b :=
  Polynomial.natDegree_mul_le.trans (Nat.add_le_add hf hg)

theorem natDegree_X_pow_mul_le (s : ℕ) (f : Polynomial ℤ_[p]) {a : ℕ} (hf : f.natDegree ≤ a) :
    (Polynomial.X ^ s * f).natDegree ≤ s + a :=
  natDegree_mul_le_of (Polynomial.natDegree_X_pow_le s) hf

theorem resQ_natDegree (s : ℕ) (h A : Polynomial ℤ_[p]) (m : ℕ) (hh : h.natDegree ≤ 2)
    (hA : A.natDegree ≤ m) (k : Fin 6) : (resQ s h A k).natDegree ≤ max (m + 4) (s + 4) := by
  have hP := intPolyP_natDegree (p := p)
  have hW := intPolyW_natDegree (p := p)
  have hPA : (intPolyP p * A).natDegree ≤ 2 + m := natDegree_mul_le_of hP hA
  have hd1 := Polynomial.natDegree_derivative_le h
  have hd2 := Polynomial.natDegree_derivative_le (Polynomial.derivative h)
  have hPX : ∀ g : Polynomial ℤ_[p], g.natDegree ≤ 2 →
      (intPolyP p * Polynomial.X ^ s * g).natDegree ≤ s + 4 := fun g hg => by
    have := natDegree_mul_le_of
      (natDegree_mul_le_of hP (Polynomial.natDegree_X_pow_le (R := ℤ_[p]) s)) hg
    omega
  fin_cases k
  · show (-(intPolyP p * thetaPoly s (thetaPoly s (intPolyP p * A))) +
      intPolyW p * A).natDegree ≤ _
    refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
    · rw [Polynomial.natDegree_neg]
      have := natDegree_mul_le_of hP
        ((thetaPoly_natDegree s _).trans ((thetaPoly_natDegree s _).trans hPA))
      omega
    · have := natDegree_mul_le_of hW hA
      omega
  · show (intPolyP p * thetaPoly s (intPolyP p * A)).natDegree ≤ _
    have := natDegree_mul_le_of hP ((thetaPoly_natDegree s _).trans hPA)
    omega
  · show (-(intPolyP p * (intPolyP p * A))).natDegree ≤ _
    rw [Polynomial.natDegree_neg]
    have := natDegree_mul_le_of hP hPA
    omega
  · show (intPolyP p * Polynomial.X ^ s * h).natDegree ≤ _
    exact (hPX h hh).trans (le_max_right _ _)
  · show (-(intPolyP p * Polynomial.X ^ s * Polynomial.derivative h)).natDegree ≤ _
    rw [Polynomial.natDegree_neg]
    exact (hPX _ (by omega)).trans (le_max_right _ _)
  · show (intPolyP p * Polynomial.X ^ s *
      Polynomial.derivative (Polynomial.derivative h)).natDegree ≤ _
    exact (hPX _ (by omega)).trans (le_max_right _ _)

/-- **Degree bound for `C⁺`**: every coordinate has degree `≤ p + 2`. -/
theorem posQ_natDegree (hp : 11 ≤ p) (k : Fin 6) :
    (resQ 0 (posH p) (posAPoly p) k).natDegree ≤ p + 2 := by
  have := resQ_natDegree 0 (posH p) (posAPoly p) (p - 2) posH_natDegree posAPoly_natDegree k
  omega

/-- **Degree bound for `C⁻`**: every coordinate has degree `≤ p + 4`. -/
theorem negQ_natDegree (k : Fin 6) :
    (resQ p (negH p) (negAPoly p) k).natDegree ≤ p + 4 := by
  have := resQ_natDegree p (negH p) (negAPoly p) p negH_natDegree negAPoly_natDegree k
  omega

/-! ### Shifted source vectors -/

/-- Multiplication of all germ polynomials by `X^t`. -/
def shiftQ (t : ℕ) (Q : Fin 6 → Polynomial ℤ_[p]) : Fin 6 → Polynomial ℤ_[p] :=
  fun k => Polynomial.X ^ t * Q k

/-- The germ polynomials of `Z_h`: zero on `H, DH, D²H`. -/
def zQ (h : Polynomial ℤ_[p]) : Fin 6 → Polynomial ℤ_[p] :=
  ![0, 0, 0, h, -Polynomial.derivative h, Polynomial.derivative (Polynomial.derivative h)]

theorem shiftQ_natDegree (t : ℕ) (Q : Fin 6 → Polynomial ℤ_[p]) {a : ℕ}
    (hQ : ∀ k, (Q k).natDegree ≤ a) (k : Fin 6) : (shiftQ t Q k).natDegree ≤ t + a :=
  natDegree_X_pow_mul_le t _ (hQ k)

theorem degree_lt_of_natDegree_lt {f : Polynomial ℤ_[p]} {d : ℕ} (h : f.natDegree < d) :
    f.degree < d :=
  Polynomial.degree_le_natDegree.trans_lt (by exact_mod_cast h)

theorem zQ_natDegree (h : Polynomial ℤ_[p]) (hh : h.natDegree ≤ 2) (k : Fin 6) :
    (zQ h k).natDegree ≤ 2 := by
  have hd1 := Polynomial.natDegree_derivative_le h
  have hd2 := Polynomial.natDegree_derivative_le (Polynomial.derivative h)
  fin_cases k
  · show (0 : Polynomial ℤ_[p]).natDegree ≤ 2
    simp
  · show (0 : Polynomial ℤ_[p]).natDegree ≤ 2
    simp
  · show (0 : Polynomial ℤ_[p]).natDegree ≤ 2
    simp
  · exact hh
  · show (-Polynomial.derivative h).natDegree ≤ 2
    rw [Polynomial.natDegree_neg]; omega
  · show (Polynomial.derivative (Polynomial.derivative h)).natDegree ≤ 2
    omega

theorem sum_shiftQ (c : ℚ) (t : ℕ) (Q : Fin 6 → Polynomial ℤ_[p]) :
    ∑ k : Fin 6, zpPoly p (shiftQ t Q k) * actualGerms p c k =
      X ^ t * ∑ k : Fin 6, zpPoly p (Q k) * actualGerms p c k := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hX : zpPoly p (Polynomial.X : Polynomial ℤ_[p]) = X := by simp
  rw [shiftQ, map_mul, map_pow, hX, mul_assoc]

theorem zQ_series (c : ℚ) (h : Polynomial ℤ_[p]) :
    ∑ k : Fin 6, zpPoly p (zQ h k) * actualGerms p c k = zPart c h := by
  obtain ⟨-, -, -, g3, g4, g5⟩ := actualGerms_six (p := p) c
  rw [Fin.sum_univ_six, g3, g4, g5]
  have q0 : zQ h 0 = 0 := rfl
  have q1 : zQ h 1 = 0 := rfl
  have q2 : zQ h 2 = 0 := rfl
  have q3 : zQ h 3 = h := rfl
  have q4 : zQ h 4 = -Polynomial.derivative h := rfl
  have q5 : zQ h 5 = Polynomial.derivative (Polynomial.derivative h) := rfl
  rw [q0, q1, q2, q3, q4, q5, zPart]
  simp only [map_zero, zero_mul, zero_add, map_neg]
  ring

/-- The actual source vector of `x^t C⁺`. -/
def posSrc (d t : ℕ) : TailIndex d → ℤ_[p] :=
  polySrc d (shiftQ t (resQ 0 (posH p) (posAPoly p)))

/-- The actual source vector of `x^t C⁻`. -/
def negSrc (d t : ℕ) : TailIndex d → ℤ_[p] :=
  polySrc d (shiftQ t (resQ p (negH p) (negAPoly p)))

/-- The actual source vector of `x^t Z_{h⁺}`. -/
def zSrc (d t : ℕ) : TailIndex d → ℤ_[p] :=
  polySrc d (shiftQ t (zQ (posH p)))

theorem posSrc_series (hp : 11 ≤ p) (c : ℚ) {d t : ℕ} (ht : t + p + 2 < d) :
    actualSourceSeries p d c (posSrc (p := p) d t) =
      X ^ t * (bandP * resY c 0 (posH p) (posA p)) := by
  rw [posSrc, actualSourceSeries_polySrc, sum_shiftQ, resQ_series, posAPoly_coe]
  intro k
  apply degree_lt_of_natDegree_lt
  have := shiftQ_natDegree t _ (posQ_natDegree hp) k
  omega

theorem negSrc_series (c : ℚ) {d t : ℕ} (ht : t + p + 4 < d) :
    actualSourceSeries p d c (negSrc (p := p) d t) =
      X ^ t * (bandP * resY c p (negH p) (negA p)) := by
  rw [negSrc, actualSourceSeries_polySrc, sum_shiftQ, resQ_series, negAPoly_coe]
  intro k
  apply degree_lt_of_natDegree_lt
  have := shiftQ_natDegree t _ (negQ_natDegree (p := p)) k
  omega

theorem zSrc_series (c : ℚ) {d t : ℕ} (ht : t + 2 < d) :
    actualSourceSeries p d c (zSrc (p := p) d t) = X ^ t * zPart c (posH p) := by
  rw [zSrc, actualSourceSeries_polySrc, sum_shiftQ, zQ_series]
  intro k
  apply degree_lt_of_natDegree_lt
  have := shiftQ_natDegree t _ (zQ_natDegree (posH p) posH_natDegree) k
  omega

/-! ### Caps of the source vectors -/

theorem Cap.X_pow_mul {N e : ℕ} {F : PowerSeries ℚ_[p]} (hF : Cap N e F) (t : ℕ) :
    Cap N e (X ^ t * F) := by
  intro n hn
  rw [coeff_X_pow_mul']
  split_ifs
  · exact hF _ (by omega)
  · simpa using (integral_zero (p := p))

theorem posSrc_cap_one (hp : 11 ≤ p) (c : ℚ) (hc : ¬p ∣ c.den) {d t : ℕ} (ht : t + p + 2 < d)
    (N : ℕ) (hN : N ≤ p^2) : Cap N 1 (actualSourceSeries p d c (posSrc (p := p) d t)) := by
  rw [posSrc_series hp c ht]
  exact (posC_cap_one hp c hc N hN).X_pow_mul t

theorem negSrc_cap_one (hp : 11 ≤ p) (c : ℚ) (hc : ¬p ∣ c.den) {d t : ℕ} (ht : t + p + 4 < d)
    (N : ℕ) (hN : N ≤ p^2) : Cap N 1 (actualSourceSeries p d c (negSrc (p := p) d t)) := by
  rw [negSrc_series c ht]
  exact (negC_cap_one hp c hc N hN).X_pow_mul t

/-- The concomitant `S(v, H)` of an integral `v` has cap three. -/
theorem concomitant_cap_three (c : ℚ) (hc : ¬p ∣ c.den) (N : ℕ) (hN : N ≤ p^2)
    (g : PowerSeries ℚ_[p]) (hg : Cap N 0 g) :
    Cap N 3 (concomitant (padicV p) (0 : ℚ_[p]) (padicH p c) g) := by
  have hH : Cap N 3 (padicH p c) := rationalH_cap_three c hc N hN
  have hg1 := hg.euler
  have hg2 := hg1.euler
  unfold concomitant
  simp only [thetaS_zero_eq]
  have t1 := hH.mul hg2
  have t2 := hH.euler.mul hg1
  have t3 := hH.euler.euler.mul hg
  have t4 := ((padicV_cap (p := p) N).mul hH).mul hg
  simp only [add_zero, zero_add] at t1 t2 t3 t4
  exact ((t1.sub t2).add t3).sub t4

/-- **Cap three for `x^t Z_{h⁺}`**, from the concomitant identity. -/
theorem zSrc_cap_three (hp : 11 ≤ p) (c : ℚ) (hc : ¬p ∣ c.den) {d t : ℕ} (ht : t + 2 < d)
    (N : ℕ) (hN : N ≤ p^2) : Cap N 3 (actualSourceSeries p d c (zSrc (p := p) d t)) := by
  rw [zSrc_series c ht]
  apply Cap.X_pow_mul
  have hz : zPart c (posH p) = resY c 0 (posH p) (posA p) +
      concomitant (padicV p) (0 : ℚ_[p]) (padicH p c) (bandP * zpMap (p := p) (posA p)) := by
    rw [resY]; simp
  rw [hz]
  exact ((posY_cap_one hp c hc N hN).mono (by norm_num)).add
    (concomitant_cap_three c hc N hN _ (vTilde_cap _ N))

end Zeta7Auxiliary

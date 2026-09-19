import Zeta7Proof.AuxiliaryResonanceProportional

/-! P5: the concomitant identity for the actual germs and the cap-one proof.

With `Z_h = h K - h' J₁ + h'' J₂` (ordinary derivatives of the quadratic `h`) and the twisted
concomitant `W_s(H, ṽ) = x^s S(v, H)`, the actual germs satisfy
`θ_s (x^s Z_h - W_s(H, ṽ)) = -ṽ R + (x^s h R - L_s ṽ) H`.
For both resonances the right side is integral below `N ≤ p²`; integration costs at most one
power of `p` at every index `n ≠ s`, and the index `s` is treated separately. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
namespace Zeta7Auxiliary
open PowerSeries Zeta7Main Zeta7Common

variable {p : ℕ} [Fact p.Prime]

/-! ### The actual germs in `ℚ_[p]` -/

abbrev padicK (p : ℕ) [Fact p.Prime] (c : ℚ) : PowerSeries ℚ_[p] :=
  padicMap (p := p) (quadratic rationalPotential (rationalH c))

abbrev padicR (p : ℕ) [Fact p.Prime] : PowerSeries ℚ_[p] := padicMap (p := p) rationalForcing

theorem euler_primitive_field {k : Type*} [Field k] [CharZero k] (f : PowerSeries k) :
    euler (primitive f) = X * f := by
  ext n
  rw [euler_coeff, coeff_X_mul_gen, primitive, coeff_mk]
  split_ifs with h
  · simp [h]
  · have hn : (n : k) ≠ 0 := by exact_mod_cast h
    field_simp

theorem padicK_euler (c : ℚ) : euler (padicK p c) = padicR p * padicH p c := by
  rw [padicK, ← map_euler, rationalH_quadratic_derivative, map_mul]

theorem padicH_L (c : ℚ) :
    resOp (1/2 : ℚ_[p]) (padicV p) 0 (padicH p c) = padicR p := by
  rw [padicH, ← modularL_padic, rationalH_modularL]

theorem thetaS_X_pow_mul {R : Type*} [CommRing R] (n : ℕ) (f : PowerSeries R) :
    thetaS (n : R) (X^n * f) = X^n * euler f := by
  rw [thetaS_mul, euler_X_pow_gen, thetaS,
    show (n : PowerSeries R) = C (n : R) from (map_natCast C n).symm]
  ring

theorem zpPoly_euler (h : Polynomial ℤ_[p]) :
    euler (zpPoly p h) = X * zpPoly p (Polynomial.derivative h) := by
  rw [← zpPoly_eulerPoly, eulerPoly, map_mul]
  simp

/-- The primitive part `Z_h = h K - h' J₁ + h'' J₂`. -/
def zPart (c : ℚ) (h : Polynomial ℤ_[p]) : PowerSeries ℚ_[p] :=
  zpPoly p h * padicK p c - zpPoly p (Polynomial.derivative h) * primitive (padicK p c) +
    zpPoly p (Polynomial.derivative (Polynomial.derivative h)) *
      primitive (primitive (padicK p c))

theorem zPart_euler (c : ℚ) (h : Polynomial ℤ_[p]) (hh : h.natDegree ≤ 2) :
    euler (zPart c h) = zpPoly p h * padicR p * padicH p c := by
  have h3 : Polynomial.derivative (Polynomial.derivative (Polynomial.derivative h)) = 0 := by
    have := Polynomial.iterate_derivative_eq_zero (p := h) (x := 3) (by omega)
    simpa using this
  have hsub : ∀ a b : PowerSeries ℚ_[p], euler (a - b) = euler a - euler b := fun a b => by
    simp [euler, mul_sub]
  simp only [zPart, euler_add_gen, hsub, euler_mul_general, zpPoly_euler, h3, map_zero,
    euler_primitive_field, padicK_euler]
  ring

/-- The resonance remainder `Y = x^s Z_h - W_s(H, P a)`. -/
def resY (c : ℚ) (s : ℕ) (h : Polynomial ℤ_[p]) (a : PowerSeries ℤ_[p]) : PowerSeries ℚ_[p] :=
  X^s * zPart c h - concomitant (padicV p) (s : ℚ_[p]) (padicH p c) (bandP * zpMap (p := p) a)

/-- **Concomitant identity** for the actual germs. -/
theorem resY_theta (c : ℚ) (s : ℕ) (h : Polynomial ℤ_[p]) (hh : h.natDegree ≤ 2)
    (a : PowerSeries ℤ_[p]) :
    thetaS (s : ℚ_[p]) (resY c s h a) =
      -((bandP * zpMap (p := p) a) * padicR p) +
        (X^s * (zpPoly p h * padicR p) -
          resOp (1/2 : ℚ_[p]) (padicV p) (s : ℚ_[p]) (bandP * zpMap (p := p) a)) * padicH p c := by
  have hL := lagrange_identity (1/2 : ℚ_[p]) half_padic (padicV p) (s : ℚ_[p]) (padicH p c)
    (bandP * zpMap (p := p) a)
  rw [padicH_L] at hL
  have hs : ∀ u w : PowerSeries ℚ_[p], thetaS (s : ℚ_[p]) (u - w) = thetaS (s : ℚ_[p]) u - thetaS (s : ℚ_[p]) w :=
    fun u w => by
      simp only [thetaS, sub_eq_add_neg, euler_add_gen]
      have : euler (-w) = -euler w := by simp [euler]
      rw [this]; ring
  rw [resY, hs, thetaS_X_pow_mul, zPart_euler c h hh, ← hL]
  ring

/-! ### Integrality of the pieces -/

attribute [local irreducible] Cap hasseR hasseXi logDer

theorem bandP_padic_cap (N : ℕ) : Cap N 0 (bandP : PowerSeries ℚ_[p]) := by
  rw [bandP_padic]; exact shortP_integer.cap_zero N

theorem vTilde_cap (a : PowerSeries ℤ_[p]) (N : ℕ) :
    Cap N 0 (bandP * zpMap (p := p) a) :=
  (bandP_padic_cap N).mul (integral_series_cap a N)

theorem cap_three_scale {N : ℕ} {F : PowerSeries ℚ_[p]} (hF : Cap N 3 F) :
    Cap N 0 ((p : PowerSeries ℚ_[p])^3 * F) := by
  unfold Cap at hF ⊢
  intro n hn
  rw [_root_.pow_zero, one_mul, coeff_natCast_pow_mul]
  exact hF n hn

/-- The right side of the concomitant identity is integral below `N ≤ p²`. -/
theorem resY_rhs_cap (c : ℚ) (hc : ¬p ∣ c.den) (N : ℕ) (hN : N ≤ p^2)
    (a res : PowerSeries ℤ_[p]) :
    Cap N 0 (-((bandP * zpMap (p := p) a) * padicR p) -
      (p : PowerSeries ℚ_[p])^3 * zpMap (p := p) res * padicH p c) := by
  have h1 : Cap N 0 ((bandP * zpMap (p := p) a) * padicR p) :=
    (vTilde_cap a N).mul (rationalForcing_cap_zero N)
  have h2 : Cap N 3 (zpMap (p := p) res * padicH p c) :=
    (integral_series_cap res N).mul (rationalH_cap_three c hc N hN)
  have h3 := cap_three_scale h2
  rw [← mul_assoc] at h3
  exact h1.neg.sub h3

theorem integral_neg_iff {x : ℚ_[p]} : Integral (-x) ↔ Integral x := by
  simp [Integral]

/-- Integration at an index `n ≠ s` below `p²` costs at most one power of `p`. -/
theorem integrate_index {s n : ℕ} (hn : n < p^2) (hs : s ≤ p) (hns : n ≠ s)
    {y d : ℚ_[p]} (hy : ((n : ℚ_[p]) - s) * y = d) (hd : Integral d) :
    Integral ((p : ℚ_[p]) * y) := by
  have hpp : p < p^2 := by nlinarith [(Fact.out : p.Prime).two_le]
  rcases Nat.lt_or_gt_of_ne hns with hlt | hgt
  · have hne : (s - n : ℕ) ≠ 0 := by omega
    have hq : ((s - n : ℕ) : ℚ_[p]) ≠ 0 := by exact_mod_cast hne
    have hi := (integral_prime_div_nat (p := p) hne (by omega)).mul hd
    have hsn : (n : ℚ_[p]) - s = -((s - n : ℕ) : ℚ_[p]) := by rw [Nat.cast_sub hlt.le]; ring
    have he : (p : ℚ_[p]) * y = -((p : ℚ_[p]) / ((s - n : ℕ) : ℚ_[p]) * d) := by
      rw [← hy, hsn]
      field_simp
    rw [he, integral_neg_iff]
    exact hi
  · have hne : (n - s : ℕ) ≠ 0 := by omega
    have hq : ((n - s : ℕ) : ℚ_[p]) ≠ 0 := by exact_mod_cast hne
    have hi := (integral_prime_div_nat (p := p) hne (by omega)).mul hd
    have hsn : (n : ℚ_[p]) - s = ((n - s : ℕ) : ℚ_[p]) := by rw [Nat.cast_sub hgt.le]
    have he : (p : ℚ_[p]) * y = (p : ℚ_[p]) / ((n - s : ℕ) : ℚ_[p]) * d := by
      rw [← hy, hsn]
      field_simp
    rw [he]
    exact hi

/-! ### The positive resonance: cap one -/

theorem constantCoeff_euler_gen {R : Type*} [CommRing R] (f : PowerSeries R) :
    constantCoeff (euler f) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, euler_coeff, Nat.cast_zero, zero_mul]

theorem coeff_zero_primitive {k : Type*} [Field k] (f : PowerSeries k) :
    coeff 0 (primitive f) = 0 := by
  simp [primitive]

theorem padicK_const (c : ℚ) : coeff 0 (padicK p c) = 0 := by
  rw [padicK, coeff_map, coeff_zero_eq_constantCoeff_apply, rationalK_constant, map_zero]

theorem padicV_const : constantCoeff (padicV p) = 0 := by
  change (algebraMap ℚ ℚ_[p]) (constantCoeff rationalPotential) = 0
  simp [rationalPotential]

theorem zPart_const (c : ℚ) (h : Polynomial ℤ_[p]) : coeff 0 (zPart c h) = 0 := by
  simp only [zPart, coeff_zero_eq_constantCoeff_apply, map_add, map_sub, map_mul]
  rw [← coeff_zero_eq_constantCoeff_apply (padicK p c), padicK_const,
    ← coeff_zero_eq_constantCoeff_apply (primitive (padicK p c)), coeff_zero_primitive,
    ← coeff_zero_eq_constantCoeff_apply (primitive (primitive (padicK p c))), coeff_zero_primitive]
  ring

theorem resY_pos_const (c : ℚ) (h : Polynomial ℤ_[p]) (a : PowerSeries ℤ_[p]) :
    coeff 0 (resY c 0 h a) = 0 := by
  rw [resY, pow_zero, one_mul, map_sub, zPart_const, zero_sub, neg_eq_zero,
    coeff_zero_eq_constantCoeff_apply]
  simp only [concomitant, Nat.cast_zero, thetaS_zero_eq, map_sub, map_add, map_mul,
    constantCoeff_euler_gen, padicV_const]
  ring

/-- **Positive resonance remainder, cap one** (with zero constant term). -/
theorem posY_cap_one (hp : 11 ≤ p) (c : ℚ) (hc : ¬p ∣ c.den) (N : ℕ) (hN : N ≤ p^2) :
    Cap N 1 (resY c 0 (posH p) (posA p)) := by
  have hth := resY_theta (p := p) c 0 (posH p) posH_natDegree (posA p)
  simp only [Nat.cast_zero, pow_zero, one_mul] at hth
  rw [posA_relation hp] at hth
  have hth' : thetaS (0 : ℚ_[p]) (resY c 0 (posH p) (posA p)) =
      -((bandP * zpMap (p := p) (posA p)) * padicR p) -
        (p : PowerSeries ℚ_[p])^3 * zpMap (p := p) (posResidual p) * padicH p c := by
    rw [hth]; ring
  have hrhs := resY_rhs_cap (p := p) c hc N hN (posA p) (posResidual p)
  show Cap N 1 (resY c 0 (posH p) (posA p))
  · unfold Cap at hrhs ⊢
    intro n hn
    rw [pow_one]
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · rw [resY_pos_const, mul_zero]; exact integral_zero
    · have hc0 : ((n : ℚ_[p]) - ((0 : ℕ) : ℚ_[p])) * coeff n (resY c 0 (posH p) (posA p)) =
          coeff n (-((bandP * zpMap (p := p) (posA p)) * padicR p) -
            (p : PowerSeries ℚ_[p])^3 * zpMap (p := p) (posResidual p) * padicH p c) := by
        rw [Nat.cast_zero, ← coeff_thetaS, hth']
      refine integrate_index (s := 0) (by omega) (Nat.zero_le _) (by omega) hc0 ?_
      have := hrhs n hn
      rwa [_root_.pow_zero, one_mul] at this

/-- **Positive resonance, cap one.** -/
theorem posC_cap_one (hp : 11 ≤ p) (c : ℚ) (hc : ¬p ∣ c.den) (N : ℕ) (hN : N ≤ p^2) :
    Cap N 1 (bandP * resY c 0 (posH p) (posA p)) := by
  simpa using (bandP_padic_cap N).mul (posY_cap_one hp c hc N hN)

/-! ### The negative resonance: the special index `p` -/

theorem coeff_mul_range {R : Type*} [CommRing R] (A B : PowerSeries R) (n : ℕ) :
    coeff n (A * B) = ∑ i ∈ Finset.range (n + 1), coeff i A * coeff (n - i) B := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

/-- The exact index-`p` coefficient of the twisted concomitant. -/
theorem coeff_concomitant_p (V F g : PowerSeries ℚ_[p]) :
    coeff p (concomitant V (p : ℚ_[p]) F g) =
      ∑ i ∈ Finset.range (p + 1), 3 * (i : ℚ_[p])^2 * coeff i F * coeff (p - i) g -
        coeff p (V * F * g) := by
  unfold concomitant
  rw [map_sub, map_add, map_sub, coeff_mul_range, coeff_mul_range, coeff_mul_range,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  have hip : i ≤ p := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  simp only [coeff_thetaS, euler_coeff]
  rw [Nat.cast_sub hip]
  ring

theorem padicV_cap (N : ℕ) : Cap N 0 (padicV p) := rationalPotential_integer.cap_zero N

theorem coeff_p_VFg_integral {F g : PowerSeries ℚ_[p]} (hF : Cap p 0 F) (hg : Cap p 0 g) :
    Integral (coeff p (padicV p * F * g)) := by
  obtain ⟨V', hV'⟩ := X_dvd_iff.mpr (padicV_const (p := p))
  have hVc : Cap p 0 V' := by
    have hV := padicV_cap (p := p) (p + 1)
    unfold Cap at hV ⊢
    intro n hn
    have h := hV (n + 1) (by omega)
    rwa [hV', coeff_succ_X_mul] at h
  have hp0 := (Fact.out : p.Prime).pos
  have hprod := (hVc.mul hF).mul hg
  unfold Cap at hprod
  have h := hprod (p - 1) (by omega)
  have hidx : ∀ Y : PowerSeries ℚ_[p], coeff p (X * Y) = coeff (p - 1) Y := fun Y => by
    rw [coeff_X_mul_gen, if_neg (by omega)]
  rw [hV', mul_assoc, mul_assoc, hidx]
  simpa [mul_assoc] using h

/-- `p · W_p` is integral: the only non-integral summand `3 p² H_p ṽ₀` has cap one. -/
theorem prime_mul_concomitant_p (c : ℚ) (hc : ¬p ∣ c.den) (N : ℕ) (hN : N ≤ p^2) (hpN : p < N)
    (g : PowerSeries ℚ_[p]) (hg : ∀ n, Integral (coeff n g)) :
    Integral ((p : ℚ_[p]) * coeff p (concomitant (padicV p) (p : ℚ_[p]) (padicH p c) g)) := by
  have hHlow := rationalH_cap_zero (p := p) c hc
  have hH3 := rationalH_cap_three (p := p) c hc N hN
  have hgc : Cap p 0 g := by
    unfold Cap
    intro n _
    rw [_root_.pow_zero, one_mul]; exact hg n
  have hV := coeff_p_VFg_integral (p := p) hHlow hgc
  unfold Cap at hHlow hH3
  rw [coeff_concomitant_p, Finset.sum_range_succ, Nat.sub_self]
  have hsum : Integral (∑ i ∈ Finset.range p,
      3 * (i : ℚ_[p])^2 * coeff i (padicH p c) * coeff (p - i) g) := by
    apply integral_sum
    intro i hi
    have h1 := hHlow i (Finset.mem_range.mp hi)
    rw [_root_.pow_zero, one_mul] at h1
    have h3 : Integral ((3 : ℚ_[p]) * (i : ℚ_[p])^2) := by
      have := (integral_nat (p := p) 3).mul ((integral_nat (p := p) i).pow 2)
      simpa using this
    exact (h3.mul h1).mul (hg _)
  have htop : Integral ((3 : ℚ_[p]) * coeff 0 g * ((p : ℚ_[p])^3 * coeff p (padicH p c))) := by
    have := ((integral_nat (p := p) 3).mul (hg 0)).mul (hH3 p hpN)
    simpa using this
  have he : (p : ℚ_[p]) * (∑ i ∈ Finset.range p,
        3 * (i : ℚ_[p])^2 * coeff i (padicH p c) * coeff (p - i) g +
      3 * (p : ℚ_[p])^2 * coeff p (padicH p c) * coeff 0 g -
      coeff p (padicV p * padicH p c * g)) =
      (p : ℚ_[p]) * (∑ i ∈ Finset.range p,
        3 * (i : ℚ_[p])^2 * coeff i (padicH p c) * coeff (p - i) g) +
      (3 : ℚ_[p]) * coeff 0 g * ((p : ℚ_[p])^3 * coeff p (padicH p c)) +
      -((p : ℚ_[p]) * coeff p (padicV p * padicH p c * g)) := by ring
  rw [he]
  exact (((integral_nat p).mul hsum).add htop).add ((integral_nat p).mul hV).neg

/-- **Negative resonance remainder, cap one** (including the special index `p`). -/
theorem negY_cap_one (hp : 11 ≤ p) (c : ℚ) (hc : ¬p ∣ c.den) (N : ℕ) (hN : N ≤ p^2) :
    Cap N 1 (resY c p (negH p) (negA p)) := by
  have hth := resY_theta (p := p) c p (negH p) negH_natDegree (negA p)
  rw [negA_relation hp] at hth
  have hth' : thetaS (p : ℚ_[p]) (resY c p (negH p) (negA p)) =
      -((bandP * zpMap (p := p) (negA p)) * padicR p) -
        (p : PowerSeries ℚ_[p])^3 * zpMap (p := p) (negResidual p) * padicH p c := by
    rw [hth]; ring
  have hrhs := resY_rhs_cap (p := p) c hc N hN (negA p) (negResidual p)
  have hvi : ∀ n, Integral (coeff n (bandP * zpMap (p := p) (negA p))) := by
    intro n
    have := vTilde_cap (p := p) (negA p) (n + 1)
    unfold Cap at this
    simpa using this n (by omega)
  show Cap N 1 (resY c p (negH p) (negA p))
  · unfold Cap at hrhs ⊢
    intro n hn
    rw [pow_one]
    by_cases hnp : n = p
    · subst hnp
      have hz : coeff n (resY c n (negH n) (negA n)) =
          -coeff n (concomitant (padicV n) (n : ℚ_[n]) (padicH n c)
            (bandP * zpMap (p := n) (negA n))) := by
        rw [resY, map_sub, coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self, zPart_const, zero_sub]
      rw [hz, mul_neg, integral_neg_iff]
      exact prime_mul_concomitant_p c hc N hN hn _ hvi
    · have hc0 : ((n : ℚ_[p]) - (p : ℚ_[p])) * coeff n (resY c p (negH p) (negA p)) =
          coeff n (-((bandP * zpMap (p := p) (negA p)) * padicR p) -
            (p : PowerSeries ℚ_[p])^3 * zpMap (p := p) (negResidual p) * padicH p c) := by
        rw [← coeff_thetaS, hth']
      refine integrate_index (s := p) (by omega) le_rfl hnp hc0 ?_
      have := hrhs n hn
      rwa [_root_.pow_zero, one_mul] at this

/-- **Negative resonance, cap one.** -/
theorem negC_cap_one (hp : 11 ≤ p) (c : ℚ) (hc : ¬p ∣ c.den) (N : ℕ) (hN : N ≤ p^2) :
    Cap N 1 (bandP * resY c p (negH p) (negA p)) := by
  simpa using (bandP_padic_cap N).mul (negY_cap_one hp c hc N hN)

end Zeta7Auxiliary

import Zeta7Proof.AuxiliaryHasseLogDerivative

/-! P4: cap criteria for the actual derivative source vectors, via the exact maps
`F₀ = P₀ + r P₁ + ½(V + r²) P₂` and `F₁ = P₁ + r P₂`, and the identification of the
unchanged determinant columns with polynomial combinations of the six actual germs. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
namespace Zeta7Auxiliary
open PowerSeries Zeta7Main Zeta7Common

variable {p : ℕ} [Fact p.Prime]

theorem hp5 {p : ℕ} (hp : 11 ≤ p) : 5 ≤ p := by omega
theorem hp2 {p : ℕ} (hp : 11 ≤ p) : 2 < p := by omega

attribute [local irreducible] hasseR hasseXi logDer Cap

/-! ### Columns as polynomial combinations of the germs -/

/-- The integral polynomial attached to germ `k` by a source vector. -/
def sourcePoly {d : ℕ} (a : TailIndex d → ℤ_[p]) (k : Fin 6) : PowerSeries ℤ_[p] :=
  ∑ i : Fin d, C (a (k, i)) * X^i.val

theorem actualSourceSeries_eq_polys (d : ℕ) (c : ℚ) (a : TailIndex d → ℤ_[p]) :
    actualSourceSeries p d c a =
      ∑ k : Fin 6, zpMap (p := p) (sourcePoly a k) * actualGerms p c k := by
  unfold actualSourceSeries sourcePoly
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, map_pow, map_C, map_X, PadicInt.algebraMap_apply]
  ring

/-- A source vector supported on the three derivative germs. -/
def DerivativeSupported {d : ℕ} (a : TailIndex d → ℤ_[p]) : Prop :=
  ∀ j : TailIndex d, 3 ≤ j.1.val → a j = 0

theorem sourcePoly_eq_zero_of_support {d : ℕ} {a : TailIndex d → ℤ_[p]}
    (ha : DerivativeSupported a) (k : Fin 6) (hk : 3 ≤ k.val) : sourcePoly a k = 0 := by
  unfold sourcePoly
  exact Finset.sum_eq_zero fun i _ => by rw [ha (k, i) hk, map_zero, zero_mul]

abbrev padicH (p : ℕ) [Fact p.Prime] (c : ℚ) : PowerSeries ℚ_[p] := padicMap (p := p) (rationalH c)

/-- The actual derivative source series `P₀H + P₁DH + P₂D²H`. -/
def derivativeSource (c : ℚ) (P0 P1 P2 : PowerSeries ℤ_[p]) : PowerSeries ℚ_[p] :=
  zpMap (p := p) P0 * padicH p c + zpMap (p := p) P1 * euler (padicH p c) +
    zpMap (p := p) P2 * euler (euler (padicH p c))

theorem actualSourceSeries_derivative (d : ℕ) (c : ℚ) (a : TailIndex d → ℤ_[p])
    (ha : DerivativeSupported a) :
    actualSourceSeries p d c a =
      derivativeSource c (sourcePoly a 0) (sourcePoly a 1) (sourcePoly a 2) := by
  rw [actualSourceSeries_eq_polys, Fin.sum_univ_six,
    sourcePoly_eq_zero_of_support ha 3 (by decide),
    sourcePoly_eq_zero_of_support ha 4 (by decide),
    sourcePoly_eq_zero_of_support ha 5 (by decide)]
  simp [derivativeSource, actualGerms, rationalGerms, germs, padicH, padicMap, map_euler]

/-! ### The exact maps `F₀`, `F₁` -/

def derivativeF0 (hp : 5 ≤ p) (P0 P1 P2 : PowerSeries ℤ_[p]) : PowerSeries ℚ_[p] :=
  zpMap (p := p) P0 + hasseR p hp * zpMap (p := p) P1 +
    C (1/2 : ℚ_[p]) * (padicMap (p := p) rationalPotential + hasseR p hp ^ 2) * zpMap (p := p) P2

def derivativeF1 (hp : 5 ≤ p) (P1 P2 : PowerSeries ℤ_[p]) : PowerSeries ℚ_[p] :=
  zpMap (p := p) P1 + hasseR p hp * zpMap (p := p) P2

/-- The integral second-order coefficient `b₁ = ξ S + T₁`. -/
def derivativeB1 (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) : PowerSeries ℚ_[p] :=
  hasseXi p hp * padicMap (p := p) (singularH p) + padicMap (p := p) (singularT1 p)

/-- The integral third-order coefficient `b₂ = ½ξ²S + ξT₁ + B⁻¹T₂`. -/
def derivativeB2 (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) : PowerSeries ℚ_[p] :=
  C (1/2 : ℚ_[p]) * hasseXi p hp ^ 2 * padicMap (p := p) (singularH p) +
    hasseXi p hp * padicMap (p := p) (singularT1 p) +
    padicMap (p := p) BSeries⁻¹ * padicMap (p := p) (singularT2 p)

/-- The regular remainder of the combination. -/
def derivativeRegular (c : ℚ) (P0 P1 P2 : PowerSeries ℤ_[p]) : PowerSeries ℚ_[p] :=
  zpMap (p := p) P0 * padicMap (p := p) (regularH p c) +
    zpMap (p := p) P1 * euler (padicMap (p := p) (regularH p c)) +
    zpMap (p := p) P2 * euler (euler (padicMap (p := p) (regularH p c)))

/-- **(27)** for the actual derivative source, with the actual Hasse splitting. -/
theorem derivativeSource_expansion (hp : 11 ≤ p) (c : ℚ) (P0 P1 P2 : PowerSeries ℤ_[p]) :
    (p : PowerSeries ℚ_[p])^3 * derivativeSource c P0 P1 P2 =
      padicMap (p := p) (singularH p) * derivativeF0 (hp5 hp) P0 P1 P2 +
      (p : PowerSeries ℚ_[p]) * derivativeB1 p (hp5 hp) * derivativeF1 (hp5 hp) P1 P2 +
      (p : PowerSeries ℚ_[p])^2 * derivativeB2 p (hp5 hp) * zpMap (p := p) P2 +
      (p : PowerSeries ℚ_[p])^3 * derivativeRegular c P0 P1 P2 := by
  have h := derivative_combination_expansion (p := p) (by omega) c
    (zpMap (p := p) P0) (zpMap (p := p) P1) (zpMap (p := p) P2) (hasseR p (hp5 hp))
    (hasseXi p (hp5 hp)) (logarithmicB_split (hp5 hp))
  unfold derivativeSource derivativeF0 derivativeF1 derivativeB1 derivativeB2 derivativeRegular
  simp only at h
  linear_combination h

/-! ### Integrality of the coefficients -/

theorem padic_half_cap (hp : 2 < p) (N : ℕ) : Cap N 0 (C (1/2 : ℚ_[p])) := by
  have h := rat_C_cap_zero (p := p) (1/2) (half_den_not_dvd hp) N
  have e : (C (1/2 : ℚ)).map (algebraMap ℚ ℚ_[p]) = C (1/2 : ℚ_[p]) := padicMap_half
  rwa [e] at h

theorem padicMap_cap_zero {f : PowerSeries ℚ} (hf : IntegerSeries f) (N : ℕ) :
    Cap N 0 (padicMap (p := p) f) := hf.cap_zero N

theorem derivativeF0_cap (hp : 11 ≤ p) (P0 P1 P2 : PowerSeries ℤ_[p]) (N : ℕ) :
    Cap N 0 (derivativeF0 (hp5 hp) P0 P1 P2) := by
  have hr := hasseR_cap (p := p) (hp5 hp) N
  have hV := padicMap_cap_zero (p := p) rationalPotential_integer N
  have hh := padic_half_cap (p := p) (hp2 hp) N
  have hr2 : Cap N 0 (hasseR p (hp5 hp) ^ 2) := hr.pow_zero 2
  unfold derivativeF0
  exact ((integral_series_cap P0 N).add (hr.mul (integral_series_cap P1 N))).add
    ((hh.mul (hV.add hr2)).mul (integral_series_cap P2 N))

theorem derivativeF1_cap (hp : 11 ≤ p) (P1 P2 : PowerSeries ℤ_[p]) (N : ℕ) :
    Cap N 0 (derivativeF1 (hp5 hp) P1 P2) := by
  unfold derivativeF1
  exact (integral_series_cap P1 N).add ((hasseR_cap (p := p) (hp5 hp) N).mul (integral_series_cap P2 N))

theorem derivativeB1_cap (hp : 11 ≤ p) (N : ℕ) (hN : N ≤ p^2) :
    Cap N 0 (derivativeB1 p (hp5 hp)) := by
  unfold derivativeB1
  exact ((hasseXi_cap (p := p) (hp5 hp) N).mul (singularH_cap_zero N hN)).add
    (singularT1_cap_zero N hN)

theorem derivativeB2_cap (hp : 11 ≤ p) (N : ℕ) (hN : N ≤ p^2) :
    Cap N 0 (derivativeB2 p (hp5 hp)) := by
  have hx := hasseXi_cap (p := p) (hp5 hp) N
  have hh := padic_half_cap (p := p) (hp2 hp) N
  have hBi := padicMap_cap_zero (p := p) BSeries_inv_integer N
  unfold derivativeB2
  exact (((hh.mul (hx.pow_zero 2)).mul (singularH_cap_zero N hN)).add
    (hx.mul (singularT1_cap_zero N hN))).add (hBi.mul (singularT2_cap_zero N hN))

theorem derivativeRegular_cap (c : ℚ) (hc : ¬p ∣ c.den) (P0 P1 P2 : PowerSeries ℤ_[p])
    (N : ℕ) : Cap N 0 (derivativeRegular c P0 P1 P2) := by
  have hR := regularH_cap_zero (p := p) c hc N
  unfold derivativeRegular
  exact (((integral_series_cap P0 N).mul hR).add ((integral_series_cap P1 N).mul hR.euler)).add
    ((integral_series_cap P2 N).mul hR.euler.euler)

/-- Cancellation of a common power of `p` in a scaled identity. -/
theorem cap_of_scaled {N e j : ℕ} {F Y : PowerSeries ℚ_[p]}
    (h : (p : PowerSeries ℚ_[p])^(e+j) * F = (p : PowerSeries ℚ_[p])^j * Y)
    (hY : Cap N 0 Y) : Cap N e F := by
  unfold Cap at hY ⊢
  intro n hn
  have hc := congrArg (coeff n) h
  rw [coeff_natCast_pow_mul, coeff_natCast_pow_mul, pow_add] at hc
  have hp0 : ((p : ℚ_[p]))^j ≠ 0 := pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  have he : (p : ℚ_[p])^e * coeff n F = coeff n Y := by
    apply mul_left_cancel₀ hp0
    linear_combination hc
  rw [he]
  simpa only [_root_.pow_zero, one_mul] using hY n hn

theorem natCast_pow_cap {N : ℕ} (k : ℕ) {F : PowerSeries ℚ_[p]} (hF : Cap N 0 F) :
    Cap N 0 ((p : PowerSeries ℚ_[p])^k * F) :=
  ((padic_natCast_cap p N).pow_zero k).mul hF

/-- Every actual derivative source vector has cap three below `p²`. -/
theorem derivativeSource_cap_three (hp : 11 ≤ p) (c : ℚ) (hc : ¬p ∣ c.den)
    (P0 P1 P2 : PowerSeries ℤ_[p]) (N : ℕ) (hN : N ≤ p^2) :
    Cap N 3 (derivativeSource c P0 P1 P2) := by
  apply cap_of_scaled (j := 0)
    (Y := padicMap (p := p) (singularH p) * derivativeF0 (hp5 hp) P0 P1 P2 +
      (p : PowerSeries ℚ_[p]) * derivativeB1 p (hp5 hp) * derivativeF1 (hp5 hp) P1 P2 +
      (p : PowerSeries ℚ_[p])^2 * derivativeB2 p (hp5 hp) * zpMap (p := p) P2 +
      (p : PowerSeries ℚ_[p])^3 * derivativeRegular c P0 P1 P2)
  · rw [Nat.add_zero, _root_.pow_zero, one_mul]
    exact derivativeSource_expansion hp c P0 P1 P2
  exact ((((singularH_cap_zero N hN).mul (derivativeF0_cap hp P0 P1 P2 N)).add
    (((padic_natCast_cap p N).mul (derivativeB1_cap hp N hN)).mul
      (derivativeF1_cap hp P1 P2 N))).add
    ((natCast_pow_cap 2 (derivativeB2_cap hp N hN)).mul (integral_series_cap P2 N))).add
    (natCast_pow_cap 3 (derivativeRegular_cap c hc P0 P1 P2 N))

/-- **P4 cap two.** If the exact map `F₀` vanishes, the actual column has cap two. -/
theorem derivativeSource_cap_two (hp : 11 ≤ p) (c : ℚ) (hc : ¬p ∣ c.den)
    (P0 P1 P2 : PowerSeries ℤ_[p]) (hF0 : derivativeF0 (hp5 hp) P0 P1 P2 = 0)
    (N : ℕ) (hN : N ≤ p^2) :
    Cap N 2 (derivativeSource c P0 P1 P2) := by
  apply cap_of_scaled (j := 1)
    (Y := derivativeB1 p (hp5 hp) * derivativeF1 (hp5 hp) P1 P2 +
      (p : PowerSeries ℚ_[p]) * derivativeB2 p (hp5 hp) * zpMap (p := p) P2 +
      (p : PowerSeries ℚ_[p])^2 * derivativeRegular c P0 P1 P2)
  · rw [derivativeSource_expansion hp c P0 P1 P2, hF0]
    ring
  · exact (((derivativeB1_cap hp N hN).mul (derivativeF1_cap hp P1 P2 N)).add
      (((padic_natCast_cap p N).mul (derivativeB2_cap hp N hN)).mul
        (integral_series_cap P2 N))).add
      (natCast_pow_cap 2 (derivativeRegular_cap c hc P0 P1 P2 N))

/-- **P4 cap one.** If `F₀ = 0` exactly and `F₁` is `p` times an integral series,
the actual column has cap one. -/
theorem derivativeSource_cap_one (hp : 11 ≤ p) (c : ℚ) (hc : ¬p ∣ c.den)
    (P0 P1 P2 : PowerSeries ℤ_[p]) (hF0 : derivativeF0 (hp5 hp) P0 P1 P2 = 0)
    (G : PowerSeries ℚ_[p]) (hF1 : derivativeF1 (hp5 hp) P1 P2 = (p : PowerSeries ℚ_[p]) * G)
    (N : ℕ) (hN : N ≤ p^2) (hG : Cap N 0 G) :
    Cap N 1 (derivativeSource c P0 P1 P2) := by
  apply cap_of_scaled (j := 2)
    (Y := derivativeB1 p (hp5 hp) * G + derivativeB2 p (hp5 hp) * zpMap (p := p) P2 +
      (p : PowerSeries ℚ_[p]) * derivativeRegular c P0 P1 P2)
  · rw [derivativeSource_expansion hp c P0 P1 P2, hF0, hF1]
    ring
  · exact (((derivativeB1_cap hp N hN).mul hG).add
      ((derivativeB2_cap hp N hN).mul (integral_series_cap P2 N))).add
      ((padic_natCast_cap p N).mul (derivativeRegular_cap c hc P0 P1 P2 N))

end Zeta7Auxiliary

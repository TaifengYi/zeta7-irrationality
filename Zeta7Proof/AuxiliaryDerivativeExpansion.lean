import Zeta7Proof.AuxiliaryP3Complete

/-! P4, first part: the exact expansion (27) of `p³H, p³DH, p³D²H` for the actual germs.
In characteristic zero the Euler derivatives of the singular part are computed exactly;
the p-adic logarithmic derivative `r` of the Hasse quotient and the integral correction
`ξ = (u - r)/p` come from the proved cleared Eisenstein congruence. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
namespace Zeta7Auxiliary
open PowerSeries Zeta7Main Zeta7Common

variable {p : ℕ} [Fact p.Prime]

/-! ### Exact derivatives of the singular part -/

/-- `T₁ = (θG)(q^p)`. -/
def singularT1 (p : ℕ) [Fact p.Prime] : PowerSeries ℚ :=
  (expand p (Fact.out : p.Prime).ne_zero (euler GSeries)).subst qSeries

/-- `T₂ = (θ²G)(q^p)`. -/
def singularT2 (p : ℕ) [Fact p.Prime] : PowerSeries ℚ :=
  (expand p (Fact.out : p.Prime).ne_zero (euler (euler GSeries))).subst qSeries

theorem qSubst_natCast_mul (n : ℕ) (f : PowerSeries ℚ) :
    ((n : PowerSeries ℚ) * f).subst qSeries = (n : PowerSeries ℚ) * f.subst qSeries := by
  have h := map_mul qTransport (n : PowerSeries ℚ) f
  rw [map_natCast, qTransport_apply, qTransport_apply] at h
  exact h

theorem euler_singularH :
    euler (singularH p) = logarithmicB * singularH p + (p : PowerSeries ℚ) * singularT1 p := by
  have h := thetaX_subst_q (expand p (Fact.out : p.Prime).ne_zero GSeries)
  rw [euler_expand_prime, qSubst_natCast_mul] at h
  unfold thetaX at h
  unfold singularH singularT1
  rw [euler_mul, euler_B, h]
  ring

theorem B_euler_singularT1 :
    BSeries * euler (singularT1 p) = (p : PowerSeries ℚ) * singularT2 p := by
  have h := thetaX_subst_q (expand p (Fact.out : p.Prime).ne_zero (euler GSeries))
  rw [euler_expand_prime, qSubst_natCast_mul] at h
  exact h

theorem euler_singularT1 :
    euler (singularT1 p) = BSeries⁻¹ * ((p : PowerSeries ℚ) * singularT2 p) := by
  rw [← B_euler_singularT1]
  calc
    euler (singularT1 p) = (BSeries⁻¹ * BSeries) * euler (singularT1 p) := by
      rw [mul_comm BSeries⁻¹, BSeries_mul_inv, one_mul]
    _ = _ := by ring

theorem logarithmicB_riccati :
    2 * euler logarithmicB + logarithmicB^2 = rationalPotential :=
  coordinatePotential_eq_rationalPotential

theorem euler_euler_singularH :
    euler (euler (singularH p)) =
      C (1/2 : ℚ) * (rationalPotential + logarithmicB^2) * singularH p +
        (p : PowerSeries ℚ) * logarithmicB * singularT1 p +
        (p : PowerSeries ℚ)^2 * BSeries⁻¹ * singularT2 p := by
  rw [euler_singularH, euler_add, euler_mul, euler_mul, euler_singularH, euler_singularT1,
    euler_natCast]
  linear_combination (-(C (1/2 : ℚ) * singularH p)) * logarithmicB_riccati.symm -
    (euler logarithmicB * singularH p + logarithmicB^2 * singularH p) * half_twice

/-! ### Integrality of the pieces -/

theorem logarithmicB_integer : IntegerSeries logarithmicB := by
  have hB := BSeries_integer
  have hD : IntegerSeries (euler BSeries) := IntegerSeries.X.mul hB.derivative
  exact hD.mul (hB.inv BSeries_constant)

theorem BSeries_inv_integer : IntegerSeries BSeries⁻¹ := BSeries_integer.inv BSeries_constant

theorem rationalPotential_integer : IntegerSeries rationalPotential := by
  have hP : IntegerSeries (1 + 13 * X + 49 * X ^ 2 : PowerSeries ℚ) :=
    (IntegerSeries.one.add ((IntegerSeries.natCast 13).mul IntegerSeries.X)).add
      ((IntegerSeries.natCast 49).mul (IntegerSeries.X.pow 2))
  have hW : IntegerSeries (8 * X * (1 + 16 * X + 49 * X ^ 2) : PowerSeries ℚ) :=
    ((IntegerSeries.natCast 8).mul IntegerSeries.X).mul
      ((IntegerSeries.one.add ((IntegerSeries.natCast 16).mul IntegerSeries.X)).add
        ((IntegerSeries.natCast 49).mul (IntegerSeries.X.pow 2)))
  exact hW.mul ((hP.pow 2).inv (by simp))

theorem singularT1_cap_zero (N : ℕ) (hN : N ≤ p^2) :
    Cap N 0 ((singularT1 p).map (algebraMap ℚ ℚ_[p])) :=
  qSubst_cap_zero (expand_cap_zero lambert_euler_cap_zero N hN)

theorem singularT2_cap_zero (N : ℕ) (hN : N ≤ p^2) :
    Cap N 0 ((singularT2 p).map (algebraMap ℚ ℚ_[p])) :=
  qSubst_cap_zero (expand_cap_zero lambert_euler_euler_cap_zero N hN)

/-! ### The combination identity in `ℚ_[p]` -/

theorem euler_add_gen {K : Type*} [CommRing K] (f g : PowerSeries K) :
    euler (f + g) = euler f + euler g := by
  simp [euler, mul_add]

theorem euler_natCast_pow {K : Type*} [CommRing K] (n k : ℕ) :
    euler ((n : PowerSeries K)^k) = 0 := by
  rw [← Nat.cast_pow, euler_natCast]

abbrev padicMap : PowerSeries ℚ →+* PowerSeries ℚ_[p] := PowerSeries.map (algebraMap ℚ ℚ_[p])

theorem padic_half_twice : (C (1/2 : ℚ_[p]) : PowerSeries ℚ_[p]) * 2 = 1 := by
  rw [← map_ofNat C 2, ← map_mul]
  norm_num

theorem padicMap_half : padicMap (p := p) (C (1/2 : ℚ)) = C (1/2 : ℚ_[p]) := by
  rw [padicMap, map_C]
  congr 1
  simp

/-- The exact scaled derivative relations for `H` in `ℚ_[p]`. -/
theorem padic_derivative_relations (hp7 : p ≠ 7) (c : ℚ) :
    let H := padicMap (p := p) (rationalH c)
    let S := padicMap (p := p) (singularH p)
    let R := padicMap (p := p) (regularH p c)
    let u := padicMap (p := p) logarithmicB
    let V := padicMap (p := p) rationalPotential
    let Bi := padicMap (p := p) BSeries⁻¹
    let T1 := padicMap (p := p) (singularT1 p)
    let T2 := padicMap (p := p) (singularT2 p)
    (p : PowerSeries ℚ_[p])^3 * H = S + (p : PowerSeries ℚ_[p])^3 * R ∧
    euler S = u * S + (p : PowerSeries ℚ_[p]) * T1 ∧
    euler (euler S) = C (1/2 : ℚ_[p]) * (V + u^2) * S + (p : PowerSeries ℚ_[p]) * u * T1 +
      (p : PowerSeries ℚ_[p])^2 * Bi * T2 := by
  intro H S R u V Bi T1 T2
  refine ⟨?_, ?_, ?_⟩
  · have h := congrArg (padicMap (p := p)) (rationalH_scaled_depletion (p := p) hp7 c)
    simp only [map_mul, map_add, map_C, map_pow, map_natCast] at h
    exact h
  · have h := congrArg (padicMap (p := p)) (euler_singularH (p := p))
    simp only [map_mul, map_add, map_natCast, padicMap, map_euler] at h
    exact h
  · have h := congrArg (padicMap (p := p)) (euler_euler_singularH (p := p))
    simp only [map_mul, map_add, map_natCast, map_pow, map_euler] at h
    rw [padicMap_half] at h
    exact h

/-- **Paper (27), exact form.** For any source series and any splitting `u = r + p ξ`,
the scaled derivative combination is `S F₀ + p b₁ F₁ + p² b₂ P₂ + p³ (regular)`. -/
theorem derivative_combination_expansion (hp7 : p ≠ 7) (c : ℚ)
    (P0 P1 P2 r ξ : PowerSeries ℚ_[p])
    (hu : padicMap (p := p) logarithmicB = r + (p : PowerSeries ℚ_[p]) * ξ) :
    let H := padicMap (p := p) (rationalH c)
    let S := padicMap (p := p) (singularH p)
    let R := padicMap (p := p) (regularH p c)
    let V := padicMap (p := p) rationalPotential
    let Bi := padicMap (p := p) BSeries⁻¹
    let T1 := padicMap (p := p) (singularT1 p)
    let T2 := padicMap (p := p) (singularT2 p)
    (p : PowerSeries ℚ_[p])^3 * (P0 * H + P1 * euler H + P2 * euler (euler H)) =
      S * (P0 + r * P1 + C (1/2 : ℚ_[p]) * (V + r^2) * P2) +
      (p : PowerSeries ℚ_[p]) * (ξ * S + T1) * (P1 + r * P2) +
      (p : PowerSeries ℚ_[p])^2 * (C (1/2 : ℚ_[p]) * ξ^2 * S + ξ * T1 + Bi * T2) * P2 +
      (p : PowerSeries ℚ_[p])^3 * (P0 * R + P1 * euler R + P2 * euler (euler R)) := by
  intro H S R V Bi T1 T2
  obtain ⟨h0, h1, h2⟩ := padic_derivative_relations (p := p) hp7 c
  have hH1 : (p : PowerSeries ℚ_[p])^3 * euler H = euler S +
      (p : PowerSeries ℚ_[p])^3 * euler R := by
    have := congrArg euler h0
    rw [euler_mul_general, euler_add_gen, euler_mul_general, euler_natCast_pow] at this
    simpa only [zero_mul, zero_add] using this
  have hH2 : (p : PowerSeries ℚ_[p])^3 * euler (euler H) = euler (euler S) +
      (p : PowerSeries ℚ_[p])^3 * euler (euler R) := by
    have := congrArg euler hH1
    rw [euler_mul_general, euler_add_gen, euler_mul_general, euler_natCast_pow] at this
    simpa only [zero_mul, zero_add] using this
  change padicMap (p := p) logarithmicB = r + (p : PowerSeries ℚ_[p]) * ξ at hu
  rw [hu] at h1 h2
  linear_combination P0 * h0 + P1 * hH1 + P2 * hH2 + P1 * h1 + P2 * h2 +
    (P2 * S * (p : PowerSeries ℚ_[p]) * r * ξ) * padic_half_twice (p := p)

end Zeta7Auxiliary

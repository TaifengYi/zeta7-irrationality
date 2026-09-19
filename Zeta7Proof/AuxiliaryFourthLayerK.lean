import Zeta7Proof.AuxiliaryGammaFrobenius
import Zeta7Proof.AuxiliaryPrimitiveLayers

/-! The complete fourth layer of the actual K: `p^4 K ≡ K0(X^p)` below `N ≤ p^2`.
`K0` is an explicit short series whose coefficients below `p` are the reductions of the
original `K` at `c = 0`, and which vanishes from `p` on. The proof substitutes the exact
Lambert depletion into the proved q-coordinate formula for `K`; no layer is assumed. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
namespace Zeta7Auxiliary
open PowerSeries Zeta7Main Zeta7Common

variable {p : ℕ} [Fact p.Prime]

/-! ### The exact characteristic-zero identity -/

/-- The q-coordinate kernel of `K`: `(G + c) θ²G - ½ (θG)²`. -/
def lambertQuadratic (c : ℚ) : PowerSeries ℚ :=
  (GSeries + C c) * euler (euler GSeries) - C (1/2 : ℚ) * (euler GSeries)^2

theorem modularDefect_eq_zero : modularDefect = 0 := by
  rw [modularDefect, coordinatePotential_eq_rationalPotential, sub_self]

theorem rationalK_eq_subst (c : ℚ) :
    quadratic rationalPotential (rationalH c) = (lambertQuadratic c).subst qSeries := by
  rw [rationalH_quadratic_transport, modularDefect_eq_zero, mul_zero, zero_mul, add_zero]
  rfl

theorem euler_expand_prime {K : Type*} [CommRing K] (f : PowerSeries K) :
    euler (expand p (Fact.out : p.Prime).ne_zero f) =
      (p : PowerSeries K) * expand p (Fact.out : p.Prime).ne_zero (euler f) := by
  ext n
  rw [euler_coeff, show (p : PowerSeries K) = C (p : K) from (map_natCast C p).symm,
    coeff_C_mul, coeff_expand, coeff_expand]
  split_ifs with h
  · obtain ⟨k, rfl⟩ := h
    rw [Nat.mul_div_cancel_left _ (Fact.out : p.Prime).pos, euler_coeff]
    push_cast
    ring
  · simp

/-- The integral remainder of the fourth-layer decomposition. -/
def depletionRemainder (p : ℕ) [Fact p.Prime] (c : ℚ) : PowerSeries ℚ :=
  (p : PowerSeries ℚ)^3 * ((depletedLambert p + C c) * euler (euler (depletedLambert p)) -
      C (1/2 : ℚ) * (euler (depletedLambert p))^2) +
    (p : PowerSeries ℚ)^2 * (depletedLambert p + C c) *
      expand p (Fact.out : p.Prime).ne_zero (euler (euler GSeries)) +
    expand p (Fact.out : p.Prime).ne_zero GSeries * euler (euler (depletedLambert p)) -
    (p : PowerSeries ℚ) * euler (depletedLambert p) *
      expand p (Fact.out : p.Prime).ne_zero (euler GSeries)

/-- **Exact decomposition.** `p^4 (G+c)θ²G - ...` is the Frobenius expansion of the
`c = 0` kernel plus `p` times an explicit remainder. -/
theorem lambertQuadratic_depletion (hp7 : p ≠ 7) (c : ℚ) :
    (p : PowerSeries ℚ)^4 * lambertQuadratic c =
      expand p (Fact.out : p.Prime).ne_zero (lambertQuadratic 0) +
        (p : PowerSeries ℚ) * depletionRemainder p c := by
  have hp0 := (Fact.out : p.Prime).ne_zero
  have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast hp0
  have hG := GSeries_depletion (p := p) hp7
  have hw : C ((p : ℚ)⁻¹^3) * (p : PowerSeries ℚ)^3 = 1 := by
    rw [show (p : PowerSeries ℚ) = C (p : ℚ) from (map_natCast C p).symm, ← map_pow,
      ← map_mul, ← mul_pow, inv_mul_cancel₀ hpQ, one_pow, map_one]
  have hD1 : euler GSeries = euler (depletedLambert p) +
      C ((p : ℚ)⁻¹^3) * ((p : PowerSeries ℚ) * expand p hp0 (euler GSeries)) := by
    conv_lhs => rw [hG]
    rw [euler_add, euler_mul_general, euler_C, zero_mul, zero_add, euler_expand_prime]
  have hD2 : euler (euler GSeries) = euler (euler (depletedLambert p)) +
      C ((p : ℚ)⁻¹^3) * ((p : PowerSeries ℚ) *
        ((p : PowerSeries ℚ) * expand p hp0 (euler (euler GSeries)))) := by
    have h1 : euler (expand p hp0 (euler GSeries)) =
        (p : PowerSeries ℚ) * expand p hp0 (euler (euler GSeries)) := euler_expand_prime _
    generalize expand p hp0 (euler (euler GSeries)) = E2 at h1 ⊢
    generalize expand p hp0 (euler GSeries) = E1 at hD1 h1 ⊢
    rw [hD1, euler_add, euler_mul_general, euler_C, zero_mul, zero_add, euler_mul_general,
      euler_natCast, zero_mul, zero_add, h1]
  unfold lambertQuadratic depletionRemainder
  rw [map_zero, add_zero, map_sub, map_mul, map_mul, map_pow, expand_C]
  generalize expand p hp0 (euler (euler GSeries)) = E2 at hD2 ⊢
  generalize expand p hp0 (euler GSeries) = E1 at hD1 hD2 ⊢
  rw [hD2, hD1]
  generalize expand p hp0 GSeries = E at hG ⊢
  rw [hG]
  generalize C ((p : ℚ)⁻¹^3) = v at hw ⊢
  generalize (p : PowerSeries ℚ) = P at hw ⊢
  linear_combination
    ((v*P^3 + 1) * (E*E2 - C (1/2 : ℚ)*E1^2) + P*E*euler (euler (depletedLambert p)) +
      P^3*(depletedLambert p + C c)*E2 - P^2*euler (depletedLambert p)*E1) * hw -
    P^5*v*euler (depletedLambert p)*E1 * half_twice

/-- `p^4 K = K0-kernel(q^p) + p * remainder(q)` for the actual K, in every degree. -/
theorem rationalK_scaled_depletion (hp7 : p ≠ 7) (c : ℚ) :
    (p : PowerSeries ℚ)^4 * quadratic rationalPotential (rationalH c) =
      (expand p (Fact.out : p.Prime).ne_zero (lambertQuadratic 0)).subst qSeries +
        (p : PowerSeries ℚ) * (depletionRemainder p c).subst qSeries := by
  have h := congrArg qTransport (lambertQuadratic_depletion hp7 c)
  simp only [map_add, map_mul, map_pow, map_natCast, qTransport_apply] at h
  rw [rationalK_eq_subst]
  exact h

/-! ### Caps of the pieces -/

theorem Cap.sub {N e : ℕ} {F G : PowerSeries ℚ_[p]}
    (hF : Cap N e F) (hG : Cap N e G) : Cap N e (F - G) := by
  simpa only [sub_eq_add_neg] using hF.add hG.neg

theorem Cap.pow_zero {N : ℕ} {F : PowerSeries ℚ_[p]} (hF : Cap N 0 F) (k : ℕ) :
    Cap N 0 (F^k) := by
  induction k with
  | zero =>
    rw [_root_.pow_zero]
    exact Cap.C (by simpa only [_root_.pow_zero, one_mul] using (integral_one (p := p)))
  | succ k ih => simpa only [pow_succ] using ih.mul hF

theorem rat_C_cap_zero (a : ℚ) (ha : ¬p ∣ a.den) (N : ℕ) :
    Cap N 0 ((C a).map (algebraMap ℚ ℚ_[p])) := by
  rw [map_C]
  have hcast : (algebraMap ℚ ℚ_[p]) a = (a : ℚ_[p]) := rfl
  rw [hcast]
  exact Cap.C (by simpa only [Integral, _root_.pow_zero, one_mul] using Padic.norm_rat_le_one ha)

theorem half_den_not_dvd (hp : 2 < p) : ¬p ∣ (1/2 : ℚ).den := by
  have h : (1/2 : ℚ).den = 2 := by norm_num
  rw [h]
  intro hd
  have := Nat.le_of_dvd (by decide) hd
  omega

theorem natCast_cap_zero (n N : ℕ) : Cap N 0 ((n : PowerSeries ℚ).map (algebraMap ℚ ℚ_[p])) :=
  (IntegerSeries.natCast n).cap_zero N

theorem expand_cap_zero {T : PowerSeries ℚ} (hT : Cap p 0 (T.map (algebraMap ℚ ℚ_[p])))
    (N : ℕ) (hN : N ≤ p^2) :
    Cap N 0 ((expand p (Fact.out : p.Prime).ne_zero T).map (algebraMap ℚ ℚ_[p])) := by
  intro n hn
  rw [_root_.pow_zero, one_mul, map_expand, coeff_expand]
  split_ifs
  · simpa only [_root_.pow_zero, one_mul] using
      hT (n/p) (div_prime_lt_of_lt_sq (hn.trans_le hN))
  · exact integral_zero

theorem lambert_euler_cap_zero :
    Cap p 0 ((euler GSeries).map (algebraMap ℚ ℚ_[p])) := by
  rw [map_euler]; exact (lambert_cap_zero (p := p)).euler

theorem lambert_euler_euler_cap_zero :
    Cap p 0 ((euler (euler GSeries)).map (algebraMap ℚ ℚ_[p])) := by
  rw [map_euler, map_euler]; exact (lambert_cap_zero (p := p)).euler.euler

theorem depletionRemainder_cap_zero (hp : 2 < p) (c : ℚ) (hc : ¬p ∣ c.den)
    (N : ℕ) (hN : N ≤ p^2) :
    Cap N 0 ((depletionRemainder p c).map (algebraMap ℚ ℚ_[p])) := by
  have hD := depletedLambert_cap_zero (p := p) N
  have hD1 : Cap N 0 ((euler (depletedLambert p)).map (algebraMap ℚ ℚ_[p])) := by
    rw [map_euler]; exact hD.euler
  have hD2 : Cap N 0 ((euler (euler (depletedLambert p))).map (algebraMap ℚ ℚ_[p])) := by
    rw [map_euler, map_euler]; exact hD.euler.euler
  have hZ : Cap N 0 ((depletedLambert p + C c).map (algebraMap ℚ ℚ_[p])) := by
    rw [map_add]; exact hD.add (rat_C_cap_zero c hc N)
  have hP := natCast_cap_zero (p := p) p N
  have hh := rat_C_cap_zero (p := p) (1/2) (half_den_not_dvd hp) N
  have hE := expandedLambert_cap_zero (p := p) N hN
  have hE1 := expand_cap_zero lambert_euler_cap_zero N hN
  have hE2 := expand_cap_zero lambert_euler_euler_cap_zero N hN
  unfold depletionRemainder
  simp only [map_add, map_sub, map_mul, map_pow] at hZ hP hh hE hE1 hE2 hD1 hD2 ⊢
  exact ((((hP.pow_zero 3).mul ((hZ.mul hD2).sub (hh.mul (hD1.pow_zero 2)))).add
    (((hP.pow_zero 2).mul hZ).mul hE2)).add (hE.mul hD2)).sub ((hP.mul hD1).mul hE1)

theorem lambertQuadratic_zero_cap_zero (hp : 2 < p) :
    Cap p 0 ((lambertQuadratic 0).map (algebraMap ℚ ℚ_[p])) := by
  have hG := lambert_cap_zero (p := p)
  have hh := rat_C_cap_zero (p := p) (1/2) (half_den_not_dvd hp) p
  have h1 := lambert_euler_cap_zero (p := p)
  have h2 := lambert_euler_euler_cap_zero (p := p)
  unfold lambertQuadratic
  rw [map_zero, add_zero]
  simp only [map_sub, map_mul, map_pow] at hh h1 h2 ⊢
  exact (hG.mul h2).sub (hh.mul (h1.pow_zero 2))

theorem qSubst_cap_zero {T : PowerSeries ℚ} {N : ℕ}
    (hT : Cap N 0 (T.map (algebraMap ℚ ℚ_[p]))) :
    Cap N 0 (PowerSeries.map (algebraMap ℚ ℚ_[p]) (T.subst qSeries)) := by
  rw [map_qSeries_subst]
  exact hT.subst_integer qSeries_integer qSeries_constant

/-! ### Generic short reduction through the integral coordinate -/

theorem cap_zero_integral {T : PowerSeries ℚ} {N : ℕ}
    (hT : Cap N 0 (T.map (algebraMap ℚ ℚ_[p]))) (j : ℕ) (hj : j < N) :
    Integral ((coeff j T : ℚ) : ℚ_[p]) := by
  have h := hT j hj
  rw [_root_.pow_zero, one_mul, coeff_map] at h
  exact h

/-- Truncation below `p` of a rational series integral below `p`, lifted to `ℤ_[p]`. -/
def shortLift (T : PowerSeries ℚ) (hT : Cap p 0 (T.map (algebraMap ℚ ℚ_[p]))) :
    PowerSeries ℤ_[p] :=
  mk fun j => if h : j < p then ⟨((coeff j T : ℚ) : ℚ_[p]), cap_zero_integral hT j h⟩ else 0

theorem shortLift_coeff_lt {T : PowerSeries ℚ} (hT : Cap p 0 (T.map (algebraMap ℚ ℚ_[p])))
    (j : ℕ) (hj : j < p) :
    coeff j ((shortLift T hT).map (algebraMap ℤ_[p] ℚ_[p])) =
      coeff j (T.map (algebraMap ℚ ℚ_[p])) := by
  simp only [coeff_map, shortLift, coeff_mk, dif_pos hj, PadicInt.algebraMap_apply]
  rfl

/-- The reduced short series attached to `T(q)`: zero from `p` on. -/
def shortSubstReduction (T : PowerSeries ℚ) (hT : Cap p 0 (T.map (algebraMap ℚ ℚ_[p]))) :
    PowerSeries (ZMod p) :=
  mk fun j => if j < p then
    coeff j (PowerSeries.map PadicInt.toZMod ((shortLift T hT).subst (integralQCoordinate p))) else 0

theorem shortSubstReduction_coeff_ge {T : PowerSeries ℚ}
    (hT : Cap p 0 (T.map (algebraMap ℚ ℚ_[p]))) (j : ℕ) (hj : p ≤ j) :
    coeff j (shortSubstReduction T hT) = 0 := by
  rw [shortSubstReduction, coeff_mk, if_neg (not_lt.mpr hj)]

theorem shortSubst_coeff_eq {T : PowerSeries ℚ} (hT : Cap p 0 (T.map (algebraMap ℚ ℚ_[p])))
    (j : ℕ) (hj : j < p) :
    coeff j (PowerSeries.map (algebraMap ℚ ℚ_[p]) (T.subst qSeries)) =
      coeff j (PowerSeries.map (algebraMap ℤ_[p] ℚ_[p]) ((shortLift T hT).subst (integralQCoordinate p))) := by
  rw [map_qSeries_subst, map_integral_subst, map_integralQ]
  apply coeff_subst_congr qSeries_map_constant
  intro i hi
  exact (shortLift_coeff_lt hT i (by omega)).symm

theorem expandSubst_coeff_eq {T : PowerSeries ℚ}
    (hT : Cap p 0 (T.map (algebraMap ℚ ℚ_[p]))) (n : ℕ) (hn : n < p^2) :
    coeff n (PowerSeries.map (algebraMap ℚ ℚ_[p]) ((expand p (Fact.out : p.Prime).ne_zero T).subst qSeries)) =
      coeff n (PowerSeries.map (algebraMap ℤ_[p] ℚ_[p]) ((expand p (Fact.out : p.Prime).ne_zero (shortLift T hT)).subst (integralQCoordinate p))) := by
  rw [map_qSeries_subst, map_integral_subst, map_integralQ, map_expand, map_expand]
  apply coeff_subst_congr qSeries_map_constant
  intro i hi
  exact (coeff_expand_congr_short (fun j hj => shortLift_coeff_lt hT j hj) i (by omega)).symm

theorem reduced_expandSubst (S : PowerSeries ℤ_[p]) :
    PowerSeries.map PadicInt.toZMod ((expand p (Fact.out : p.Prime).ne_zero S).subst (integralQCoordinate p)) =
      expand p (Fact.out : p.Prime).ne_zero
        (PowerSeries.map PadicInt.toZMod (S.subst (integralQCoordinate p))) := by
  rw [map_integral_subst, map_integral_subst, map_expand,
    zmod_expand_subst _ _ reducedQCoordinate_constant]

theorem integralResidue_eq_of_lift {x : ℚ_[p]} (hx : Integral x) (a : ℤ_[p])
    (ha : (a : ℚ_[p]) = x) : integralResidue x hx = PadicInt.toZMod a := by
  unfold integralResidue
  congr 1
  exact Subtype.ext ha.symm

/-- Reduction of `T(q^p)`, coefficientwise below `p^2`, is `(short T(q))(X^p)`. -/
theorem expandSubst_residue {T : PowerSeries ℚ}
    (hT : Cap p 0 (T.map (algebraMap ℚ ℚ_[p]))) (n : ℕ) (hn : n < p^2)
    (hx : Integral (coeff n (PowerSeries.map (algebraMap ℚ ℚ_[p]) ((expand p (Fact.out : p.Prime).ne_zero T).subst qSeries)))) :
    integralResidue _ hx =
      coeff n (expand p (Fact.out : p.Prime).ne_zero (shortSubstReduction T hT)) := by
  rw [integralResidue_eq_of_lift hx
    (coeff n ((expand p (Fact.out : p.Prime).ne_zero (shortLift T hT)).subst
      (integralQCoordinate p))) (by rw [expandSubst_coeff_eq hT n hn, coeff_map]; rfl),
    ← coeff_map, reduced_expandSubst]
  refine coeff_expand_congr_short (fun j hj => ?_) n hn
  rw [shortSubstReduction, coeff_mk, if_pos hj]

/-- The coefficients of the short reduction below `p` are exactly residues of `T(q)`. -/
theorem shortSubstReduction_coeff_lt {T : PowerSeries ℚ}
    (hT : Cap p 0 (T.map (algebraMap ℚ ℚ_[p]))) (j : ℕ) (hj : j < p)
    (hx : Integral (coeff j (PowerSeries.map (algebraMap ℚ ℚ_[p]) (T.subst qSeries)))) :
    coeff j (shortSubstReduction T hT) = integralResidue _ hx := by
  rw [integralResidue_eq_of_lift hx
    (coeff j ((shortLift T hT).subst (integralQCoordinate p)))
    (by rw [shortSubst_coeff_eq hT j hj, coeff_map]; rfl),
    shortSubstReduction, coeff_mk, if_pos hj, coeff_map]

/-! ### The actual K0 and the fourth layer -/

/-- The paper's short series `K0`. -/
def hasseShortK (p : ℕ) [Fact p.Prime] (hp : 2 < p) : PowerSeries (ZMod p) :=
  shortSubstReduction (lambertQuadratic 0) (lambertQuadratic_zero_cap_zero hp)

theorem lambertQuadratic_zero_subst :
    (lambertQuadratic 0).subst qSeries = quadratic rationalPotential (rationalH 0) :=
  (rationalK_eq_subst 0).symm

/-- Exact coefficient theorem for `K0` below `p`. -/
theorem hasseShortK_coeff_lt (hp : 2 < p) (j : ℕ) (hj : j < p) :
    coeff j (hasseShortK p hp) =
      layerCoefficient (rationalK_cap_zero (p := p) 0 zero_den_not_dvd) ⟨j, hj⟩ := by
  have hK := rationalK_cap_zero (p := p) 0 zero_den_not_dvd
  have hx : Integral (coeff j (PowerSeries.map (algebraMap ℚ ℚ_[p]) ((lambertQuadratic 0).subst qSeries))) := by
    rw [lambertQuadratic_zero_subst]
    simpa only [_root_.pow_zero, one_mul] using hK j hj
  rw [hasseShortK, shortSubstReduction_coeff_lt _ j hj hx, layerCoefficient_eq_residue]
  exact integralResidue_congr _ _ (by rw [lambertQuadratic_zero_subst, _root_.pow_zero, one_mul])

theorem hasseShortK_coeff_ge (hp : 2 < p) (j : ℕ) (hj : p ≤ j) :
    coeff j (hasseShortK p hp) = 0 :=
  shortSubstReduction_coeff_ge _ j hj

theorem hasseShortK_coeff_zero (hp : 2 < p) : coeff 0 (hasseShortK p hp) = 0 := by
  rw [hasseShortK_coeff_lt hp 0 (Fact.out : p.Prime).pos, layerCoefficient_eq_residue]
  have hz : (p : ℚ_[p])^0 * coeff 0 ((quadratic rationalPotential (rationalH 0)).map
      (algebraMap ℚ ℚ_[p])) = 0 := by
    rw [coeff_map, coeff_zero_eq_constantCoeff_apply, rationalK_constant, map_zero, mul_zero]
  rw [integralResidue_congr _ integral_zero hz]
  exact map_zero (PadicInt.toZMod (p := p))

/-- Degree bound: `K0` is a polynomial of degree below `p`. -/
theorem hasseShortK_support (hp : 2 < p) (j : ℕ) (hj : coeff j (hasseShortK p hp) ≠ 0) :
    0 < j ∧ j < p := by
  refine ⟨Nat.pos_of_ne_zero ?_, not_le.mp fun h => hj (hasseShortK_coeff_ge hp j h)⟩
  rintro rfl
  exact hj (hasseShortK_coeff_zero hp)

theorem coeff_natCast_pow_mul {K : Type*} [CommRing K] (a k n : ℕ) (f : PowerSeries K) :
    coeff n ((a : PowerSeries K)^k * f) = (a : K)^k * coeff n f := by
  rw [show (a : PowerSeries K) = C (a : K) from (map_natCast C a).symm, ← map_pow, coeff_C_mul]

/-- **P3 fourth layer of K.** `p^4 K ≡ K0(X^p)` in every coefficient `n < N ≤ p^2`. -/
theorem actualK_fourth_frobenius (hp : 11 ≤ p) (c : ℚ) (hc : ¬p ∣ c.den)
    (N : ℕ) (hN : N ≤ p^2) (n : ℕ) (hn : n < N) :
    actualKFourth c hc N hN n hn =
      coeff n (expand p (Fact.out : p.Prime).ne_zero (hasseShortK p (by omega))) := by
  have hp2 : 2 < p := by omega
  have hnp : n < p^2 := hn.trans_le hN
  have hX := qSubst_cap_zero (expand_cap_zero (lambertQuadratic_zero_cap_zero hp2) N hN)
  have hY := qSubst_cap_zero (depletionRemainder_cap_zero hp2 c hc N hN)
  have hXn : Integral (coeff n (PowerSeries.map (algebraMap ℚ ℚ_[p]) ((expand p (Fact.out : p.Prime).ne_zero (lambertQuadratic 0)).subst qSeries))) := by
    simpa only [_root_.pow_zero, one_mul] using hX n hn
  have hYn : Integral (coeff n (PowerSeries.map (algebraMap ℚ ℚ_[p]) ((depletionRemainder p c).subst qSeries))) := by
    simpa only [_root_.pow_zero, one_mul] using hY n hn
  have he := congrArg (fun f : PowerSeries ℚ => coeff n (f.map (algebraMap ℚ ℚ_[p])))
    (rationalK_scaled_depletion (p := p) (by omega) c)
  simp only [map_add, map_mul, map_pow, map_natCast] at he
  have hcoef : ∀ f : PowerSeries ℚ_[p], coeff n ((p : PowerSeries ℚ_[p]) * f) =
      (p : ℚ_[p]) * coeff n f := fun f => by
    simpa only [pow_one] using coeff_natCast_pow_mul p 1 n f
  rw [hcoef, coeff_natCast_pow_mul] at he
  unfold actualKFourth layerAt
  rw [layerCoefficient_eq_residue]
  refine (integralResidue_congr_mod_prime _ hXn hYn he).trans ?_
  rw [hasseShortK, expandSubst_residue _ n hnp hXn]

end Zeta7Auxiliary

import Zeta7Proof.AuxiliaryThirdLayer
import Zeta7Proof.AuxiliaryHasseFrobenius

/-! The reduced actual singular part is `Gamma * F(X^p)` in every coefficient below `p^2`.
`F` is an explicit short series: below `p` its coefficients are the reductions of the
original `rationalH 0`, and it vanishes from `p` on. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
namespace Zeta7Auxiliary
open PowerSeries Zeta7Main Zeta7Common

section Congruence
variable {R : Type*} [CommRing R]

theorem coeff_pow_eq_zero_of_lt {g : PowerSeries R} (hg : constantCoeff g = 0)
    {n k : ℕ} (hk : n < k) : coeff n (g^k) = 0 := by
  obtain ⟨v, hv⟩ := X_dvd_iff.mpr hg
  rw [hv, mul_pow, coeff_X_pow_mul', if_neg (by omega)]

/-- Substitution of a series without constant term only reads coefficients up to `n`. -/
theorem coeff_subst_congr {A B g : PowerSeries R} (hg : constantCoeff g = 0) (n : ℕ)
    (h : ∀ k, k ≤ n → coeff k A = coeff k B) :
    coeff n (A.subst g) = coeff n (B.subst g) := by
  have hs := HasSubst.of_constantCoeff_zero' hg
  rw [coeff_subst' hs, coeff_subst' hs]
  apply finsum_congr
  intro k
  by_cases hk : k ≤ n
  · rw [h k hk]
  · simp only [smul_eq_mul, coeff_pow_eq_zero_of_lt hg (not_le.mp hk), mul_zero]

theorem coeff_mul_congr (M : PowerSeries R) {A B : PowerSeries R} (n : ℕ)
    (h : ∀ k, k ≤ n → coeff k A = coeff k B) :
    coeff n (M*A) = coeff n (M*B) := by
  rw [coeff_mul, coeff_mul]
  apply Finset.sum_congr rfl
  intro x hx
  rw [h x.2 (by have := Finset.HasAntidiagonal.mem_antidiagonal.mp hx; omega)]

end Congruence

variable {p : ℕ} [Fact p.Prime]

/-- Index range: below `p^2`, the quotient by `p` is below `p`. -/
theorem div_prime_lt_of_lt_sq {n : ℕ} (hn : n < p^2) : n/p < p :=
  (Nat.div_lt_iff_lt_mul (Fact.out : p.Prime).pos).mpr (by simpa only [pow_two] using hn)

theorem coeff_expand_congr_short {R : Type*} [CommRing R] {A B : PowerSeries R}
    (h : ∀ j, j < p → coeff j A = coeff j B) (n : ℕ) (hn : n < p^2) :
    coeff n (expand p (Fact.out : p.Prime).ne_zero A) =
      coeff n (expand p (Fact.out : p.Prime).ne_zero B) := by
  rw [coeff_expand, coeff_expand]
  split_ifs
  · exact h _ (div_prime_lt_of_lt_sq hn)
  · rfl

/-- In characteristic `p`, Frobenius expansion commutes with substitution. -/
theorem zmod_expand_subst (A b : PowerSeries (ZMod p)) (hb : constantCoeff b = 0) :
    (expand p (Fact.out : p.Prime).ne_zero A).subst b =
      expand p (Fact.out : p.Prime).ne_zero (A.subst b) := by
  have hs := HasSubst.of_constantCoeff_zero' hb
  have hp0 := (Fact.out : p.Prime).ne_zero
  have h := expand_subst (S := ZMod p) p hp0 hs A
  rw [expand_apply, subst_comp_subst_apply (HasSubst.X_pow hp0) hs, subst_pow hs,
    subst_X hs, zmod_series_frobenius p b]
  exact h.symm

/-- The Lambert series truncated strictly below `p`, lifted to `ℤ_[p]`. -/
def integralShortLambert (p : ℕ) [Fact p.Prime] : PowerSeries ℤ_[p] :=
  mk fun j => if h : j < p then
    ⟨((coeff j GSeries : ℚ) : ℚ_[p]), lambert_integral_below_prime j h⟩ else 0

theorem integralShortLambert_coeff_lt (j : ℕ) (hj : j < p) :
    coeff j ((integralShortLambert p).map (algebraMap ℤ_[p] ℚ_[p])) =
      coeff j (GSeries.map (algebraMap ℚ ℚ_[p])) := by
  simp only [coeff_map, integralShortLambert, coeff_mk, dif_pos hj, PadicInt.algebraMap_apply]
  rfl

theorem integralShortLambert_coeff_ge (j : ℕ) (hj : p ≤ j) :
    coeff j (integralShortLambert p) = 0 := by
  simp only [integralShortLambert, coeff_mk, dif_neg (not_lt.mpr hj)]

theorem integralQCoordinate_constant : constantCoeff (integralQCoordinate p) = 0 :=
  integerSeriesLift_constant p qSeries qSeries_integer qSeries_constant

/-- Integral model of `rationalH 0` below `p`. -/
def integralShortH (p : ℕ) [Fact p.Prime] : PowerSeries ℤ_[p] :=
  integralB p * (integralShortLambert p).subst (integralQCoordinate p)

/-- Integral model of the singular part below `p^2`. -/
def integralShortSingular (p : ℕ) [Fact p.Prime] : PowerSeries ℤ_[p] :=
  integralB p * (expand p (Fact.out : p.Prime).ne_zero
    (integralShortLambert p)).subst (integralQCoordinate p)

def reducedShortH (p : ℕ) [Fact p.Prime] : PowerSeries (ZMod p) :=
  (integralShortH p).map PadicInt.toZMod

/-- The paper's short series `F`: reductions of `rationalH 0` below `p`, zero from `p` on. -/
def hasseShortSeries (p : ℕ) [Fact p.Prime] : PowerSeries (ZMod p) :=
  mk fun j => if j < p then coeff j (reducedShortH p) else 0

theorem reducedQCoordinate_constant :
    constantCoeff ((integralQCoordinate p).map (PadicInt.toZMod (p := p))) = 0 := by
  change PadicInt.toZMod (constantCoeff (integralQCoordinate p)) = 0
  rw [integralQCoordinate_constant, map_zero]

theorem map_integral_subst {S : Type*} [CommRing S] (h : ℤ_[p] →+* S)
    (A : PowerSeries ℤ_[p]) :
    PowerSeries.map h (A.subst (integralQCoordinate p) : PowerSeries ℤ_[p]) =
      (PowerSeries.map h A).subst (PowerSeries.map h (integralQCoordinate p)) :=
  map_subst (HasSubst.of_constantCoeff_zero' integralQCoordinate_constant) A

/-- The global characteristic-`p` identity behind the singular layer. -/
theorem reducedShortSingular_eq (hp : 5 ≤ p) :
    (integralShortSingular p).map PadicInt.toZMod =
      hasseGammaSeries p hp * expand p (Fact.out : p.Prime).ne_zero (reducedShortH p) := by
  have hp0 := (Fact.out : p.Prime).ne_zero
  unfold integralShortSingular reducedShortH integralShortH
  rw [map_mul, map_mul, map_integral_subst, map_integral_subst, map_expand,
    zmod_expand_subst _ _ reducedQCoordinate_constant]
  change reducedB p * _ = _ * expand p hp0 (reducedB p * _)
  rw [map_mul, ← mul_assoc, ← reducedB_frobenius p hp]

theorem map_qSeries_subst {S : Type*} [CommRing S] (h : ℚ →+* S) (A : PowerSeries ℚ) :
    PowerSeries.map h (A.subst qSeries : PowerSeries ℚ) =
      (PowerSeries.map h A).subst (PowerSeries.map h qSeries) :=
  map_subst (HasSubst.of_constantCoeff_zero' qSeries_constant) A

theorem map_integralB : (integralB p).map (algebraMap ℤ_[p] ℚ_[p]) =
    BSeries.map (algebraMap ℚ ℚ_[p]) := integerSeriesLift_map p _ _

theorem map_integralQ : (integralQCoordinate p).map (algebraMap ℤ_[p] ℚ_[p]) =
    qSeries.map (algebraMap ℚ ℚ_[p]) := integerSeriesLift_map p _ _

theorem qSeries_map_constant : constantCoeff (qSeries.map (algebraMap ℚ ℚ_[p])) = 0 := by
  change (algebraMap ℚ ℚ_[p]) (constantCoeff qSeries) = 0
  rw [qSeries_constant, map_zero]

/-- The integral model agrees with the actual singular part below `p^2`. -/
theorem singularH_coeff_eq_short (n : ℕ) (hn : n < p^2) :
    coeff n ((singularH p).map (algebraMap ℚ ℚ_[p])) =
      coeff n ((integralShortSingular p).map (algebraMap ℤ_[p] ℚ_[p])) := by
  unfold singularH integralShortSingular
  rw [map_mul (PowerSeries.map (algebraMap ℚ ℚ_[p])),
    map_mul (PowerSeries.map (algebraMap ℤ_[p] ℚ_[p])), map_qSeries_subst, map_integral_subst,
    map_integralB, map_integralQ, map_expand, map_expand]
  apply coeff_mul_congr
  intro k hk
  apply coeff_subst_congr qSeries_map_constant
  intro i hi
  exact (coeff_expand_congr_short (fun j hj => integralShortLambert_coeff_lt j hj) i
    (by omega)).symm

/-- The integral model agrees with `rationalH 0` below `p`. -/
theorem rationalH_zero_coeff_eq_short (j : ℕ) (hj : j < p) :
    coeff j ((rationalH 0).map (algebraMap ℚ ℚ_[p])) =
      coeff j ((integralShortH p).map (algebraMap ℤ_[p] ℚ_[p])) := by
  unfold rationalH integralShortH
  rw [map_zero, add_zero, map_mul (PowerSeries.map (algebraMap ℚ ℚ_[p])),
    map_mul (PowerSeries.map (algebraMap ℤ_[p] ℚ_[p])), map_qSeries_subst, map_integral_subst,
    map_integralB, map_integralQ]
  apply coeff_mul_congr
  intro k hk
  apply coeff_subst_congr qSeries_map_constant
  intro i hi
  exact (integralShortLambert_coeff_lt i (by omega)).symm

theorem zero_den_not_dvd : ¬p ∣ (0 : ℚ).den := by
  rw [Rat.den_zero]
  exact (Fact.out : p.Prime).not_dvd_one

theorem toZMod_eq_layer {N e : ℕ} {F : PowerSeries ℚ_[p]} (h : Cap N e F) (n : Fin N)
    (a : ℤ_[p]) (ha : (a : ℚ_[p]) = (p : ℚ_[p])^e * coeff n.val F) :
    PadicInt.toZMod a = layerCoefficient h n := by
  unfold layerCoefficient
  congr 1
  exact Subtype.ext ha

/-- Exact coefficient theorem for `F` below `p`. -/
theorem hasseShortSeries_coeff_lt (j : ℕ) (hj : j < p) :
    coeff j (hasseShortSeries p) =
      layerCoefficient (rationalH_cap_zero (p := p) 0 zero_den_not_dvd) ⟨j, hj⟩ := by
  rw [hasseShortSeries, coeff_mk, if_pos hj, reducedShortH, coeff_map]
  apply toZMod_eq_layer
  rw [pow_zero, one_mul, rationalH_zero_coeff_eq_short j hj, coeff_map]
  rfl

theorem hasseShortSeries_coeff_ge (j : ℕ) (hj : p ≤ j) :
    coeff j (hasseShortSeries p) = 0 := by
  rw [hasseShortSeries, coeff_mk, if_neg (not_lt.mpr hj)]

theorem hasseShortSeries_coeff_lt_reduced (j : ℕ) (hj : j < p) :
    coeff j (hasseShortSeries p) = coeff j (reducedShortH p) := by
  rw [hasseShortSeries, coeff_mk, if_pos hj]

/-- Only coefficients of `F` below `p` contribute to `F(X^p)` below `p^2`. -/
theorem expand_hasseShort_coeff (n : ℕ) (hn : n < p^2) :
    coeff n (expand p (Fact.out : p.Prime).ne_zero (hasseShortSeries p)) =
      (if p ∣ n then coeff (n/p) (hasseShortSeries p) else 0) ∧
    (p ∣ n → n/p < p) :=
  ⟨coeff_expand _ _ _, fun _ => div_prime_lt_of_lt_sq hn⟩

theorem gamma_expand_short_congr (M : PowerSeries (ZMod p)) (n : ℕ) (hn : n < p^2) :
    coeff n (M * expand p (Fact.out : p.Prime).ne_zero (hasseShortSeries p)) =
      coeff n (M * expand p (Fact.out : p.Prime).ne_zero (reducedShortH p)) := by
  apply coeff_mul_congr
  intro k hk
  exact coeff_expand_congr_short (fun j hj => hasseShortSeries_coeff_lt_reduced j hj) k
    (by omega)

/-- **P3 singular identification.** The reduced actual singular part equals
`Gamma * F(X^p)` in each coefficient `n < N ≤ p^2`. -/
theorem singularH_gamma_frobenius (hp : 5 ≤ p) (N : ℕ) (hN : N ≤ p^2) (n : Fin N) :
    layerCoefficient (singularH_cap_zero N hN) n =
      coeff n.val (hasseGammaSeries p hp *
        expand p (Fact.out : p.Prime).ne_zero (hasseShortSeries p)) := by
  have hn : n.val < p^2 := n.isLt.trans_le hN
  rw [gamma_expand_short_congr _ n.val hn, ← reducedShortSingular_eq hp, coeff_map]
  symm
  apply toZMod_eq_layer
  rw [pow_zero, one_mul, singularH_coeff_eq_short n.val hn, coeff_map]
  rfl

/-- **P3 third layer of H.** -/
theorem rationalH_third_layer_gamma (hp : 11 ≤ p) (c : ℚ) (hc : ¬p ∣ c.den)
    (N : ℕ) (hN : N ≤ p^2) (n : Fin N) :
    layerCoefficient (rationalH_cap_three c hc N hN) n =
      coeff n.val (hasseGammaSeries p (by omega) *
        expand p (Fact.out : p.Prime).ne_zero (hasseShortSeries p)) := by
  rw [rationalH_third_layer_depletion (by omega) c hc N hN n,
    singularH_gamma_frobenius (by omega) N hN n]

theorem euler_mul_expand (M F : PowerSeries (ZMod p)) :
    euler (M * expand p (Fact.out : p.Prime).ne_zero F) =
      euler M * expand p (Fact.out : p.Prime).ne_zero F := by
  rw [euler_mul_general, euler_frobenius_zero, mul_zero, add_zero]

/-- **P3 third layers of DH and D²H**, in the form `(D^k Gamma) F(X^p)`. -/
theorem rationalH_third_jets_gamma (hp : 11 ≤ p) (c : ℚ) (hc : ¬p ∣ c.den)
    (N : ℕ) (hN : N ≤ p^2) (n : Fin N) :
    layerCoefficient (rationalH_cap_three c hc N hN).euler n =
      coeff n.val (euler (hasseGammaSeries p (by omega)) *
        expand p (Fact.out : p.Prime).ne_zero (hasseShortSeries p)) ∧
    layerCoefficient (rationalH_cap_three c hc N hN).euler.euler n =
      coeff n.val (euler (euler (hasseGammaSeries p (by omega))) *
        expand p (Fact.out : p.Prime).ne_zero (hasseShortSeries p)) := by
  obtain ⟨h1, h2⟩ := rationalH_third_jet_layers (by omega) c hc N hN n
  rw [h1, h2, singularH_gamma_frobenius (by omega) N hN n, ← euler_mul_expand,
    ← euler_mul_expand, ← euler_mul_expand, euler_coeff, euler_coeff, euler_coeff]
  exact ⟨rfl, by ring⟩

end Zeta7Auxiliary

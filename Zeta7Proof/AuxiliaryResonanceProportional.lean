import Zeta7Proof.AuxiliaryResonanceReduction

/-! P5 modulo `p`: uniqueness of quadratically forced solutions with fixed leading coefficient,
the proportionality `v̄⁻ - w₀ = λ v̄⁺`, `h̄⁻ = λ h̄⁺` with an explicit `λ ≠ 0`, and the
nonvanishing `h̄⁺ ≠ 0` from the proved polynomial degree obstruction. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
namespace Zeta7Auxiliary
open PowerSeries Zeta7Common
open scoped LaurentSeries

variable {p : ℕ} [Fact p.Prime]

/-! ### The reduced correction point -/

def redTenth (p : ℕ) [Fact p.Prime] : ZMod p := PadicInt.toZMod (tenthPt p)

theorem one_add_ten_redTenth (hp : 11 ≤ p) : 1 + 10 * redTenth p = 0 := by
  have h := congrArg PadicInt.toZMod (ten_mul_tenthPt (p := p) hp)
  rw [map_mul, map_neg, map_one, map_ofNat] at h
  rw [redTenth, h]; ring

theorem bandOneLow_red_ne (hp : 11 ≤ p) : (bandOneLow (ZMod p)).eval (redTenth p) ≠ 0 := by
  have hu := (bandOneLow_unit (p := p) hp).map (PadicInt.toZMod (p := p))
  have he : PadicInt.toZMod ((bandOneLow ℤ_[p]).eval (tenthPt p)) =
      (bandOneLow (ZMod p)).eval (redTenth p) := by
    simp [bandOneLow, redTenth, map_ofNat]
  rw [he] at hu
  exact hu.ne_zero

theorem bandB0_zmod : (bandB0 : PowerSeries (ZMod p)) =
    X * ((bandOneLow (ZMod p) : Polynomial (ZMod p)) : PowerSeries (ZMod p)) := by
  simp [bandB0, bandOneLow, map_ofNat]
  ring

theorem topPivot_zmod_ne (hp : 11 ≤ p) (m : ℕ) (hm : m + 2 < p) :
    bandWeight 4 ((m : ℕ) : ZMod p) ≠ 0 := by
  have hu := (topPivot_isUnit (p := p) hp m hm).map (PadicInt.toZMod (p := p))
  rw [map_bandWeight, map_natCast] at hu
  exact hu.ne_zero

theorem one_add_ten_X_ne_zero : (1 + 10 * Polynomial.X : Polynomial (ZMod p)) ≠ 0 := by
  intro h
  have h0 := congrArg (fun f : Polynomial (ZMod p) => f.coeff 0) h
  simp at h0

/-! ### Uniqueness -/

/-- **Uniqueness for fixed leading coefficient.** A quadratically forced reduced solution of
degree `≤ p - 2` is a multiple of `ā⁺`, and its forcing the same multiple of `h̄⁺`. -/
theorem band_unique (hp : 11 ≤ p) (α : PowerSeries (ZMod p))
    (hα : ∀ m, p - 2 < m → coeff m α = 0) (g : Polynomial (ZMod p)) (hg : g.natDegree ≤ 2)
    (h : bandSeries 0 α = X * ((1 + 10 * X) * (g : PowerSeries (ZMod p)))) :
    α = C (coeff (p - 2) α) * zred p (posA p) ∧
      g = Polynomial.C (coeff (p - 2) α) * redZ p (posH p) := by
  set l := coeff (p - 2) α with hl
  set β := α - C l * zred p (posA p) with hβ
  set γ := g - Polynomial.C l * redZ p (posH p) with hγ
  have hγd : γ.natDegree ≤ 2 := by
    refine (Polynomial.natDegree_sub_le _ _).trans (max_le hg ?_)
    refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
    exact Polynomial.natDegree_map_le.trans posH_natDegree
  have hband : bandSeries 0 β =
      ((Polynomial.X * ((1 + 10 * Polynomial.X) * γ) : Polynomial (ZMod p)) : PowerSeries (ZMod p)) := by
    have h10 : ((10 : Polynomial (ZMod p)) : PowerSeries (ZMod p)) = 10 :=
      map_ofNat Polynomial.coeToPowerSeries.ringHom 10
    rw [hβ, bandSeries_sub_gen, bandSeries_C_mul, h, redPos_band hp, hγ]
    simp only [Polynomial.coe_mul, Polynomial.coe_sub, Polynomial.coe_add, Polynomial.coe_X,
      Polynomial.coe_one, Polynomial.coe_C, h10]
    ring
  have hRdeg : (Polynomial.X * ((1 + 10 * Polynomial.X) * γ) : Polynomial (ZMod p)).natDegree ≤ 4 := by
    refine Polynomial.natDegree_mul_le.trans ?_
    have h1 : (Polynomial.X : Polynomial (ZMod p)).natDegree ≤ 1 := Polynomial.natDegree_X_le
    have h2 : ((1 + 10 * Polynomial.X) * γ : Polynomial (ZMod p)).natDegree ≤ 3 := by
      refine Polynomial.natDegree_mul_le.trans ?_
      have : (1 + 10 * Polynomial.X : Polynomial (ZMod p)).natDegree ≤ 1 := by compute_degree
      omega
    omega
  have hhigh : ∀ m, p - 2 ≤ m → coeff m β = 0 := by
    intro m hm
    rw [hβ, map_sub, coeff_C_mul]
    rcases Nat.eq_or_lt_of_le hm with rfl | hlt
    · rw [coeff_redPos_top hp, mul_one, hl, sub_self]
    · rw [hα m hlt, coeff_redPos_high m hlt, mul_zero, sub_zero]
  have hdesc : ∀ d m, 1 ≤ m → p - 2 - d ≤ m → coeff m β = 0 := by
    intro d
    induction d with
    | zero => intro m _ hm; exact hhigh m (by omega)
    | succ d ih =>
      intro m hm1 hm
      by_cases hmd : p - 2 - d ≤ m
      · exact ih m hm1 hmd
      have hmv : m + 2 < p := by omega
      have hc := congrArg (coeff (m + 4)) hband
      rw [Polynomial.coeff_coe, Polynomial.coeff_eq_zero_of_natDegree_lt (by omega),
        coeff_bandSeries, sum_range_five] at hc
      rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), if_pos (by omega),
        if_pos (by omega), show m + 4 - 0 = m + 4 by omega, show m + 4 - 1 = m + 3 by omega,
        show m + 4 - 2 = m + 2 by omega, show m + 4 - 3 = m + 1 by omega,
        show m + 4 - 4 = m by omega, ih (m + 4) (by omega) (by omega),
        ih (m + 3) (by omega) (by omega), ih (m + 2) (by omega) (by omega),
        ih (m + 1) (by omega) (by omega)] at hc
      simp only [sub_zero, mul_zero, zero_add] at hc
      exact (mul_eq_zero.mp hc).resolve_left (topPivot_zmod_ne hp m hmv)
  have hβC : β = C (coeff 0 β) := by
    ext m
    rw [coeff_C]
    split_ifs with hm
    · rw [hm]
    · exact hdesc p m (by omega) (by omega)
  -- the constant part
  have hconst : Polynomial.C (coeff 0 β) * bandOneLow (ZMod p) =
      (1 + 10 * Polynomial.X) * γ := by
    apply Polynomial.coe_injective
    apply X_mul_cancel (R := ZMod p)
    have h2 := hband
    rw [hβC, bandSeries_zero_C, bandB0_zmod] at h2
    simp only [Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_X] at h2 ⊢
    rw [← h2]
    ring
  have hev := congrArg (Polynomial.eval (redTenth p)) hconst
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_add, Polynomial.eval_one,
    Polynomial.eval_X, Polynomial.eval_ofNat] at hev
  rw [one_add_ten_redTenth hp, zero_mul] at hev
  have hβ0 : coeff 0 β = 0 := (mul_eq_zero.mp hev).resolve_right (bandOneLow_red_ne hp)
  have hγ0 : γ = 0 := by
    rw [hβ0, map_zero, zero_mul] at hconst
    exact (mul_eq_zero.mp hconst.symm).resolve_left one_add_ten_X_ne_zero
  constructor
  · have : β = 0 := by rw [hβC, hβ0, map_zero]
    rw [hβ] at this
    exact sub_eq_zero.mp this
  · exact sub_eq_zero.mp hγ0

/-! ### Proportionality -/

/-- The proportionality constant `λ = -lead(A₀)`. -/
def resLambda (p : ℕ) [Fact p.Prime] (hp : 11 ≤ p) : ZMod p := -homLead p hp

theorem resLambda_ne_zero (hp : 11 ≤ p) : resLambda p hp ≠ 0 :=
  neg_ne_zero.mpr (homLead_ne_zero hp)

/-- **Modulo-`p` proportionality:** `ã⁻ - A₀ = λ X^p ā⁺` and `h̄⁻ = λ h̄⁺`, with `λ ≠ 0`.
Equivalently `v̄⁻ - w₀ = λ v̄⁺` after multiplying by `P̄ x^{-p}`. -/
theorem resonance_proportional (hp : 11 ≤ p) :
    zred p (negA p) - (homA0 p (by omega) : PowerSeries (ZMod p)) =
        X^p * (C (resLambda p hp) * zred p (posA p)) ∧
      redZ p (negH p) = Polynomial.C (resLambda p hp) * redZ p (posH p) ∧
      resLambda p hp ≠ 0 := by
  have hu := band_unique hp (resAlpha p hp) (resAlpha_high hp) (redZ p (negH p))
    (Polynomial.natDegree_map_le.trans negH_natDegree) (resAlpha_band hp)
  rw [resAlpha_top hp] at hu
  refine ⟨?_, hu.2, resLambda_ne_zero hp⟩
  change resDelta p hp = _
  rw [resDelta_eq hp, hu.1]
  rfl

/-! ### Bridge to the proved rational kernel theorem -/

open Zeta7FiniteCalculus in
theorem pLM_laurentD (g : PowerSeries (ZMod p)) :
    laurentD (primeLaurentMap p g) = primeLaurentMap p (euler g) :=
  laurentD_powerSeries g

open Zeta7FiniteCalculus in
theorem embed_polyP : embed (primePolynomialMap p (hassePolyP : Polynomial (ZMod p))) =
    primeLaurentMap p (bandP : PowerSeries (ZMod p)) := by
  have h := embed_polynomial (K := ZMod p) (hassePolyP : Polynomial (ZMod p))
  rw [hassePolyP_coe] at h
  exact h

open Zeta7FiniteCalculus in
theorem embed_polyW : embed (primePolynomialMap p (hassePolyW : Polynomial (ZMod p))) =
    primeLaurentMap p (bandW : PowerSeries (ZMod p)) := by
  have h := embed_polynomial (K := ZMod p) (hassePolyW : Polynomial (ZMod p))
  rw [hassePolyW_coe] at h
  exact h

theorem pLM_inv (g : PowerSeries (ZMod p)) (hg : constantCoeff g ≠ 0) :
    primeLaurentMap p g⁻¹ = (primeLaurentMap p g)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  rw [← map_mul, PowerSeries.mul_inv_cancel _ hg, map_one]

open Zeta7FiniteCalculus in
theorem embed_hassePotential :
    embed (hassePotentialRational p) = primeLaurentMap p (redV2 p) := by
  have hc : constantCoeff ((bandP : PowerSeries (ZMod p))^2) ≠ 0 := by
    rw [map_pow]; exact pow_ne_zero _ bandP_zmod_const
  rw [hassePotentialRational, map_div₀, map_pow, embed_polyP, embed_polyW, redV2, map_mul,
    pLM_inv _ hc, map_pow, div_eq_mul_inv]

open Zeta7FiniteCalculus in
theorem embed_hasseOperator (hp : 11 ≤ p) (F : Polynomial (ZMod p)) :
    embed (hasseOperatorRational p (primePolynomialMap p F)) =
      primeLaurentMap p (redL p (F : PowerSeries (ZMod p))) := by
  have hF : embed (primePolynomialMap p F) = primeLaurentMap p (F : PowerSeries (ZMod p)) :=
    embed_polynomial F
  have h2 : (2 : (ZMod p)⸨X⸩) ≠ 0 := by
    have : (2 : (ZMod p)⸨X⸩) = HahnSeries.C 2 := (map_ofNat HahnSeries.C 2).symm
    rw [this]
    exact (map_ne_zero _).mpr (two_ne_zero_zmod hp)
  have hhalf : primeLaurentMap p (C (halfZMod p)) = (2 : (ZMod p)⸨X⸩)⁻¹ := by
    have hc : primeLaurentMap p (C (halfZMod p)) = HahnSeries.C (halfZMod p) :=
      HahnSeries.ofPowerSeries_C _
    rw [hc, halfZMod, map_inv₀, map_ofNat]
  simp only [hasseOperatorRational, map_sub, map_mul, map_div₀, embed_rationalD, hF,
    embed_hassePotential, map_ofNat]
  simp only [redL, resOp, thetaS_zero_eq, map_sub, map_mul, pLM_laurentD, hhalf]
  rw [div_eq_mul_inv]
  ring

theorem trunc_redPos (hp : 11 ≤ p) :
    ((PowerSeries.trunc (p - 1) (zred p (posA p)) : Polynomial (ZMod p)) : PowerSeries (ZMod p)) =
      zred p (posA p) := by
  ext m
  rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc]
  split_ifs with h
  · rfl
  · rw [coeff_redPos_high m (by omega)]

theorem trunc_redPos_natDegree (hp : 11 ≤ p) :
    (PowerSeries.trunc (p - 1) (zred p (posA p))).natDegree = p - 2 := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro m hm
    rw [PowerSeries.coeff_trunc]
    split_ifs with h
    · exfalso; omega
    · rfl
  · rw [PowerSeries.coeff_trunc, if_pos (by omega), coeff_redPos_top hp]
    exact one_ne_zero

/-- **Nonvanishing of the positive forcing**, from the proved degree obstruction for polynomial
elements of the actual reduced kernel. -/
theorem posH_red_ne_zero (hp : 11 ≤ p) : redZ p (posH p) ≠ 0 := by
  intro h0
  have hb := redPos_band (p := p) hp
  rw [h0, Polynomial.coe_zero, mul_zero, mul_zero] at hb
  have hAc := trunc_redPos (p := p) hp
  have hAd := trunc_redPos_natDegree (p := p) hp
  obtain ⟨A, hA⟩ : ∃ A, A = PowerSeries.trunc (p - 1) (zred p (posA p)) := ⟨_, rfl⟩
  rw [← hA] at hAc hAd
  have hA0 : A ≠ 0 := by
    intro h; rw [h, Polynomial.natDegree_zero] at hAd; omega
  set F := (hassePolyP : Polynomial (ZMod p)) * A with hFdef
  have hF0 : F ≠ 0 := mul_ne_zero hassePolyP_ne_zero_zmod hA0
  have hFd : F.natDegree = p := by
    rw [hFdef, Polynomial.natDegree_mul hassePolyP_ne_zero_zmod hA0, hassePolyP_natDegree p hp, hAd]
    omega
  have hL : redL p (F : PowerSeries (ZMod p)) = 0 := by
    have hid := band_identity (halfZMod p) (halfZMod_mul hp) (redV2 p) redV2_band 0
      (A : PowerSeries (ZMod p))
    rw [hAc, hb] at hid
    have hcoe : (F : PowerSeries (ZMod p)) = bandP * zred p (posA p) := by
      rw [hFdef, Polynomial.coe_mul, hassePolyP_coe_reducedP, ← bandP_zmod, hAc]
    rw [hcoe]
    apply (bandP_isUnit (R := ZMod p)).mul_left_cancel
    rw [mul_zero]
    exact hid
  have he : hasseOperatorRational p (primePolynomialMap p F) = 0 := by
    apply Zeta7FiniteCalculus.embed_injective
    rw [embed_hasseOperator hp, hL, map_zero, map_zero]
  have := hasseOperatorRational_polynomial_degree p hp F hF0 he
  omega

end Zeta7Auxiliary

import Zeta7Proof.AuxiliaryLambertDepletion

/-! Exact depletion in the original x-coordinate, with integral regular and
truncated singular parts. No radius or target identification is used. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
namespace Zeta7Auxiliary
open PowerSeries Zeta7Main Zeta7Common
variable {p : ℕ} [Fact p.Prime]

def regularH (p : ℕ) (c : ℚ) : PowerSeries ℚ :=
  BSeries * ((depletedLambert p).subst qSeries + C c)

def singularH (p : ℕ) [Fact p.Prime] : PowerSeries ℚ :=
  BSeries * ((expand p (Fact.out : p.Prime).ne_zero GSeries).subst qSeries)

theorem rationalH_depletion (hp7 : p ≠ 7) (c : ℚ) :
    rationalH c = regularH p c + C ((p : ℚ)⁻¹^3)*singularH p := by
  have hq := HasSubst.of_constantCoeff_zero qSeries_constant
  have h := congrArg (substAlgHom hq) (GSeries_depletion hp7)
  have hC : substAlgHom hq (C ((p : ℚ)⁻¹^3)) = C ((p : ℚ)⁻¹^3) :=
    (substAlgHom hq).commutes _
  rw [map_add, map_mul, hC] at h
  simp only [coe_substAlgHom] at h
  unfold rationalH regularH singularH
  rw [h]
  ring

theorem rationalH_scaled_depletion (hp7 : p ≠ 7) (c : ℚ) :
    C ((p : ℚ)^3)*rationalH c =
      singularH p + C ((p : ℚ)^3)*regularH p c := by
  rw [rationalH_depletion hp7 c, mul_add]
  have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  rw [← mul_assoc, ← map_mul, ← mul_pow, mul_inv_cancel₀ hpQ, one_pow, map_one, one_mul]
  ring

theorem regularH_cap_zero (c : ℚ) (hc : ¬p ∣ c.den) (N : ℕ) :
    Cap N 0 ((regularH p c).map (algebraMap ℚ ℚ_[p])) := by
  have hG := (depletedLambert_cap_zero (p := p) N).subst_integer
    qSeries_integer qSeries_constant
  have hc0 : Cap N 0 (C (c : ℚ_[p])) :=
    Cap.C (by simpa only [Integral, pow_zero, one_mul] using Padic.norm_rat_le_one hc)
  have h := (BSeries_integer.cap_zero (p := p) N).mul (hG.add hc0)
  have hs : PowerSeries.map (algebraMap ℚ ℚ_[p]) ((depletedLambert p).subst qSeries) =
      ((depletedLambert p).map (algebraMap ℚ ℚ_[p])).subst
        (qSeries.map (algebraMap ℚ ℚ_[p])) :=
    map_subst (HasSubst.of_constantCoeff_zero qSeries_constant) (depletedLambert p)
  have hcast : (algebraMap ℚ ℚ_[p]) c = (c : ℚ_[p]) := rfl
  unfold regularH
  rw [map_mul, map_add, map_C, hs, hcast]
  exact h

theorem expandedLambert_cap_zero (N : ℕ) (hN : N ≤ p^2) :
    Cap N 0 ((expand p (Fact.out : p.Prime).ne_zero GSeries).map (algebraMap ℚ ℚ_[p])) := by
  intro n hn
  rw [pow_zero, one_mul, coeff_map, coeff_expand]
  split_ifs with hd
  · change Integral ((coeff (n/p) GSeries : ℚ) : ℚ_[p])
    apply lambert_integral_below_prime
    apply (Nat.div_lt_iff_lt_mul (Fact.out : p.Prime).pos).mpr
    simpa only [pow_two] using hn.trans_le hN
  · simpa using (integral_zero (p := p))

theorem singularH_cap_zero (N : ℕ) (hN : N ≤ p^2) :
    Cap N 0 ((singularH p).map (algebraMap ℚ ℚ_[p])) := by
  have hG := (expandedLambert_cap_zero N hN).subst_integer qSeries_integer qSeries_constant
  have h := (BSeries_integer.cap_zero (p := p) N).mul hG
  have hs : PowerSeries.map (algebraMap ℚ ℚ_[p])
      ((expand p (Fact.out : p.Prime).ne_zero GSeries).subst qSeries) =
      ((expand p (Fact.out : p.Prime).ne_zero GSeries).map (algebraMap ℚ ℚ_[p])).subst
        (qSeries.map (algebraMap ℚ ℚ_[p])) :=
    map_subst (HasSubst.of_constantCoeff_zero qSeries_constant) _
  unfold singularH
  rw [map_mul, hs]
  exact h

/-- The exact integral remainder behind the third-layer congruence, including
both derivative jets. The remaining Frobenius identification is a separate step. -/
theorem actual_depletion_integral_remainder (hp7 : p ≠ 7) (c : ℚ)
    (hc : ¬p ∣ c.den) (N : ℕ) (hN : N ≤ p^2) :
    C ((p : ℚ)^3)*rationalH c = singularH p + C ((p : ℚ)^3)*regularH p c ∧
    Cap N 0 ((singularH p).map (algebraMap ℚ ℚ_[p])) ∧
    Cap N 0 ((regularH p c).map (algebraMap ℚ ℚ_[p])) ∧
    Cap N 0 ((euler (regularH p c)).map (algebraMap ℚ ℚ_[p])) ∧
    Cap N 0 ((euler (euler (regularH p c))).map (algebraMap ℚ ℚ_[p])) := by
  have hr := regularH_cap_zero c hc N
  exact ⟨rationalH_scaled_depletion hp7 c, singularH_cap_zero N hN, hr,
    by simpa only [map_euler] using hr.euler,
    by simpa only [map_euler] using hr.euler.euler⟩

end Zeta7Auxiliary

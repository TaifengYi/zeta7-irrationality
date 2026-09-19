/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in reference/cbirkbeck/LICENSE.
Authors: Chris Birkbeck
-/
import PadicLFunctions.Interpolation.Branches
import Mathlib.NumberTheory.Basic

/-! Continuity tools extracted from ResidueZeta.lean at the pinned upstream commit.
The extraction avoids unrelated exponential, residue and character-value developments.
Local adaptation: see KL_CONSTRUCTION_PROVENANCE.md. -/

namespace PadicLFunctions
open PadicInt Filter Topology
variable (p : ℕ) [Fact p.Prime]

/-- Exponent-congruence (the `p = 2`-valid analogue of `norm_onePAdicPow_sub_one`):
if `t ∈ p^k·ℤ_p` then `y^t ≡ 1 mod p^k`. Route: `t = p^k·c`, so
`y^t = (y^c)^{p^k}` and `dvd_sub_pow_of_dvd_sub` lifts `p ∣ y^c − 1` to
`p^{k+1} ∣ (y^c)^{p^k} − 1`. -/
private lemma onePAdicPow_sub_one_mem_span_pow {y : ℤ_[p]}
    (hy : y - 1 ∈ Ideal.span {(p : ℤ_[p])}) (k : ℕ) {t : ℤ_[p]}
    (ht : t ∈ Ideal.span {(p : ℤ_[p]) ^ k}) :
    PadicInt.onePAdicPow p y hy t - 1 ∈ Ideal.span {(p : ℤ_[p]) ^ k} := by
  -- `t = p^k · c`
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp ht
  -- `y^t = (y^c)^{p^k}` via `κ(n • a) = κ(a)^n` (`p^k·c = (p^k : ℕ) • c`)
  have hsmul : (p : ℤ_[p]) ^ k * c = (p ^ k : ℕ) • c := by
    rw [nsmul_eq_mul, Nat.cast_pow]
  have hpow : PadicInt.onePAdicPow p y hy ((p : ℤ_[p]) ^ k * c)
      = (PadicInt.onePAdicPow p y hy c) ^ (p ^ k) := by
    rw [hsmul, AddChar.map_nsmul_eq_pow]
  rw [hpow]
  -- `p ∣ y^c − 1`
  have hdvd1 : (p : ℤ_[p]) ∣ PadicInt.onePAdicPow p y hy c - 1 :=
    Ideal.mem_span_singleton.mp (PadicInt.onePAdicPow_sub_one_mem p y hy c)
  -- `p^{k+1} ∣ (y^c)^{p^k} − 1`, weaken to `p^k`
  have hsharp : ((p : ℤ_[p]) ^ (k + 1)) ∣
      (PadicInt.onePAdicPow p y hy c) ^ p ^ k - (1 : ℤ_[p]) ^ p ^ k :=
    dvd_sub_pow_of_dvd_sub hdvd1 k
  rw [one_pow] at hsharp
  exact Ideal.mem_span_singleton.mpr
    (dvd_trans (pow_dvd_pow _ (Nat.le_succ k)) hsharp)

/-- The `p = 2`-valid weak isometry: `‖y^t − 1‖ ≤ ‖t‖` for `y ∈ 1 + pℤ_p` and
every `t` (the sharp `‖y^t − 1‖ = ‖t‖·‖y − 1‖` of `norm_onePAdicPow_sub_one`
needs `p ≠ 2`; this one-sided bound holds for all `p`). -/
private lemma norm_onePAdicPow_sub_one_le {y : ℤ_[p]}
    (hy : y - 1 ∈ Ideal.span {(p : ℤ_[p])}) (t : ℤ_[p]) :
    ‖(PadicInt.onePAdicPow p y hy t : ℤ_[p]) - 1‖ ≤ ‖t‖ := by
  rcases eq_or_ne t 0 with rfl | ht
  · rw [show PadicInt.onePAdicPow p y hy 0 = 1 from AddChar.map_zero_eq_one _,
      sub_self, norm_zero]
  -- `‖t‖ = p^{-val t}`, so `t ∈ span{p^{val t}}`
  set k : ℕ := t.valuation with hk
  have htmem : t ∈ Ideal.span {(p : ℤ_[p]) ^ k} := by
    rw [← PadicInt.norm_le_pow_iff_mem_span_pow, PadicInt.norm_eq_zpow_neg_valuation ht]
  have hmem := onePAdicPow_sub_one_mem_span_pow p hy k htmem
  rw [PadicInt.norm_eq_zpow_neg_valuation ht]
  exact (PadicInt.norm_le_pow_iff_mem_span_pow _ k).mpr hmem

/-- R7.3a: the numerator pairing is continuous in `s` (the `p^m`-congruence
route: `s ≡ s' mod p^m ⟹ ⟨x⟩^{1−s} ≡ ⟨x⟩^{1−s'} mod p^m` uniformly in
`x`, through `onePAdicPow_sub_one_mem_pow`; then the measure norm bound).
Notably `p = 2` is allowed here. -/
theorem continuous_zetaNum_branch_pairing (m i : ℕ) :
    Continuous (fun s : ℤ_[p] =>
      (((PadicMeasure.zetaNum p m (branchChar p i (1 - s)) : ℤ_[p]))
        : ℚ_[p])) := by
  -- pointwise sup-norm bound `‖branchChar (1−s) x − branchChar (1−s') x‖ ≤ ‖s − s'‖`
  have hptbound : ∀ (s s' : ℤ_[p]) (x : ℤ_[p]ˣ),
      ‖(branchChar p i (1 - s) x : ℤ_[p]) - branchChar p i (1 - s') x‖ ≤ ‖s - s'‖ := by
    intro s s' x
    set ω : ℤ_[p] := (PadicInt.teichmuller p x : ℤ_[p]) with hω
    set κ : AddChar ℤ_[p] ℤ_[p] := PadicInt.onePAdicPow p (PadicInt.angleUnit p x : ℤ_[p])
      (PadicInt.angleUnit_sub_one_mem p x) with hκ
    -- `branchChar (1−s) x = ω^i · κ(1−s)` and `κ(1−s) = κ(1−s')·κ(s'−s)`
    have hadd : κ (1 - s) = κ (1 - s') * κ (s' - s) := by
      rw [← AddChar.map_add_eq_mul]; congr 1; ring
    have hdiff : (branchChar p i (1 - s) x : ℤ_[p]) - branchChar p i (1 - s') x
        = ω ^ i * κ (1 - s') * (κ (s' - s) - 1) := by
      rw [branchChar_apply, branchChar_apply, ← hω, ← hκ, hadd]; ring
    rw [hdiff]
    -- norms: `‖ω^i‖ ≤ 1`, `‖κ(1−s')‖ ≤ 1`, `‖κ(s'−s) − 1‖ ≤ ‖s'−s‖ = ‖s − s'‖`
    have hω1 : ‖ω ^ i‖ ≤ 1 := PadicInt.norm_le_one _
    have hκ1 : ‖κ (1 - s')‖ ≤ 1 := PadicInt.norm_le_one _
    have hκd : ‖κ (s' - s) - 1‖ ≤ ‖s' - s‖ :=
      norm_onePAdicPow_sub_one_le p (PadicInt.angleUnit_sub_one_mem p x) (s' - s)
    calc ‖ω ^ i * κ (1 - s') * (κ (s' - s) - 1)‖
        = ‖ω ^ i‖ * ‖κ (1 - s')‖ * ‖κ (s' - s) - 1‖ := by rw [norm_mul, norm_mul]
      _ ≤ 1 * 1 * ‖s' - s‖ := by gcongr
      _ = ‖s - s'‖ := by rw [one_mul, one_mul, norm_sub_rev]
  -- the `ℤ_[p]`-valued pairing is `1`-Lipschitz, hence continuous
  have hLip : LipschitzWith 1 (fun s : ℤ_[p] =>
      (PadicMeasure.zetaNum p m (branchChar p i (1 - s)) : ℤ_[p])) := by
    refine LipschitzWith.of_dist_le_mul fun s s' => ?_
    rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm, ← map_sub]
    refine le_trans (PadicMeasure.norm_apply_le p _ _) ?_
    refine (ContinuousMap.norm_le _ (norm_nonneg _)).2 fun x => ?_
    rw [ContinuousMap.coe_sub, Pi.sub_apply]
    exact hptbound s s' x
  exact continuous_subtype_val.comp hLip.continuous


end PadicLFunctions

/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import Mathlib.NumberTheory.ModularForms.Cusps
import Mathlib.Analysis.Complex.Periodic
import Mathlib.NumberTheory.ModularForms.QExpansion

/-!
# Level-raising operator for cusp forms (Miyake §4.6 Lemma 4.6.1)

The level-raising operator `ι_d : S_k(Γ₁(M)) → S_k(Γ₁(d·M))` sends a cusp
form `f` for `Γ₁(M)` to the cusp form `(ι_d f)(τ) = f(d·τ)` for the deeper
level `Γ₁(d·M)`, normalised so that the Fourier coefficient at `q^d`
equals the Fourier coefficient of `f` at `q`. In matrix form:
`ι_d f = d^{1-k} · (f ∣[k] [[d,0],[0,1]])`.

## Main definitions

* `levelRaiseMatrix d` — the matrix `α_d = [[d, 0], [0, 1]]` in `GL(2, ℝ)`.
* `levelRaiseFun d k f` — the level-raising operator at the function level.
* `levelRaiseConjOfDvd d γ hdvd` — the explicit `SL(2, ℤ)` element
  `α_d γ α_d⁻¹` constructed when `d ∣ γ.val 1 0`.
* `levelRaiseConj d M γ hγ` — specialisation of `levelRaiseConjOfDvd` to
  `γ ∈ Γ₁(d·M)` (where the divisibility is automatic).
* `CuspForm.restrictSubgroup` — restriction of a cusp form along a subgroup
  inclusion `Γ' ≤ Γ`.
* `levelRaise M d k` — the bundled `ℂ`-linear level-raising operator
  `S_k(Γ₁(M)) →ₗ[ℂ] S_k(Γ₁(d·M))`.

## References

* Miyake, *Modular Forms*, §4.6 (Lemma 4.6.1, p.162).
* Diamond–Shurman, *A First Course in Modular Forms*, §5.7 (DS (5.16)).
-/

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup CuspForm ModularFormClass
  UpperHalfPlane

open scoped MatrixGroups ModularForm Pointwise

noncomputable section

namespace HeckeRing.GL2

/-- The level-raising matrix `α_d = [[d, 0], [0, 1]]` in `GL(2, ℝ)`. -/
def levelRaiseMatrix (d : ℕ) [NeZero d] : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    !![(d : ℝ), 0; 0, 1]
    (by simp [Matrix.det_fin_two, Nat.cast_ne_zero.mpr (NeZero.ne d)])

/-- The level-raising operator at the function level: `(ι_d f)(τ) = f(d·τ)`,
realised as `ι_d f = d^{1-k} · (f ∣[k] α_d)` (the `d^{1-k}` scalar cancels the
`det^{k-1}` factor in the slash action). -/
def levelRaiseFun (d : ℕ) [NeZero d] (k : ℤ) (f : UpperHalfPlane → ℂ) :
    UpperHalfPlane → ℂ :=
  ((d : ℂ) ^ (1 - k)) • (f ∣[k] levelRaiseMatrix d)

/-- The denominator of `levelRaiseMatrix l` at any point is `1` (bottom row
of `α_l` is `(0, 1)`). -/
lemma denom_levelRaiseMatrix (l : ℕ) [NeZero l] (τ : UpperHalfPlane) :
    UpperHalfPlane.denom (levelRaiseMatrix l) (↑τ : ℂ) = 1 := by
  simp [UpperHalfPlane.denom, levelRaiseMatrix, Matrix.GeneralLinearGroup.mkOfDetNeZero]

/-- The determinant of `levelRaiseMatrix l` is positive (it equals `l > 0`). -/
lemma levelRaiseMatrix_det_pos (l : ℕ) [NeZero l] :
    (0 : ℝ) < (Matrix.GeneralLinearGroup.det (levelRaiseMatrix l) : ℝ) := by
  simp [levelRaiseMatrix, Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.det_fin_two,
    Nat.cast_pos.mpr (Nat.pos_of_neZero l)]

/-- The real absolute determinant of `levelRaiseMatrix l` is `l`. -/
lemma abs_levelRaiseMatrix_det_val (l : ℕ) [NeZero l] :
    |((Matrix.GeneralLinearGroup.det (levelRaiseMatrix l)) : ℝ)| = (l : ℝ) := by
  rw [abs_of_pos (levelRaiseMatrix_det_pos l)]
  simp [levelRaiseMatrix, Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.det_fin_two]

/-- The conjugation factor `σ` for `levelRaiseMatrix l` is the identity
(positive determinant). -/
lemma σ_levelRaiseMatrix (l : ℕ) [NeZero l] :
    UpperHalfPlane.σ (levelRaiseMatrix l) = ContinuousAlgEquiv.refl ℝ ℂ := by
  unfold UpperHalfPlane.σ; rw [if_pos (levelRaiseMatrix_det_pos l)]

/-- For γ ∈ Γ₁(d*M), the entry `γ.val 1 0` is divisible by `d`. -/
lemma Gamma1_dmul_lower_left_dvd (d M : ℕ) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma1 (d * M)) :
    (d : ℤ) ∣ γ.val 1 0 :=
  dvd_trans ⟨M, by push_cast; ring⟩
    ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp ((Gamma1_mem _ _).mp hγ).2.2)

/-- For `γ ∈ Γ₀(d*M)`, the entry `γ.val 1 0` is divisible by `d`. -/
lemma Gamma0_dmul_lower_left_dvd (d M : ℕ) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 (d * M)) :
    (d : ℤ) ∣ γ.val 1 0 :=
  dvd_trans ⟨M, by push_cast; ring⟩
    ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp hγ))

/-- Construction of `δ_d γ δ_d⁻¹` as an explicit `SL(2, ℤ)` element when
`d ∣ γ.val 1 0`. The formula `[[a, d*b], [c/d, e]]` is integer by hypothesis. -/
noncomputable def levelRaiseConjOfDvd (d : ℕ) [NeZero d] (γ : SL(2, ℤ))
    (hdvd : (d : ℤ) ∣ γ.val 1 0) : SL(2, ℤ) :=
  ⟨!![γ.val 0 0, d * γ.val 0 1; γ.val 1 0 / d, γ.val 1 1], by
    rw [Matrix.det_fin_two_of]
    linear_combination (Matrix.det_fin_two γ.val).symm.trans γ.property -
      γ.val 0 1 * Int.ediv_mul_cancel hdvd⟩

/-- Construction of `δ_d γ δ_d⁻¹` as an explicit `SL(2, ℤ)` element when
`γ ∈ Γ₁(d*M)`. The formula `[[a, d*b], [c/d, e]]` is integer because `d ∣ c`. -/
noncomputable def levelRaiseConj (d M : ℕ) [NeZero d] (γ : SL(2, ℤ))
    (hγ : γ ∈ Gamma1 (d * M)) : SL(2, ℤ) :=
  levelRaiseConjOfDvd d γ (Gamma1_dmul_lower_left_dvd d M γ hγ)

private lemma natCast_dvd_ediv_of_mul_dvd {d M : ℕ} [NeZero d] {c : ℤ}
    (h : ((d * M : ℕ) : ℤ) ∣ c) : (M : ℤ) ∣ c / d := by
  obtain ⟨j, hj⟩ := h
  refine ⟨j, ?_⟩
  rw [hj]
  push_cast
  rw [mul_assoc, Int.mul_ediv_cancel_left _ (Nat.cast_ne_zero.mpr (NeZero.ne d))]

/-- The conjugated matrix is in `Γ₀(M)` when `γ ∈ Γ₀(d*M)`. The (1,0) entry of
`δ_d γ δ_d⁻¹` is `c/d`, which is divisible by `M` because `c` is divisible by `d*M`. -/
lemma levelRaiseConjOfDvd_mem_Gamma0 (d M : ℕ) [NeZero d] (γ : SL(2, ℤ))
    (hγ : γ ∈ Gamma0 (d * M)) :
    levelRaiseConjOfDvd d γ (Gamma0_dmul_lower_left_dvd d M γ hγ) ∈ Gamma0 M := by
  rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact natCast_dvd_ediv_of_mul_dvd
    ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp hγ))

/-- The (1,1) entry of the conjugate equals the (1,1) entry of the original. -/
lemma levelRaiseConjOfDvd_lower_right (d : ℕ) [NeZero d] (γ : SL(2, ℤ))
    (hdvd : (d : ℤ) ∣ γ.val 1 0) :
    (levelRaiseConjOfDvd d γ hdvd).val 1 1 = γ.val 1 1 := rfl

/-- The matrix conjugation identity (in `GL(2, ℝ)`) for `levelRaiseConjOfDvd`:
`α_d * γ * α_d⁻¹ = (levelRaiseConjOfDvd d γ hdvd : GL₂(ℝ))`, equivalently
`levelRaiseMatrix d * mapGL ℝ γ =
mapGL ℝ (levelRaiseConjOfDvd d γ hdvd) * levelRaiseMatrix d`. -/
lemma levelRaiseMatrix_mul_mapGL (d : ℕ) [NeZero d] (γ : SL(2, ℤ))
    (hdvd : (d : ℤ) ∣ γ.val 1 0) :
    mapGL ℝ (levelRaiseConjOfDvd d γ hdvd) * levelRaiseMatrix d =
      levelRaiseMatrix d * mapGL ℝ γ := by
  have hdvd_real : ((d : ℕ) : ℝ) * (((γ.val 1 0 / (d : ℤ)) : ℤ) : ℝ) =
      ((γ.val 1 0 : ℤ) : ℝ) := by
    rw [mul_comm, ← Int.cast_natCast (R := ℝ), ← Int.cast_mul, Int.ediv_mul_cancel hdvd]
  have hentry (g : SL(2, ℤ)) (i j : Fin 2) :
      ((mapGL ℝ g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j =
        (g.val i j : ℝ) := rfl
  ext i j
  simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hentry]
  fin_cases i <;> fin_cases j <;>
    simp [levelRaiseMatrix, levelRaiseConjOfDvd, mul_comm, hdvd_real]

/-- The conjugated matrix is in `Γ₁(M)` (Miyake Lemma 4.6.1, conjugation step).

If `γ ∈ Γ₁(d*M)` then `δ_d γ δ_d⁻¹ ∈ Γ₁(M)`. -/
lemma levelRaiseConj_mem_Gamma1 (d M : ℕ) [NeZero d] (γ : SL(2, ℤ))
    (hγ : γ ∈ Gamma1 (d * M)) :
    levelRaiseConj d M γ hγ ∈ Gamma1 M := by
  obtain ⟨ha, he, hc⟩ := (Gamma1_mem _ _).mp hγ
  have h00 : (levelRaiseConj d M γ hγ).val 0 0 = γ.val 0 0 := rfl
  have h11 : (levelRaiseConj d M γ hγ).val 1 1 = γ.val 1 1 := rfl
  refine (Gamma1_mem _ _).mpr
    ⟨by rw [h00]; simpa using congr_arg (ZMod.castHom (Nat.dvd_mul_left M d) (ZMod M)) ha,
     by rw [h11]; simpa using congr_arg (ZMod.castHom (Nat.dvd_mul_left M d) (ZMod M)) he,
     ?_⟩
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact natCast_dvd_ediv_of_mul_dvd ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hc)

end HeckeRing.GL2

namespace ModularForm

variable {k : ℤ}

/-- Restrict a modular form along a subgroup inclusion `Γ' ≤ Γ`.

If `f` is `Γ`-invariant, then in particular it's `Γ'`-invariant. Cusps of `Γ'`
are also cusps of `Γ` (by `IsCusp.mono`), so boundedness at cusps transfers. -/
def restrictSubgroup {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} (h : Γ' ≤ Γ) (f : ModularForm Γ k) :
    ModularForm Γ' k where
  toFun := f.toFun
  slash_action_eq' γ hγ := f.slash_action_eq' γ (h hγ)
  holo' := f.holo'
  bdd_at_cusps' hc := f.bdd_at_cusps' (hc.mono h)

@[simp]
lemma coe_restrictSubgroup {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} (h : Γ' ≤ Γ) (f : ModularForm Γ k) :
    ⇑(ModularForm.restrictSubgroup h f) = ⇑f := rfl

end ModularForm

namespace CuspForm

variable {k : ℤ}

/-- Restrict a cusp form along a subgroup inclusion `Γ' ≤ Γ`.

If `f` is `Γ`-invariant, then in particular it's `Γ'`-invariant. Cusps of `Γ'` are
also cusps of `Γ` (by `IsCusp.mono`), so cusp-vanishing transfers. -/
def restrictSubgroup {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} (h : Γ' ≤ Γ) (f : CuspForm Γ k) :
    CuspForm Γ' k where
  toFun := f.toFun
  slash_action_eq' γ hγ := f.slash_action_eq' γ (h hγ)
  holo' := f.holo'
  zero_at_cusps' hc := f.zero_at_cusps' (hc.mono h)

end CuspForm

namespace HeckeRing.GL2

open CongruenceSubgroup Matrix.SpecialLinearGroup CuspForm
open scoped MatrixGroups ModularForm Pointwise

variable {N : ℕ} [NeZero N] {k : ℤ}

/-- The conjugation inclusion `(Γ₁(d*M)).map (mapGL ℝ) ≤ α_d⁻¹ ((Γ₁(M)).map (mapGL ℝ)) α_d`.

This is the key inclusion that lets us restrict the translated cusp form. -/
lemma Gamma1_dmul_le_conj (M : ℕ) [NeZero M] (d : ℕ) [NeZero d] :
    (Gamma1 (d * M)).map (mapGL ℝ) ≤
      ConjAct.toConjAct (levelRaiseMatrix d)⁻¹ • (Gamma1 M).map (mapGL ℝ) := by
  intro g hg
  obtain ⟨γ, hγ_mem, rfl⟩ := Subgroup.mem_map.mp hg
  rw [Subgroup.mem_smul_pointwise_iff_exists]
  refine ⟨mapGL ℝ (levelRaiseConj d M γ hγ_mem),
    Subgroup.mem_map.mpr ⟨_, levelRaiseConj_mem_Gamma1 d M γ hγ_mem, rfl⟩, ?_⟩
  rw [ConjAct.toConjAct_smul, inv_inv, mul_assoc, inv_mul_eq_iff_eq_mul]
  exact levelRaiseMatrix_mul_mapGL d γ (Gamma1_dmul_lower_left_dvd d M γ hγ_mem)

/-- The level-raising operator `ι_d : S_k(Γ₁(M)) → S_k(Γ₁(d*M))`, defined as
`(ι_d f)(τ) = f(d·τ)`, equivalently `d^{1-k} · (f ∣[k] [[d,0],[0,1]])`
(DS (5.16); Miyake §4.6 Lemma 4.6.1). -/
def levelRaise (M : ℕ) [NeZero M] (d : ℕ) [NeZero d] (k : ℤ) :
    CuspForm ((Gamma1 M).map (mapGL ℝ)) k →ₗ[ℂ]
    CuspForm ((Gamma1 (d * M)).map (mapGL ℝ)) k where
  toFun f :=
    ((d : ℂ) ^ (1 - k)) •
      (CuspForm.translate f (levelRaiseMatrix d)).restrictSubgroup (Gamma1_dmul_le_conj M d)
  map_add' f₁ f₂ := by
    ext z
    change ((d : ℂ) ^ (1 - k)) • ((⇑(f₁ + f₂) ∣[k] levelRaiseMatrix d) z) =
      ((d : ℂ) ^ (1 - k)) • ((⇑f₁ ∣[k] levelRaiseMatrix d) z) +
      ((d : ℂ) ^ (1 - k)) • ((⇑f₂ ∣[k] levelRaiseMatrix d) z)
    simp only [CuspForm.coe_add, SlashAction.add_slash, Pi.add_apply, smul_add]
  map_smul' c f := by
    ext z
    change ((d : ℂ) ^ (1 - k)) • ((⇑(c • f) ∣[k] levelRaiseMatrix d) z) =
      c • (((d : ℂ) ^ (1 - k)) • ((⇑f ∣[k] levelRaiseMatrix d) z))
    simp only [show (⇑(c • f) : UpperHalfPlane → ℂ) = c • ⇑f from rfl,
      ModularForm.smul_slash, σ_levelRaiseMatrix d, ContinuousAlgEquiv.refl_apply,
      Pi.smul_apply, smul_eq_mul]
    ring

/-- The `ModularForm` analogue of `levelRaise`:
`ι_d : M_k(Γ₁(M)) → M_k(Γ₁(d*M))`, sending `f ↦ d^{1-k} · (f ∣[k] α_d)` where
`α_d = [[d, 0], [0, 1]]`. The pointwise formula `(ι_d f)(τ) = f(d·τ)` is provided
by `modularFormLevelRaise_apply`. -/
def modularFormLevelRaise (M : ℕ) [NeZero M] (d : ℕ) [NeZero d] (k : ℤ) :
    ModularForm ((Gamma1 M).map (mapGL ℝ)) k →ₗ[ℂ]
    ModularForm ((Gamma1 (d * M)).map (mapGL ℝ)) k where
  toFun f :=
    ((d : ℂ) ^ (1 - k)) •
      (ModularForm.translate f (levelRaiseMatrix d)).restrictSubgroup
        (Gamma1_dmul_le_conj M d)
  map_add' f₁ f₂ := by
    ext z
    change ((d : ℂ) ^ (1 - k)) • ((⇑(f₁ + f₂) ∣[k] levelRaiseMatrix d) z) =
      ((d : ℂ) ^ (1 - k)) • ((⇑f₁ ∣[k] levelRaiseMatrix d) z) +
      ((d : ℂ) ^ (1 - k)) • ((⇑f₂ ∣[k] levelRaiseMatrix d) z)
    simp only [ModularForm.coe_add, SlashAction.add_slash, Pi.add_apply, smul_add]
  map_smul' c f := by
    ext z
    change ((d : ℂ) ^ (1 - k)) • ((⇑(c • f) ∣[k] levelRaiseMatrix d) z) =
      c • (((d : ℂ) ^ (1 - k)) • ((⇑f ∣[k] levelRaiseMatrix d) z))
    simp only [show (⇑(c • f) : UpperHalfPlane → ℂ) = c • ⇑f from rfl,
      ModularForm.smul_slash, σ_levelRaiseMatrix d, ContinuousAlgEquiv.refl_apply,
      Pi.smul_apply, smul_eq_mul]
    ring

/-- **Coercion of `modularFormLevelRaise` to `UpperHalfPlane → ℂ`.**

`⇑(modularFormLevelRaise M d k f) = d^{1-k} · (⇑f ∣[k] α_d) = levelRaiseFun d k ⇑f`. -/
@[simp]
lemma coe_modularFormLevelRaise (M : ℕ) [NeZero M] (d : ℕ) [NeZero d] (k : ℤ)
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k) :
    ⇑(modularFormLevelRaise M d k f) = levelRaiseFun d k ⇑f :=
  rfl

/-- **Down-conjugation bridge.** For `γ : SL(2, ℤ)` with `l ∣ γ.val 1 0` and
`γ̃ := levelRaiseConjOfDvd l γ hdvd = α_l γ α_l⁻¹`, the slash action by
`mapGL ℝ γ` on `levelRaiseFun l k f` equals the level-raise of the slash
action by `mapGL ℝ γ̃` on `f`. This is the slash-action incarnation of
`levelRaiseMatrix_mul_mapGL`. -/
lemma slash_mapGL_levelRaiseFun (l : ℕ) [NeZero l] (k : ℤ) (γ : SL(2, ℤ))
    (hdvd : (l : ℤ) ∣ γ.val 1 0) (f : UpperHalfPlane → ℂ) :
    levelRaiseFun l k f ∣[k] (mapGL ℝ γ : GL (Fin 2) ℝ) =
      levelRaiseFun l k
        (f ∣[k] (mapGL ℝ (levelRaiseConjOfDvd l γ hdvd) : GL (Fin 2) ℝ)) := by
  have hσγ : UpperHalfPlane.σ (mapGL ℝ γ : GL (Fin 2) ℝ) = ContinuousAlgEquiv.refl ℝ ℂ := by
    unfold UpperHalfPlane.σ
    rw [if_pos (show (0 : ℝ) < (Matrix.GeneralLinearGroup.det (mapGL ℝ γ)).val by
      rw [Matrix.SpecialLinearGroup.det_mapGL]; norm_num)]
  change ((l : ℂ) ^ (1 - k) • (f ∣[k] levelRaiseMatrix l)) ∣[k]
      (mapGL ℝ γ : GL (Fin 2) ℝ) = _
  rw [ModularForm.smul_slash, hσγ, ContinuousAlgEquiv.refl_apply, ← SlashAction.slash_mul,
    ← levelRaiseMatrix_mul_mapGL l γ hdvd, SlashAction.slash_mul]
  rfl

/-- **Pointwise evaluation of the level-raise operator.** `levelRaiseFun l k f`
evaluates to `f` at the scaled point `α_l • τ`; the `l^{1-k}` prefactor exactly
cancels the `l^{k-1}` factor from the slash action. -/
lemma levelRaiseFun_apply (l : ℕ) [NeZero l] (k : ℤ) (f : UpperHalfPlane → ℂ) (τ : UpperHalfPlane) :
    levelRaiseFun l k f τ = f ((levelRaiseMatrix l) • τ) := by
  change ((l : ℂ) ^ (1 - k)) • ((f ∣[k] levelRaiseMatrix l) τ) = _
  rw [ModularForm.slash_apply, σ_levelRaiseMatrix, ContinuousAlgEquiv.refl_apply,
    abs_levelRaiseMatrix_det_val, denom_levelRaiseMatrix, one_zpow, mul_one,
    smul_eq_mul, Complex.ofReal_natCast, mul_comm (f _), ← mul_assoc,
    ← zpow_add₀ (Nat.cast_ne_zero.mpr (NeZero.ne l))]
  norm_num

/-- The action of `levelRaiseMatrix l = [[l, 0], [0, 1]]` on `ℍ` is the diagonal
scaling `(α_l • τ : ℂ) = l · (↑τ : ℂ)`. -/
lemma coe_levelRaiseMatrix_smul (l : ℕ) [NeZero l] (τ : UpperHalfPlane) :
    ((levelRaiseMatrix l • τ : UpperHalfPlane) : ℂ) = (l : ℂ) * (↑τ : ℂ) := by
  rw [UpperHalfPlane.coe_smul_of_det_pos (levelRaiseMatrix_det_pos l)]
  simp [UpperHalfPlane.num, UpperHalfPlane.denom, levelRaiseMatrix,
    Matrix.GeneralLinearGroup.mkOfDetNeZero]

/-- **Pointwise evaluation** of the `ModularForm` level-raising operator:
`(modularFormLevelRaise M d k f) τ = f (α_d • τ)`, where `α_d` acts as
`τ ↦ d · τ` on `ℍ`. -/
lemma modularFormLevelRaise_apply (M : ℕ) [NeZero M] (d : ℕ) [NeZero d] (k : ℤ)
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k) (τ : UpperHalfPlane) :
    modularFormLevelRaise M d k f τ = f ((levelRaiseMatrix d) • τ) :=
  levelRaiseFun_apply d k (⇑f) τ


end HeckeRing.GL2

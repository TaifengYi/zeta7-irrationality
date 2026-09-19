import Zeta7Proof.Radius49HOFricke
import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing

/-! Radius internalization, HO: level-one forms of weight `k ≡ 4 (mod 6)` are rational
polynomials in `E₄, E₆` (at the level of `q`-expansions).

`span_of_qExpansion`: if `f ∈ M_k(SL₂ℤ)` (`k ≡ 4 mod 6`) has rational `q`-expansion `F`, then
`F ∈ span_ℚ {E₄^a E₆^b : 4a + 6b = k}`. Proof: subtract `c E₄ E₆^b` (`c` the constant term); the
difference is a cusp form, zero if `k < 12` and `Δ · g` otherwise, where `g` has rational
expansion (division by `Δ = q + …` over `ℚ`), and induct. No published radius input is used. -/

noncomputable section
set_option autoImplicit false
open ModularForm UpperHalfPlane PowerSeries
open scoped MatrixGroups
namespace Zeta7Radius49
open Zeta7LevelSeven

/-- The rational `q`-expansions of `E₄`, `E₆`. -/
abbrev E4Q : ℚ⟦X⟧ := Zeta7Common.eisensteinFourQ
abbrev E6Q : ℚ⟦X⟧ := Zeta7Common.eisensteinSixQ

theorem E4_qexp : qExpansion 1 classicalE4 = E4Q.map (algebraMap ℚ ℂ) :=
  Zeta7Common.eisensteinFourQ_classical.symm

theorem E6_qexp : qExpansion 1 classicalE6 = E6Q.map (algebraMap ℚ ℂ) :=
  Zeta7Common.eisensteinSixQ_classical.symm

theorem E4Q_const : constantCoeff E4Q = 1 := by
  simp [E4Q, Zeta7Common.eisensteinFourQ, Zeta7Common.sigmaThree]

theorem E6Q_const : constantCoeff E6Q = 1 := by
  simp [E6Q, Zeta7Common.eisensteinSixQ, Zeta7Common.sigmaFive]

/-- The monomials of weight `k`. -/
def monoSet (k : ℕ) : Set ℚ⟦X⟧ := {f | ∃ a b : ℕ, 4 * a + 6 * b = k ∧ f = E4Q ^ a * E6Q ^ b}

/-- `E₄^a E₆^b` as a level-one form. -/
def mono (a b : ℕ) : ModularForm 𝒮ℒ ((4 * a + 6 * b : ℕ) : ℤ) :=
  mcast (by push_cast; ring) ((classicalE4.pow a).mul (classicalE6.pow b))

theorem mono_qexp (a b : ℕ) :
    qExpansion 1 (mono a b) = (E4Q ^ a * E6Q ^ b).map (algebraMap ℚ ℂ) := by
  rw [mono, coe_mcast, ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL, E4_qexp, E6_qexp,
    map_mul, map_pow, map_pow]

/-- `Δ` over `ℚ`. -/
def DeltaQ : ℚ⟦X⟧ := C (1 / 1728 : ℚ) * (E4Q ^ 3 - E6Q ^ 2)

theorem Delta_qexp : qExpansion 1 discriminant = DeltaQ.map (algebraMap ℚ ℂ) := by
  let D : ModularForm 𝒮ℒ 12 := (1 / 1728 : ℂ) •
    (mcast (by decide) (classicalE4.pow 3) - mcast (by decide) (classicalE6.pow 2))
  have hD : (D : ℍ → ℂ) = discriminant := by
    funext z
    rw [discriminant_eq_E₄_cube_sub_E₆_sq]
    simp only [D, FunLike.coe_smul, FunLike.coe_sub, coe_mcast, ModularForm.coe_pow,
      Pi.smul_apply, Pi.sub_apply, Pi.pow_apply, smul_eq_mul]
    have e4 : classicalE4 z = E₄ z := rfl
    have e6 : classicalE6 z = E₆ z := rfl
    rw [e4, e6]; ring
  rw [← hD]
  rw [show (D : ℍ → ℂ) = (1 / 1728 : ℂ) • ⇑(mcast (by decide) (classicalE4.pow 3) -
      mcast (by decide) (classicalE6.pow 2) : ModularForm 𝒮ℒ 12) from rfl]
  rw [ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL, FunLike.coe_sub,
    ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL, coe_mcast, coe_mcast,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL, E4_qexp, E6_qexp]
  ext n
  simp [DeltaQ, coeff_C_mul, map_sub, map_pow]

theorem map_rat_injective : Function.Injective (PowerSeries.map (algebraMap ℚ ℂ)) := by
  intro f g hfg
  ext n
  have := congrArg (coeff n) hfg
  simp only [coeff_map] at this
  exact (algebraMap ℚ ℂ).injective this

theorem Delta_span {k : ℕ} {G : ℚ⟦X⟧} (hG : G ∈ Submodule.span ℚ (monoSet k)) :
    DeltaQ * G ∈ Submodule.span ℚ (monoSet (k + 12)) := by
  induction hG using Submodule.span_induction with
  | mem s hs =>
    obtain ⟨a, b, hab, rfl⟩ := hs
    have h1 : E4Q ^ (a + 3) * E6Q ^ b ∈ Submodule.span ℚ (monoSet (k + 12)) :=
      Submodule.subset_span ⟨a + 3, b, by omega, rfl⟩
    have h2 : E4Q ^ a * E6Q ^ (b + 2) ∈ Submodule.span ℚ (monoSet (k + 12)) :=
      Submodule.subset_span ⟨a, b + 2, by omega, rfl⟩
    have heq : DeltaQ * (E4Q ^ a * E6Q ^ b) =
        (1 / 1728 : ℚ) • (E4Q ^ (a + 3) * E6Q ^ b - E4Q ^ a * E6Q ^ (b + 2)) := by
      rw [DeltaQ, smul_eq_C_mul]; ring
    rw [heq]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _ h1 h2)
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hx

/-- Division of a series with zero constant term by `Δ = X · U` over `ℚ`. -/
theorem rational_quotient (F : ℚ⟦X⟧) (hF : constantCoeff F = 0) (g : ℂ⟦X⟧)
    (h : F.map (algebraMap ℚ ℂ) = DeltaQ.map (algebraMap ℚ ℂ) * g) :
    ∃ G : ℚ⟦X⟧, g = G.map (algebraMap ℚ ℂ) ∧ F = DeltaQ * G := by
  have hD1 : coeff 1 DeltaQ = 1 := by
    have h1 := congrArg (coeff 1) Delta_qexp
    rw [discriminant_qExpansion_coeff_one, coeff_map] at h1
    exact (algebraMap ℚ ℂ).injective (h1.symm.trans (map_one _).symm)
  have hD0 : constantCoeff DeltaQ = 0 := by
    have h0 := congrArg (coeff 0) Delta_qexp
    have hz := CuspFormClass.qExpansion_coeff_zero CuspForm.discriminant one_pos
      one_mem_strictPeriods_SL
    rw [CuspForm.coe_discriminant] at hz
    rw [hz, coeff_map, coeff_zero_eq_constantCoeff_apply] at h0
    exact (algebraMap ℚ ℂ).injective (h0.symm.trans (map_zero _).symm)
  obtain ⟨U, hU⟩ := X_dvd_iff.mpr hD0
  obtain ⟨R, hR⟩ := X_dvd_iff.mpr hF
  have hU0 : constantCoeff U = 1 := by
    have := congrArg (coeff 1) hU
    rw [coeff_succ_X_mul, hD1] at this
    rw [← coeff_zero_eq_constantCoeff_apply]; exact this.symm
  refine ⟨R * U⁻¹, ?_, ?_⟩
  · rw [hU, hR, map_mul, map_mul, map_X, mul_assoc] at h
    have h' : R.map (algebraMap ℚ ℂ) = U.map (algebraMap ℚ ℂ) * g :=
      mul_left_cancel₀ X_ne_zero h
    have hinv : U.map (algebraMap ℚ ℂ) * (U⁻¹).map (algebraMap ℚ ℂ) = 1 := by
      rw [← map_mul, PowerSeries.mul_inv_cancel _ (by rw [hU0]; exact one_ne_zero), map_one]
    rw [map_mul, h']
    calc g = (U.map (algebraMap ℚ ℂ) * (U⁻¹).map (algebraMap ℚ ℂ)) * g := by rw [hinv, one_mul]
      _ = U.map (algebraMap ℚ ℂ) * g * (U⁻¹).map (algebraMap ℚ ℂ) := by ring
  · rw [hR, hU, mul_assoc, ← mul_assoc U, mul_comm U R, mul_assoc,
      PowerSeries.mul_inv_cancel _ (by rw [hU0]; exact one_ne_zero), mul_one]

/-- **Generation.** -/
theorem span_of_qExpansion (k : ℕ) (hk : k % 6 = 4) (f : ModularForm 𝒮ℒ (k : ℤ)) (F : ℚ⟦X⟧)
    (hF : qExpansion 1 f = F.map (algebraMap ℚ ℂ)) : F ∈ Submodule.span ℚ (monoSet k) := by
  induction k using Nat.strong_induction_on generalizing F with
  | _ k ih =>
    obtain ⟨b, rfl⟩ : ∃ b, k = 4 * 1 + 6 * b := ⟨(k - 4) / 6, by omega⟩
    set c : ℚ := coeff 0 F
    set f' : ModularForm 𝒮ℒ ((4 * 1 + 6 * b : ℕ) : ℤ) := f - (c : ℂ) • mono 1 b
    have hqf' : qExpansion 1 f' = (F - C c * (E4Q * E6Q ^ b)).map (algebraMap ℚ ℂ) := by
      rw [show (f' : ℍ → ℂ) = ⇑f - ⇑((c : ℂ) • mono 1 b) from rfl,
        ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL, FunLike.coe_smul,
        ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL, hF, mono_qexp]
      ext n; simp [coeff_C_mul, map_sub, coeff_smul]
    have hc0 : constantCoeff (F - C c * (E4Q * E6Q ^ b)) = 0 := by
      simp [c, E4Q_const, E6Q_const, coeff_zero_eq_constantCoeff_apply]
    have h0 : (qExpansion 1 f').coeff 0 = 0 := by
      rw [hqf', coeff_map, coeff_zero_eq_constantCoeff_apply, hc0, map_zero]
    have hmono : C c * (E4Q * E6Q ^ b) ∈ Submodule.span ℚ (monoSet (4 * 1 + 6 * b)) := by
      rw [← smul_eq_C_mul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, b, rfl, by ring⟩)
    have hsplit : F = C c * (E4Q * E6Q ^ b) + (F - C c * (E4Q * E6Q ^ b)) := by ring
    by_cases hsmall : 4 * 1 + 6 * b < 12
    · -- the difference is a cusp form of weight `< 12`, hence zero
      have hz : ModularForm.toCuspForm f' h0 = 0 := by
        have hr := CuspForm.rank_eq_zero_of_weight_lt_twelve
          (k := ((4 * 1 + 6 * b : ℕ) : ℤ)) (by exact_mod_cast hsmall)
        exact (rank_zero_iff_forall_zero.mp hr) _
      have hq0 : qExpansion 1 f' = 0 := by
        have hfun : (f' : ℍ → ℂ) = 0 := by
          funext z
          have := congrArg (fun g : CuspForm 𝒮ℒ _ => g z) hz
          simpa using this
        rw [hfun]
        exact qExpansion_zero 1
      have hdiff : F - C c * (E4Q * E6Q ^ b) = 0 := by
        apply map_rat_injective
        rw [← hqf', hq0, map_zero]
      rw [hsplit, hdiff, add_zero]
      exact hmono
    · -- divide by `Δ`
      obtain ⟨b', hb'⟩ : ∃ b', b = b' + 2 := ⟨b - 2, by omega⟩
      set g := CuspForm.discriminantEquiv (ModularForm.toCuspForm f' h0)
      have hmul := ModularForm.qExpansion_eq_qExpansion_discriminant_mul f' h0
      rw [hqf', Delta_qexp] at hmul
      obtain ⟨G, hGg, hGF⟩ := rational_quotient _ hc0 _ hmul
      let g' : ModularForm 𝒮ℒ ((4 * 1 + 6 * b' : ℕ) : ℤ) := mcast (by subst hb'; push_cast; ring) g
      have hg' : qExpansion 1 g' = G.map (algebraMap ℚ ℂ) := by
        rw [coe_mcast]; exact hGg
      have hGspan := ih (4 * 1 + 6 * b') (by omega) (by omega) g' G hg'
      have hΔ := Delta_span hGspan
      rw [show 4 * 1 + 6 * b' + 12 = 4 * 1 + 6 * b by omega] at hΔ
      rw [hsplit, hGF]
      exact Submodule.add_mem _ hmono hΔ

end Zeta7Radius49

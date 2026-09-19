import Zeta7Proof.ValenceQDisc

/-! Translation cosets `Γ_∞ \ Γ₀(7)` and their lower rows.

* `eq_T_mul_of_bottom`: two elements of `SL(2, ℤ)` with the same lower row differ by `Tᵏ` on the left;
  hence `qParam_eq_of_bottom`: they give the same point `e^{2πiγτ}` of the q-disc.
* `normSL`: changing the sign so that the lower row `(c, d)` has `c > 0`, or `c = 0, d > 0`.
* `bottomShape p`: `p = (0, 1)`, or `p = (c, d)` with `c > 0`, `7 ∣ c`, `c, d` coprime.
  `bottomShape_of_Gamma0` shows every normalised element of `Γ₀(7)` has such a lower row, and
  `exists_rep` gives a representative for every such row.
* `im_smul_horPt`: `Im(γ(u + iy)) = y / ((cu + d)² + c² y²)`. -/
noncomputable section
set_option autoImplicit false
namespace Zeta7Valence
open Complex Zeta7LevelSeven Matrix Matrix.SpecialLinearGroup
open UpperHalfPlane hiding I
open scoped MatrixGroups

theorem qParam_T_zpow_smul (k : ℤ) (τ : ℍ) :
    Function.Periodic.qParam 1 ((ModularGroup.T ^ k • τ : ℍ) : ℂ) =
      Function.Periodic.qParam 1 τ := by
  rw [ModularGroup.coe_T_zpow_smul_eq]
  unfold Function.Periodic.qParam
  rw [show 2 * (Real.pi : ℂ) * I * ((τ : ℂ) + k) / ((1 : ℝ) : ℂ) =
      2 * Real.pi * I * τ / ((1 : ℝ) : ℂ) + k * (2 * Real.pi * I) by push_cast; ring,
    Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem eq_T_mul_of_bottom {γ γ' : SL(2, ℤ)} (hc : γ' 1 0 = γ 1 0) (hd : γ' 1 1 = γ 1 1) :
    ∃ k : ℤ, γ' = ModularGroup.T ^ k * γ := by
  set δ := γ' * γ⁻¹ with hδ
  have hdetγ : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.2; rw [Matrix.det_fin_two] at this; exact this
  have e10 : δ 1 0 = 0 := by
    simp [hδ, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.mul_apply,
      Fin.sum_univ_two, hc, hd]
    ring
  have e11 : δ 1 1 = 1 := by
    simp [hδ, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.mul_apply,
      Fin.sum_univ_two, hc, hd]
    linear_combination hdetγ
  have e00 : δ 0 0 = 1 := by
    have := δ.2
    rw [Matrix.det_fin_two, e10, e11] at this
    simpa using this
  refine ⟨δ 0 1, ?_⟩
  have hδT : δ = ModularGroup.T ^ (δ 0 1) := by
    ext i j
    rw [ModularGroup.coe_T_zpow]
    fin_cases i <;> fin_cases j <;> simp [e00, e10, e11]
  rw [← hδT, hδ, inv_mul_cancel_right]

theorem qParam_eq_of_bottom {γ γ' : SL(2, ℤ)} (hc : γ' 1 0 = γ 1 0) (hd : γ' 1 1 = γ 1 1)
    (τ : ℍ) : Function.Periodic.qParam 1 ((γ' • τ : ℍ) : ℂ) =
      Function.Periodic.qParam 1 ((γ • τ : ℍ) : ℂ) := by
  obtain ⟨k, hk⟩ := eq_T_mul_of_bottom hc hd
  rw [hk, mul_smul, qParam_T_zpow_smul]

/-! ### Normalised lower rows -/

/-- Sign normalisation of the lower row. -/
def normSL (γ : SL(2, ℤ)) : SL(2, ℤ) :=
  if 0 < γ 1 0 ∨ (γ 1 0 = 0 ∧ 0 < γ 1 1) then γ else -γ

theorem normSL_smul (γ : SL(2, ℤ)) (τ : ℍ) : normSL γ • τ = γ • τ := by
  unfold normSL
  split_ifs
  · rfl
  · exact ModularGroup.SL_neg_smul γ τ

theorem neg_mem_Gamma0 {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma0 7) :
    -γ ∈ CongruenceSubgroup.Gamma0 7 := by
  rw [CongruenceSubgroup.Gamma0_mem] at hγ ⊢
  simp [Matrix.SpecialLinearGroup.coe_neg, hγ]

theorem normSL_mem {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma0 7) :
    normSL γ ∈ CongruenceSubgroup.Gamma0 7 := by
  unfold normSL
  split_ifs
  · exact hγ
  · exact neg_mem_Gamma0 hγ

/-- Admissible lower rows. -/
def bottomShape (p : ℤ × ℤ) : Prop :=
  (p.1 = 0 ∧ p.2 = 1) ∨ (0 < p.1 ∧ (7 : ℤ) ∣ p.1 ∧ IsCoprime p.1 p.2)

instance (p : ℤ × ℤ) : Decidable (bottomShape p) := by unfold bottomShape; infer_instance

theorem bottomShape_of_Gamma0 {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma0 7) :
    bottomShape ((normSL γ) 1 0, (normSL γ) 1 1) := by
  set g := normSL γ with hg
  have hg7 : g ∈ CongruenceSubgroup.Gamma0 7 := normSL_mem hγ
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    have := g.2; rw [Matrix.det_fin_two] at this; exact this
  have h7 : (7 : ℤ) ∣ g 1 0 := by
    rw [CongruenceSubgroup.Gamma0_mem] at hg7
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).mp (by exact_mod_cast hg7)
  have hsign : 0 < g 1 0 ∨ (g 1 0 = 0 ∧ 0 < g 1 1) := by
    rw [hg]; unfold normSL
    split_ifs with h
    · exact h
    · push Not at h
      simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply]
      rcases lt_trichotomy (γ 1 0) 0 with h1 | h1 | h1
      · left; linarith
      · right
        refine ⟨by rw [h1]; simp, ?_⟩
        have hd := h.2 h1
        have hdet' : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
          have := γ.2; rw [Matrix.det_fin_two] at this; exact this
        rw [h1, mul_zero, sub_zero] at hdet'
        rcases hd.lt_or_eq with hd | hd
        · linarith
        · rw [hd, mul_zero] at hdet'; exact absurd hdet' (by norm_num)
      · exact absurd h1 (not_lt.mpr h.1)
  rcases hsign with hc | ⟨hc, hd⟩
  · exact Or.inr ⟨hc, h7, ⟨-(g 0 1), g 0 0, by linear_combination hdet⟩⟩
  · left
    refine ⟨hc, ?_⟩
    rw [hc, mul_zero, sub_zero] at hdet
    have := Int.eq_one_or_neg_one_of_mul_eq_one' hdet
    rcases this with ⟨_, h1⟩ | ⟨_, h1⟩
    · exact h1
    · rw [h1] at hd; norm_num at hd

theorem exists_rep {p : ℤ × ℤ} (hp : bottomShape p) :
    ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 7 ∧ γ 1 0 = p.1 ∧ γ 1 1 = p.2 := by
  rcases hp with ⟨h1, h2⟩ | ⟨_, h7, u, v, huv⟩
  · exact ⟨1, one_mem _, by simp [h1], by simp [h2]⟩
  · let γ : SL(2, ℤ) := ⟨!![v, -u; p.1, p.2], by
      rw [Matrix.det_fin_two_of]; linear_combination huv⟩
    refine ⟨γ, ?_, by simp [γ], by simp [γ]⟩
    rw [CongruenceSubgroup.Gamma0_mem]
    simp only [γ]
    simp
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).mpr h7

/-! ### Imaginary parts -/

theorem im_smul_horPt {y : ℝ} (hy : 0 < y) (u : ℝ) (γ : SL(2, ℤ)) :
    (γ • horPt hy u).im = y / (((γ 1 0 : ℝ) * u + γ 1 1) ^ 2 + (γ 1 0 : ℝ) ^ 2 * y ^ 2) := by
  rw [ModularGroup.im_smul_eq_div_normSq, ModularGroup.denom_apply]
  have him : (horPt hy u).im = y := by simp [horPt, UpperHalfPlane.im]
  rw [him]
  congr 1
  simp [horPt, Complex.normSq_apply, UpperHalfPlane.coe_mk]
  ring

end Zeta7Valence

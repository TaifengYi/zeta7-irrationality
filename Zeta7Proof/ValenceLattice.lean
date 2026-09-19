import Zeta7Proof.ValenceWeierstrass
import Zeta7Proof.LevelSevenFunctionIdentities

/-! From equal values of the modular coordinate to an `SL(2, ℤ)` relation.

* `tauPair τ` is the period pair `(τ, 1)`, `scalePair c L` is `c L`.
* `G_tauPair`: `G_k(ℤτ + ℤ) = 2 ζ(k) E_k(τ)`, from Mathlib's
  `tsum_eisSummand_eq_riemannZeta_mul_eisensteinSeries`.
* `G_scalePair`: `G_k(cL) = c^{-k} G_k(L)`.
* `sl2_of_lattice_eq`: `ℤτ₁ + ℤ = c(ℤτ₂ + ℤ)` implies `τ₁ = γ τ₂` for some `γ ∈ SL(2, ℤ)`.
* `sl2_of_E`: `E₄(τ₁) = μ⁴ E₄(τ₂)`, `E₆(τ₁) = μ⁶ E₆(τ₂)`, `μ ≠ 0` give `τ₁ = γ τ₂` (by
  `lattice_eq_of_g`, the uniqueness of `℘` from `g₂, g₃`).
* `sl2_of_x_eq`: `x(τ₁) = x(τ₂)` and `P(x(τ₂)) ≠ 0` give `τ₁ = γ τ₂`, using
  `E₄ P(x) = A² N(x)`, `E₆ P(x)² = A³ T(x)` and `Δ = (E₄³ - E₆²)/1728 ≠ 0`. -/
noncomputable section
set_option autoImplicit false
namespace Zeta7Valence
open UpperHalfPlane PeriodPair Zeta7LevelSeven
open scoped MatrixGroups

/-- The period pair `(τ, 1)`. -/
def tauPair (τ : ℍ) : PeriodPair where
  ω₁ := τ
  ω₂ := 1
  indep := by
    rw [LinearIndependent.pair_iff]
    intro s t h
    have him := congrArg Complex.im h
    simp only [Complex.add_im, Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero, Complex.one_im, mul_zero, Complex.zero_im] at him
    have hs : s = 0 := (mul_eq_zero.mp him).resolve_right τ.im_pos.ne'
    subst hs
    simp only [zero_smul, zero_add, Complex.real_smul, mul_one] at h
    exact ⟨rfl, by exact_mod_cast h⟩

/-- The period pair `c L`. -/
def scalePair (c : ℂ) (hc : c ≠ 0) (L : PeriodPair) : PeriodPair where
  ω₁ := c * L.ω₁
  ω₂ := c * L.ω₂
  indep := by
    rw [LinearIndependent.pair_iff]
    intro s t h
    have h' : c * (s • L.ω₁ + t • L.ω₂) = 0 := by
      rw [← h]; simp only [Complex.real_smul]; ring
    exact (LinearIndependent.pair_iff.mp L.indep) s t ((mul_eq_zero.mp h').resolve_left hc)

theorem G_eq_tsum (L : PeriodPair) (k : ℕ) :
    L.G k = ∑' x : ℤ × ℤ, ((x.1 * L.ω₁ + x.2 * L.ω₂) ^ k)⁻¹ := by
  rw [PeriodPair.G, ← L.latticeEquivProd.symm.toEquiv.tsum_eq]
  congr 1
  funext x
  simp only [LinearEquiv.coe_toEquiv, latticeEquiv_symm_apply]

theorem G_scalePair (c : ℂ) (hc : c ≠ 0) (L : PeriodPair) (k : ℕ) :
    (scalePair c hc L).G k = (c ^ k)⁻¹ * L.G k := by
  rw [G_eq_tsum, G_eq_tsum, ← tsum_mul_left]
  congr 1
  funext x
  change ((x.1 * (c * L.ω₁) + x.2 * (c * L.ω₂)) ^ k)⁻¹ = _
  rw [show (x.1 : ℂ) * (c * L.ω₁) + x.2 * (c * L.ω₂) = c * (x.1 * L.ω₁ + x.2 * L.ω₂) by ring,
    mul_pow, mul_inv]

theorem eisSummand_sum_eq (τ : ℍ) (k : ℕ) :
    (tauPair τ).G k = ∑' v : Fin 2 → ℤ, EisensteinSeries.eisSummand k v τ := by
  rw [G_eq_tsum, ← (finTwoArrowEquiv ℤ).tsum_eq]
  congr 1
  funext v
  simp [EisensteinSeries.eisSummand, tauPair, zpow_neg, finTwoArrowEquiv, piFinTwoEquiv]

theorem E_apply (k : ℕ) (hk : 3 ≤ k) (τ : ℍ) :
    ModularForm.E hk τ = (1 / 2 : ℂ) * eisensteinSeries (N := 1) 0 k τ := rfl

/-- `G_k(ℤτ + ℤ) = 2 ζ(k) E_k(τ)`. -/
theorem G_tauPair (k : ℕ) (hk : 3 ≤ k) (τ : ℍ) :
    (tauPair τ).G k = 2 * riemannZeta k * ModularForm.E hk τ := by
  rw [eisSummand_sum_eq, tsum_eisSummand_eq_riemannZeta_mul_eisensteinSeries hk,
    E_apply]
  ring

/-! ### Homothetic lattices -/

theorem int_indep (τ : ℍ) {u v : ℤ} (h : (u : ℂ) * τ + v = 0) : u = 0 ∧ v = 0 := by
  have him := congrArg Complex.im h
  simp only [Complex.add_im, Complex.mul_im, Complex.intCast_re, Complex.intCast_im, zero_mul,
    add_zero, Complex.zero_im] at him
  have hu : (u : ℝ) = 0 := (mul_eq_zero.mp him).resolve_right τ.im_pos.ne'
  have hu' : u = 0 := by exact_mod_cast hu
  subst hu'
  simp only [Int.cast_zero, zero_mul, zero_add, Int.cast_eq_zero] at h
  exact ⟨rfl, h⟩

/-- **Homothetic lattices give an `SL(2, ℤ)` relation.** -/
theorem sl2_of_lattice_eq {τ₁ τ₂ : ℍ} {c : ℂ} (hc : c ≠ 0)
    (h : ((tauPair τ₁).lattice : Set ℂ) = (scalePair c hc (tauPair τ₂)).lattice) :
    ∃ γ : SL(2, ℤ), τ₁ = γ • τ₂ := by
  have mem1 : ∀ z : ℂ, z ∈ (tauPair τ₁).lattice ↔ z ∈ (scalePair c hc (tauPair τ₂)).lattice :=
    fun z => Set.ext_iff.mp h z
  obtain ⟨a, b, hab⟩ := mem_lattice.mp ((mem1 _).mp (tauPair τ₁).ω₁_mem_lattice)
  obtain ⟨e, f, hef⟩ := mem_lattice.mp ((mem1 _).mp (tauPair τ₁).ω₂_mem_lattice)
  obtain ⟨p, q, hpq⟩ := mem_lattice.mp ((mem1 _).mpr (scalePair c hc (tauPair τ₂)).ω₁_mem_lattice)
  obtain ⟨r, s, hrs⟩ := mem_lattice.mp ((mem1 _).mpr (scalePair c hc (tauPair τ₂)).ω₂_mem_lattice)
  change (a : ℂ) * (c * τ₂) + b * (c * 1) = τ₁ at hab
  change (e : ℂ) * (c * τ₂) + f * (c * 1) = 1 at hef
  change (p : ℂ) * τ₁ + q * 1 = c * τ₂ at hpq
  change (r : ℂ) * τ₁ + s * 1 = c * 1 at hrs
  -- the composite relations
  have k1 : ((p * a + q * e - 1 : ℤ) : ℂ) * τ₂ + ((p * b + q * f : ℤ) : ℂ) = 0 := by
    have : c * (((p * a + q * e - 1 : ℤ) : ℂ) * τ₂ + ((p * b + q * f : ℤ) : ℂ)) = 0 := by
      push_cast; linear_combination (p : ℂ) * hab + (q : ℂ) * hef + hpq
    exact (mul_eq_zero.mp this).resolve_left hc
  have k2 : ((r * a + s * e : ℤ) : ℂ) * τ₂ + ((r * b + s * f - 1 : ℤ) : ℂ) = 0 := by
    have : c * (((r * a + s * e : ℤ) : ℂ) * τ₂ + ((r * b + s * f - 1 : ℤ) : ℂ)) = 0 := by
      push_cast; linear_combination (r : ℂ) * hab + (s : ℂ) * hef + hrs
    exact (mul_eq_zero.mp this).resolve_left hc
  obtain ⟨k11, k12⟩ := int_indep τ₂ k1
  obtain ⟨k21, k22⟩ := int_indep τ₂ k2
  have hdet : (a * f - b * e) * (p * s - q * r) = 1 := by
    have e1 : p * a + q * e = 1 := by omega
    have e2 : p * b + q * f = 0 := by omega
    have e3 : r * a + s * e = 0 := by omega
    have e4 : r * b + s * f = 1 := by omega
    nlinarith [e1, e2, e3, e4]
  have hunit : a * f - b * e = 1 ∨ a * f - b * e = -1 := Int.eq_one_or_neg_one_of_mul_eq_one hdet
  -- `τ₁ = (a τ₂ + b)/(e τ₂ + f)`
  have hden : (e : ℂ) * τ₂ + f ≠ 0 := by
    intro h0
    have : c * ((e : ℂ) * τ₂ + f) = 1 := by linear_combination hef
    rw [h0, mul_zero] at this
    exact zero_ne_one this
  have hτ : (τ₁ : ℂ) = ((a : ℂ) * τ₂ + b) / ((e : ℂ) * τ₂ + f) := by
    have hcf : c = 1 / ((e : ℂ) * τ₂ + f) := by
      field_simp; linear_combination hef
    rw [← hab, hcf]; field_simp
  -- the determinant is `+1`
  have hpos : a * f - b * e = 1 := by
    rcases hunit with h1 | h1
    · exact h1
    · exfalso
      have him : (τ₁ : ℂ).im = ((a * f - b * e : ℤ) : ℝ) * (τ₂ : ℂ).im /
          Complex.normSq ((e : ℂ) * τ₂ + f) := by
        rw [hτ, Complex.div_im]
        simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
          Complex.intCast_re, Complex.intCast_im, zero_mul, sub_zero, add_zero, zero_add]
        push_cast
        field_simp
        ring
      rw [h1] at him
      have h1' := τ₁.im_pos
      have h2' := τ₂.im_pos
      have hn : 0 < Complex.normSq ((e : ℂ) * τ₂ + f) := Complex.normSq_pos.mpr hden
      change 0 < (τ₁ : ℂ).im at h1'
      rw [him] at h1'
      push_cast at h1'
      have : (-1 : ℝ) * (τ₂ : ℂ).im / Complex.normSq ((e : ℂ) * τ₂ + f) < 0 :=
        div_neg_of_neg_of_pos (by change -1 * τ₂.im < 0; linarith) hn
      linarith
  let γ : SL(2, ℤ) := ⟨!![a, b; e, f], by rw [Matrix.det_fin_two_of]; exact hpos⟩
  refine ⟨γ, ?_⟩
  apply UpperHalfPlane.ext
  rw [coe_specialLinearGroup_apply γ τ₂, hτ]
  simp [γ]

/-! ### Equal Eisenstein data give an `SL(2, ℤ)` relation -/

theorem g2_tauPair (τ : ℍ) : (tauPair τ).g₂ = 60 * (2 * riemannZeta 4 * classicalE4 τ) := by
  rw [PeriodPair.g₂, G_tauPair 4 (by norm_num)]
  rfl

theorem g3_tauPair (τ : ℍ) : (tauPair τ).g₃ = 140 * (2 * riemannZeta 6 * classicalE6 τ) := by
  rw [PeriodPair.g₃, G_tauPair 6 (by norm_num)]
  rfl

/-- **Proportional Eisenstein values give an `SL(2, ℤ)` relation.** -/
theorem sl2_of_E {τ₁ τ₂ : ℍ} {μ : ℂ} (hμ : μ ≠ 0)
    (h4 : classicalE4 τ₁ = μ ^ 4 * classicalE4 τ₂) (h6 : classicalE6 τ₁ = μ ^ 6 * classicalE6 τ₂) :
    ∃ γ : SL(2, ℤ), τ₁ = γ • τ₂ := by
  have hc : μ⁻¹ ≠ 0 := inv_ne_zero hμ
  have hg2 : (tauPair τ₁).g₂ = (scalePair μ⁻¹ hc (tauPair τ₂)).g₂ := by
    rw [PeriodPair.g₂, PeriodPair.g₂, G_scalePair, G_tauPair 4 (by norm_num),
      G_tauPair 4 (by norm_num)]
    change 60 * (2 * riemannZeta 4 * classicalE4 τ₁) =
      60 * (((μ⁻¹) ^ 4)⁻¹ * (2 * riemannZeta 4 * classicalE4 τ₂))
    rw [h4, inv_pow, inv_inv]; ring
  have hg3 : (tauPair τ₁).g₃ = (scalePair μ⁻¹ hc (tauPair τ₂)).g₃ := by
    rw [PeriodPair.g₃, PeriodPair.g₃, G_scalePair, G_tauPair 6 (by norm_num),
      G_tauPair 6 (by norm_num)]
    change 140 * (2 * riemannZeta 6 * classicalE6 τ₁) =
      140 * (((μ⁻¹) ^ 6)⁻¹ * (2 * riemannZeta 6 * classicalE6 τ₂))
    rw [h6, inv_pow, inv_inv]; ring
  exact sl2_of_lattice_eq hc (lattice_eq_of_g _ _ hg2 hg3)

theorem E4_cube_sub_E6_sq_ne (τ : ℍ) : classicalE4 τ ^ 3 - classicalE6 τ ^ 2 ≠ 0 := by
  have h := ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq τ
  have hne := ModularForm.discriminant_ne_zero τ
  intro h0
  apply hne
  rw [h]
  change (classicalE4 τ ^ 3 - classicalE6 τ ^ 2) / 1728 = 0
  rw [h0, zero_div]

theorem actualA_ne_zero {τ : ℍ} (hP : polyP (etaCoordinate τ) ≠ 0) : actualA τ ≠ 0 := by
  intro hA
  have h4 := E4_function τ
  have h6 := E6_function τ
  rw [hA] at h4 h6
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul] at h4 h6
  have e4 : classicalE4 τ = 0 := (mul_eq_zero.mp h4).resolve_right hP
  have e6 : classicalE6 τ = 0 := (mul_eq_zero.mp h6).resolve_right (pow_ne_zero 2 hP)
  exact E4_cube_sub_E6_sq_ne τ (by rw [e4, e6]; ring)

/-- **Equal coordinates give an `SL(2, ℤ)` relation** (off the finitely many values `P(x) = 0`). -/
theorem sl2_of_x_eq {τ₁ τ₂ : ℍ} (hx : etaCoordinate τ₁ = etaCoordinate τ₂)
    (hP : polyP (etaCoordinate τ₂) ≠ 0) : ∃ γ : SL(2, ℤ), τ₁ = γ • τ₂ := by
  have hP1 : polyP (etaCoordinate τ₁) ≠ 0 := by rw [hx]; exact hP
  have hA1 := actualA_ne_zero hP1
  have hA2 := actualA_ne_zero hP
  set μ : ℂ := (actualA τ₁ / actualA τ₂) ^ ((2 : ℕ)⁻¹ : ℂ) with hμdef
  have hμ2 : μ ^ 2 = actualA τ₁ / actualA τ₂ := Complex.cpow_nat_inv_pow _ (by norm_num)
  have hμ : μ ≠ 0 := by
    intro h0; rw [h0] at hμ2; simp at hμ2
    exact (div_ne_zero hA1 hA2) hμ2.symm
  refine sl2_of_E hμ ?_ ?_
  · have e1 := E4_function τ₁
    have e2 := E4_function τ₂
    rw [hx] at e1
    have : classicalE4 τ₁ = (actualA τ₁ / actualA τ₂) ^ 2 * classicalE4 τ₂ := by
      field_simp
      have := congrArg (· * actualA τ₂ ^ 2) e1
      have := congrArg (· * actualA τ₁ ^ 2) e2
      apply mul_right_cancel₀ hP
      linear_combination actualA τ₂ ^ 2 * e1 - actualA τ₁ ^ 2 * e2
    rw [this, ← hμ2]; ring
  · have e1 := E6_function τ₁
    have e2 := E6_function τ₂
    rw [hx] at e1
    have : classicalE6 τ₁ = (actualA τ₁ / actualA τ₂) ^ 3 * classicalE6 τ₂ := by
      field_simp
      apply mul_right_cancel₀ (pow_ne_zero 2 hP)
      linear_combination actualA τ₂ ^ 3 * e1 - actualA τ₁ ^ 3 * e2
    rw [this, ← hμ2]; ring

end Zeta7Valence

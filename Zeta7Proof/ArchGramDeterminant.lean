import Mathlib
import Zeta7Proof.CommonRationalGerms

/-! C4, linear-algebra layer: the Gram-determinant representation of a nonsingular determinant.

For a nonsingular `M` and a positive definite Hermitian `G`, there is a `G`-orthonormal basis
`C` (`Cᴴ G C = 1`) adapted to the flag cut out by the rows of `M`, i.e. `M C` is lower
triangular, and then `|det M| = ∏ |(M C)ᵢᵢ| · (det G)^{1/2}`. The construction is the
LDL (Gram–Schmidt) decomposition taken in reversed order. For the seven-block source with the
same weight in every block, the Gram matrix is `1₇ ⊗ G_d`, with determinant `(det G_d)^7`. -/
noncomputable section
set_option autoImplicit false
namespace Zeta7Arch
open Matrix
open scoped ComplexOrder Kronecker

variable {N : ℕ}

theorem complex_pos_re {z : ℂ} (hz : 0 < z) : 0 < z.re ∧ z = (z.re : ℂ) := by
  obtain ⟨h1, h2⟩ := Complex.pos_iff.mp hz
  exact ⟨h1, Complex.ext (by simp) (by simpa using h2.symm)⟩

/-- An upper-triangular normalizer from the LDL decomposition. -/
theorem exists_upper_normalizer (S : Matrix (Fin N) (Fin N) ℂ) (hS : S.PosDef) :
    ∃ T : Matrix (Fin N) (Fin N) ℂ, Tᴴ * S * T = 1 ∧ ∀ i j, j < i → T i j = 0 := by
  classical
  set L := LDL.lowerInv hS with hL
  have hD : LDL.diag hS = L * S * Lᴴ := LDL.diag_eq_lowerInv_conj hS
  have hLu : IsUnit L := (Matrix.isUnit_iff_isUnit_det L).mpr (Matrix.isUnit_det_of_invertible L)
  have hDpos : (LDL.diag hS).PosDef := by
    rw [hD]
    exact hS.mul_mul_conjTranspose_same (Matrix.vecMul_injective_of_isUnit hLu)
  set δ := LDL.diagEntries hS
  have hδ : ∀ i, 0 < (δ i).re ∧ δ i = ((δ i).re : ℂ) := fun i => by
    have := hDpos.diag_pos (i := i)
    simp only [LDL.diag, diagonal_apply_eq] at this
    exact complex_pos_re this
  set s : Fin N → ℂ := fun i => ((Real.sqrt (δ i).re)⁻¹ : ℝ)
  refine ⟨Lᴴ * diagonal s, ?_, ?_⟩
  · have hE : (diagonal s)ᴴ = diagonal s := by
      rw [diagonal_conjTranspose]
      congr 1
      ext i
      simp [s, Complex.conj_ofReal]
    calc (Lᴴ * diagonal s)ᴴ * S * (Lᴴ * diagonal s)
        = diagonal s * (L * S * Lᴴ) * diagonal s := by
          rw [conjTranspose_mul, hE, conjTranspose_conjTranspose]
          simp only [Matrix.mul_assoc]
      _ = diagonal s * LDL.diag hS * diagonal s := by rw [hD]
      _ = 1 := by
          rw [LDL.diag, diagonal_mul_diagonal, diagonal_mul_diagonal, ← diagonal_one]
          congr 1
          ext i
          obtain ⟨hpos, heq⟩ := hδ i
          change s i * δ i * s i = 1
          rw [heq]
          simp only [s]
          rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_one]
          congr 1
          have hsq := Real.sq_sqrt hpos.le
          have hne : Real.sqrt (δ i).re ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
          field_simp
          linarith
  · intro i j hji
    have h0 : L j i = 0 := by rw [hL]; exact LDL.lowerInv_triangular hS hji
    rw [mul_diagonal, conjTranspose_apply, h0, star_zero, zero_mul]

/-- The reversed normalizer is lower triangular. -/
theorem exists_lower_normalizer (S : Matrix (Fin N) (Fin N) ℂ) (hS : S.PosDef) :
    ∃ T : Matrix (Fin N) (Fin N) ℂ, Tᴴ * S * T = 1 ∧ T.IsLowerTriangular := by
  classical
  set r : Fin N ≃ Fin N := Fin.revPerm
  have hS' : (S.submatrix r r).PosDef := hS.submatrix r.injective
  obtain ⟨T', hT', hup⟩ := exists_upper_normalizer _ hS'
  refine ⟨T'.submatrix r r, ?_, ?_⟩
  · have hS2 : S = (S.submatrix r r).submatrix r r := by
      ext i j; simp [r]
    rw [hS2, conjTranspose_submatrix, submatrix_mul_equiv _ _ _ r _,
      submatrix_mul_equiv _ _ _ r _, hT', submatrix_one_equiv]
  · intro i j hij
    simp only [submatrix_apply]
    apply hup
    change OrderDual.toDual j < OrderDual.toDual i at hij
    rw [OrderDual.toDual_lt_toDual] at hij
    exact Fin.rev_lt_rev.mpr hij

/-- **Gram-determinant representation.** -/
theorem gram_det_representation (M G : Matrix (Fin N) (Fin N) ℂ) (hM : IsUnit M.det)
    (hG : G.PosDef) :
    ∃ C : Matrix (Fin N) (Fin N) ℂ, Cᴴ * G * C = 1 ∧ (M * C).IsLowerTriangular ∧
      ‖M.det‖ = (∏ i, ‖(M * C) i i‖) * Real.sqrt G.det.re := by
  classical
  set B := M⁻¹
  have hBu : IsUnit B := (Matrix.isUnit_nonsing_inv_iff).mpr ((Matrix.isUnit_iff_isUnit_det M).mpr hM)
  have hS : (Bᴴ * G * B).PosDef :=
    hG.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit hBu)
  obtain ⟨T, hT, hlow⟩ := exists_lower_normalizer _ hS
  have hMB : M * B = 1 := Matrix.mul_nonsing_inv M hM
  have hCunit : (B * T)ᴴ * G * (B * T) = 1 := by
    rw [conjTranspose_mul]
    calc Tᴴ * Bᴴ * G * (B * T) = Tᴴ * (Bᴴ * G * B) * T := by simp only [Matrix.mul_assoc]
      _ = 1 := hT
  have hMC : M * (B * T) = T := by rw [← Matrix.mul_assoc, hMB, Matrix.one_mul]
  refine ⟨B * T, hCunit, by rw [hMC]; exact hlow, ?_⟩
  rw [hMC]
  have hdetT : T.det = ∏ i, T i i := det_of_isLowerTriangular T hlow
  obtain ⟨hgpos, hgeq⟩ := complex_pos_re hG.det_pos
  have hd := congrArg det hCunit
  rw [det_mul, det_mul, det_conjTranspose, det_one] at hd
  have hx : ‖(B * T).det‖ ^ 2 * G.det.re = 1 := by
    have h := congrArg norm hd
    rw [norm_mul, norm_mul, norm_star, norm_one, hgeq, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hgpos] at h
    nlinarith [h]
  have hy : ‖M.det‖ * ‖(B * T).det‖ = ∏ i, ‖T i i‖ := by
    rw [← norm_mul, ← det_mul, hMC, hdetT, norm_prod]
  have hsg := Real.sq_sqrt hgpos.le
  have hxs : ‖(B * T).det‖ * Real.sqrt G.det.re = 1 := by
    have h0 : 0 ≤ ‖(B * T).det‖ * Real.sqrt G.det.re := by positivity
    have h1 : (‖(B * T).det‖ * Real.sqrt G.det.re) ^ 2 = 1 := by rw [mul_pow, hsg]; exact hx
    nlinarith [h0, h1]
  calc ‖M.det‖ = ‖M.det‖ * (‖(B * T).det‖ * Real.sqrt G.det.re) := by rw [hxs, mul_one]
    _ = (∏ i, ‖T i i‖) * Real.sqrt G.det.re := by rw [← hy]; ring

/-! ### The seven-block Gram matrix -/

/-- The orthogonal-sum Gram matrix of seven blocks, each carrying the same `G_d`. -/
def sevenBlockGram {d : ℕ} (Gd : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin 7 × Fin d) (Fin 7 × Fin d) ℂ :=
  (1 : Matrix (Fin 7) (Fin 7) ℂ) ⊗ₖ Gd

theorem sevenBlockGram_apply {d : ℕ} (Gd : Matrix (Fin d) (Fin d) ℂ) (a b : Fin 7 × Fin d) :
    sevenBlockGram Gd a b = if a.1 = b.1 then Gd a.2 b.2 else 0 := by
  simp [sevenBlockGram, kroneckerMap_apply, one_apply]

theorem sevenBlockGram_posDef {d : ℕ} {Gd : Matrix (Fin d) (Fin d) ℂ} (hG : Gd.PosDef) :
    (sevenBlockGram Gd).PosDef :=
  PosDef.one.kronecker hG

theorem sevenBlockGram_det {d : ℕ} (Gd : Matrix (Fin d) (Fin d) ℂ) :
    (sevenBlockGram Gd).det = Gd.det ^ 7 := by
  rw [sevenBlockGram, det_kronecker, det_one, one_pow, one_mul, Fintype.card_fin]

/-- Relabelling the source coordinates preserves positivity and the determinant. -/
theorem relabel_gram {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : ι ≃ κ) {G : Matrix κ κ ℂ} (hG : G.PosDef) :
    (G.submatrix e e).PosDef ∧ (G.submatrix e e).det = G.det :=
  ⟨hG.submatrix e.injective, det_submatrix_equiv_self e G⟩

end Zeta7Arch

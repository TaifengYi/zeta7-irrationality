import Zeta7Proof.ArchQPullback
import Zeta7Proof.ArchGramDeterminant
import Zeta7Proof.ActualN4BoundedRows

/-! C3–C4: the original seven-block source space over `ℂ`, its monomial basis, the vanishing flag
at the actual jump rows, and the Gram-determinant representation of the unchanged determinant.

* `complexGerms c` is the complex embedding of the six actual rational germs; the seventh germ
  is `1`.
* `SourcePoly d = Fin 7 → degreeLT ℂ d` is the original block-polynomial source; `sourceEquiv`
  identifies it with monomial coordinates `BlockIndex d → ℂ`, and `monomialBasis` maps to
  exactly the columns `blockSeries d` used by `actualCommonDeterminant`.
* `jump d c` are the canonical jump rows of the rational coefficient rows (the rows of the
  determinant), with `k ≤ λ_k ≤ k + 176`.
* `flag d c k` is the common kernel of the selected rows `λ_l`, `l < k`. It is a complete flag
  (`finrank = 7d - k`), and every vector in it has image vanishing below `x^{λ_k}`.
* `actualDeterminant_gram_representation`: for any positive definite `G_d`, there is an
  orthonormal basis for the seven-block Gram matrix, adapted to the flag, with
  `|D_d| = ∏_k |[x^{λ_k}] F_k| · (det G_d)^{7/2}` for the unchanged `D_d`. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
namespace Zeta7Arch
open PowerSeries Zeta7Common Matrix
open scoped ComplexOrder

/-! ### Complex embedding of the seven germs -/

/-- The complex embedding of the six actual germs. -/
def complexGerms (c : ℚ) : Fin 6 → ℂ⟦X⟧ := fun j => (rationalGerms c j).map (algebraMap ℚ ℂ)

/-- The seven germs `(1, g_0, …, g_5)` over `ℂ`. -/
def sevenGerms (c : ℚ) : Fin 7 → ℂ⟦X⟧ := Fin.cons 1 (complexGerms c)

theorem complex_coefficientRow (d : ℕ) (c : ℚ) (n : ℕ) (i : BlockIndex d) :
    coefficientRow d (complexGerms c) n i =
      ((coefficientRow d (rationalGerms c) n i : ℚ) : ℂ) := by
  rcases i with m | ⟨j, m⟩
  · simp only [coefficientRow, blockSeries, coeff_X_pow]
    split_ifs <;> simp
  · simp only [coefficientRow, blockSeries, complexGerms]
    rw [← PowerSeries.map_X (algebraMap ℚ ℂ), ← map_pow, ← map_mul, coeff_map]
    rfl

/-! ### The original source space and its monomial basis -/

/-- Block `0` is the polynomial block; block `j+1` multiplies `g_j`. -/
def blockPos (d : ℕ) : BlockIndex d ≃ Fin 7 × Fin d where
  toFun i := match i with
    | .inl m => (0, m)
    | .inr jm => (jm.1.succ, jm.2)
  invFun p := Fin.cases (motive := fun _ => Fin d → BlockIndex d) (fun m => .inl m)
    (fun j m => .inr (j, m)) p.1 p.2
  left_inv i := by rcases i with m | ⟨j, m⟩ <;> simp
  right_inv p := by
    obtain ⟨k, m⟩ := p
    cases k using Fin.cases <;> simp

theorem blockSeries_blockPos_symm {K : Type*} [CommRing K] (d : ℕ) (g : Fin 6 → K⟦X⟧)
    (k : Fin 7) (m : Fin d) :
    blockSeries d g ((blockPos d).symm (k, m)) = X ^ m.val * (Fin.cons 1 g : Fin 7 → K⟦X⟧) k := by
  cases k using Fin.cases <;> simp [blockPos, blockSeries]

/-- Seven polynomial blocks of degree `< d`. -/
abbrev SourcePoly (d : ℕ) := Fin 7 → Polynomial.degreeLT ℂ d

/-- Monomial coordinates of the source. -/
abbrev Source (d : ℕ) := BlockIndex d → ℂ

/-- The monomial-coordinate isomorphism. -/
def sourceEquiv (d : ℕ) : SourcePoly d ≃ₗ[ℂ] Source d where
  toFun P i := Polynomial.degreeLTEquiv ℂ d (P (blockPos d i).1) (blockPos d i).2
  invFun v k := (Polynomial.degreeLTEquiv ℂ d).symm (fun m => v ((blockPos d).symm (k, m)))
  map_add' P Q := by ext i; simp
  map_smul' a P := by ext i; simp
  left_inv P := by
    ext1 k
    simp only [Equiv.apply_symm_apply]
    exact (Polynomial.degreeLTEquiv ℂ d).symm_apply_apply (P k)
  right_inv v := by
    ext1 i
    simp only [LinearEquiv.apply_symm_apply, Prod.mk.eta, Equiv.symm_apply_apply]

theorem sourceEquiv_apply (d : ℕ) (P : SourcePoly d) (i : BlockIndex d) :
    sourceEquiv d P i = ((P (blockPos d i).1 : Polynomial ℂ)).coeff (blockPos d i).2 := rfl

/-- The monomial basis of the seven-block source. -/
def monomialBasis (d : ℕ) : Module.Basis (BlockIndex d) ℂ (SourcePoly d) :=
  (Pi.basisFun ℂ (BlockIndex d)).map (sourceEquiv d).symm

/-- The image `Σ_k P_k g_k` of a tuple of polynomials. -/
def polyImage (c : ℚ) (P : Fin 7 → Polynomial ℂ) : ℂ⟦X⟧ :=
  ∑ k, (P k : ℂ⟦X⟧) * sevenGerms c k

/-- The same image in monomial coordinates: the columns of the original determinant. -/
def sourceMap (d : ℕ) (c : ℚ) : Source d →ₗ[ℂ] ℂ⟦X⟧ where
  toFun v := ∑ i, v i • blockSeries d (complexGerms c) i
  map_add' v w := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a v := by simp [smul_smul, Finset.smul_sum]

theorem coe_degreeLT_eq_sum (d : ℕ) (p : Polynomial.degreeLT ℂ d) :
    ((p : Polynomial ℂ) : ℂ⟦X⟧) =
      ∑ m : Fin d, ((p : Polynomial ℂ).coeff m) • (X : ℂ⟦X⟧) ^ m.val := by
  ext n
  rw [Polynomial.coeff_coe, map_sum]
  simp only [coeff_smul, coeff_X_pow, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Fin.sum_univ_eq_sum_range (fun m => if n = m then (p : Polynomial ℂ).coeff m else 0) d,
    Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · have hp := Polynomial.mem_degreeLT.mp p.2
    apply Polynomial.coeff_eq_zero_of_degree_lt
    refine lt_of_lt_of_le hp ?_
    exact_mod_cast Nat.le_of_not_lt (fun h' => h (Finset.mem_range.mpr h'))

/-- **The source identification.** The polynomial image equals the monomial image. -/
theorem polyImage_eq (d : ℕ) (c : ℚ) (P : SourcePoly d) :
    polyImage c (fun k => (P k : Polynomial ℂ)) = sourceMap d c (sourceEquiv d P) := by
  change _ = ∑ i, sourceEquiv d P i • blockSeries d (complexGerms c) i
  rw [← (blockPos d).symm.sum_comp, Fintype.sum_prod_type]
  simp only [sourceEquiv_apply, Equiv.apply_symm_apply, blockSeries_blockPos_symm]
  unfold polyImage
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [coe_degreeLT_eq_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [smul_mul_assoc]
  rfl

theorem sourceMap_single (d : ℕ) (c : ℚ) (i : BlockIndex d) :
    sourceMap d c (Pi.single i 1) = blockSeries d (complexGerms c) i := by
  classical
  change ∑ i', (Pi.single i (1 : ℂ) : BlockIndex d → ℂ) i' • blockSeries d (complexGerms c) i' = _
  rw [Finset.sum_eq_single i (fun b _ hb => by simp [hb]) (by simp)]
  simp

/-- The monomial basis maps exactly to the columns `x^m g_j` of the original determinant. -/
theorem polyImage_monomialBasis (d : ℕ) (c : ℚ) (i : BlockIndex d) :
    polyImage c (fun k => (monomialBasis d i k : Polynomial ℂ)) =
      blockSeries d (complexGerms c) i := by
  rw [polyImage_eq, monomialBasis, Module.Basis.map_apply, LinearEquiv.apply_symm_apply,
    Pi.basisFun_apply, sourceMap_single]

theorem coeff_sourceMap (d : ℕ) (c : ℚ) (n : ℕ) (v : Source d) :
    coeff n (sourceMap d c v) =
      ∑ i, ((coefficientRow d (rationalGerms c) n i : ℚ) : ℂ) * v i := by
  change coeff n (∑ i, v i • blockSeries d (complexGerms c) i) = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coeff_smul, smul_eq_mul, ← complex_coefficientRow, mul_comm]
  rfl

/-! ### Jump rows and the vanishing flag -/

/-- Indices of the selected rows, in increasing order. -/
abbrev JIdx (d : ℕ) := Fin (Fintype.card (BlockIndex d))

theorem card_blockIndex (d : ℕ) : Fintype.card (BlockIndex d) = 7 * d := by
  simp [BlockIndex, TailIndex]
  omega

/-- The actual jump rows `λ_0 < λ_1 < …` of the unchanged determinant. -/
def jump (d : ℕ) (c : ℚ) : JIdx d ↪o ℕ :=
  Zeta7Jump.fullJumpRow (coefficientRow d (rationalGerms c)) (rationalGerms_fullRank c d)

theorem jump_bounds (d : ℕ) (c : ℚ) (k : JIdx d) :
    k.val ≤ jump d c k ∧ jump d c k ≤ k.val + 176 :=
  rationalGerms_jumpRow_bounds c d k

/-- The coefficient functional `v ↦ [x^n] F_v`. -/
def rowFun (d : ℕ) (c : ℚ) (n : ℕ) : Source d →ₗ[ℂ] ℂ :=
  (PowerSeries.coeff n).comp (sourceMap d c)

/-- The flag: common kernel of the selected rows before `k`. -/
def flag (d : ℕ) (c : ℚ) (k : JIdx d) : Submodule ℂ (Source d) :=
  ⨅ l : {l : JIdx d // l < k}, LinearMap.ker (rowFun d c (jump d c l))

theorem mem_flag {d : ℕ} {c : ℚ} {k : JIdx d} {v : Source d} :
    v ∈ flag d c k ↔ ∀ l < k, coeff (jump d c l) (sourceMap d c v) = 0 := by
  simp only [flag, Submodule.mem_iInf, LinearMap.mem_ker, rowFun, LinearMap.comp_apply,
    Subtype.forall]

/-- **Vanishing below the jump.** A flag vector's image has no coefficient below `x^{λ_k}`. -/
theorem flag_vanishing (d : ℕ) (c : ℚ) (k : JIdx d) (v : Source d) (hv : v ∈ flag d c k)
    (m : ℕ) (hm : m < jump d c k) : coeff m (sourceMap d c v) = 0 := by
  classical
  set R := coefficientRow d (rationalGerms c) with hR
  set h := rationalGerms_fullRank c d
  let φ : (BlockIndex d → ℚ) →ₗ[ℚ] ℂ :=
    { toFun := fun w => ∑ i, ((w i : ℚ) : ℂ) * v i
      map_add' := by intro a b; simp [add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro a w
        simp only [Pi.smul_apply, smul_eq_mul, Rat.cast_mul, RingHom.id_apply, Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Rat.smul_def, mul_assoc] }
  have hφ : ∀ n, φ (R n) = coeff n (sourceMap d c v) := fun n => (coeff_sourceMap d c n v).symm
  have hspan : Zeta7Jump.rowSpan (K := ℚ) R (m + 1) ≤ LinearMap.ker φ := by
    rw [← (Zeta7Jump.pivots_independent_span (K := ℚ) R (m + 1)).2]
    apply Submodule.span_le.mpr
    rintro _ ⟨p, hp, rfl⟩
    have hp' : p < m + 1 ∧ R p ∉ Zeta7Jump.rowSpan (K := ℚ) R p := by
      have := Finset.mem_coe.mp hp
      unfold Zeta7Jump.pivots at this
      simpa using this
    have hpc : p ∈ Zeta7Jump.pivots (K := ℚ) R (Zeta7Jump.cutoff R h) := by
      have hmem : jump d c k ∈ Zeta7Jump.pivots (K := ℚ) R (Zeta7Jump.cutoff R h) :=
        Finset.orderEmbOfFin_mem _ _ k
      have hcut : jump d c k < Zeta7Jump.cutoff R h := by
        unfold Zeta7Jump.pivots at hmem
        simpa using (Finset.mem_filter.mp hmem).1
      unfold Zeta7Jump.pivots
      simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, hp'.2⟩
    obtain ⟨l, hl⟩ : p ∈ Set.range (jump d c) := by
      change p ∈ Set.range (Zeta7Jump.fullJumpRow R h)
      rw [Zeta7Jump.fullJumpRow, Finset.range_orderEmbOfFin]
      exact hpc
    have hlk : l < k := (jump d c).lt_iff_lt.mp (by rw [hl]; omega)
    simp only [SetLike.mem_coe, LinearMap.mem_ker]
    rw [← hl, hφ]
    exact mem_flag.mp hv l hlk
  have hm' : R m ∈ Zeta7Jump.rowSpan (K := ℚ) R (m + 1) :=
    Submodule.subset_span ⟨m, by simp, rfl⟩
  have := hspan hm'
  rw [LinearMap.mem_ker, hφ] at this
  exact this

/-- At the jump itself the coefficient is the selected-row functional. -/
theorem flag_leading (d : ℕ) (c : ℚ) (k : JIdx d) (v : Source d) :
    coeff (jump d c k) (sourceMap d c v) = rowFun d c (jump d c k) v := rfl

/-! ### The selected matrix of the unchanged determinant -/

/-- Rows are the jump rows in increasing order; columns are the source monomials in block order. -/
def selMatrix (d : ℕ) (c : ℚ) : Matrix (JIdx d) (JIdx d) ℂ :=
  fun k l => ((coefficientRow d (rationalGerms c) (jump d c k) ((blockOrder d).symm l) : ℚ) : ℂ)

theorem det_selMatrix (d : ℕ) (c : ℚ) :
    (selMatrix d c).det = (actualCommonDeterminant d c : ℂ) := by
  have h1 : (actualCommonDeterminant d c : ℂ) =
      ((algebraMap ℚ ℂ).mapMatrix (commonMatrix d c (rationalGerms_fullRank c d))).det := by
    rw [actualCommonDeterminant, commonDeterminant, ← RingHom.map_det]
    rfl
  rw [h1, ← det_submatrix_equiv_self (blockOrder d).symm]
  congr 1
  ext k l
  simp only [submatrix_apply, RingHom.mapMatrix_apply, map_apply, commonMatrix,
    Equiv.apply_symm_apply, selMatrix, jump]
  rfl

theorem selMatrix_det_isUnit (d : ℕ) (c : ℚ) : IsUnit (selMatrix d c).det := by
  rw [det_selMatrix]
  exact Ne.isUnit (by exact_mod_cast actualCommonDeterminant_ne_zero d c)

/-- Coordinates listed in block order. -/
def coordEquiv (d : ℕ) : (JIdx d → ℂ) ≃ₗ[ℂ] Source d :=
  LinearEquiv.funCongrLeft ℂ ℂ (blockOrder d)

theorem coordEquiv_apply (d : ℕ) (w : JIdx d → ℂ) (i : BlockIndex d) :
    coordEquiv d w i = w (blockOrder d i) := rfl

theorem selMatrix_mulVec (d : ℕ) (c : ℚ) (w : JIdx d → ℂ) (k : JIdx d) :
    (selMatrix d c *ᵥ w) k = coeff (jump d c k) (sourceMap d c (coordEquiv d w)) := by
  rw [coeff_sourceMap, mulVec, dotProduct, ← (blockOrder d).sum_comp]
  simp only [selMatrix, Equiv.symm_apply_apply, coordEquiv_apply]

theorem card_fin_lt {N : ℕ} (k : Fin N) : Fintype.card {l : Fin N // l < k} = k.val := by
  rw [Fintype.card_subtype]
  have h : (Finset.univ.filter fun l : Fin N => l < k) =
      Finset.univ.filter fun l : Fin N => (l : ℕ) < k.val := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact Fin.lt_def
  rw [h, Fin.card_filter_val_lt]
  have := k.isLt
  omega

/-- **Complete flag.** `dim flag_k = 7d - k`. -/
theorem flag_finrank (d : ℕ) (c : ℚ) (k : JIdx d) :
    Module.finrank ℂ (flag d c k) = Fintype.card (BlockIndex d) - k.val := by
  classical
  let Φ : Source d →ₗ[ℂ] ({l : JIdx d // l < k} → ℂ) :=
    LinearMap.pi fun l => rowFun d c (jump d c l.1)
  have hker : LinearMap.ker Φ = flag d c k := by
    ext v
    simp only [LinearMap.mem_ker, Φ, flag, Submodule.mem_iInf, funext_iff, LinearMap.pi_apply,
      Pi.zero_apply]
  have hsurj : Function.Surjective Φ := by
    intro y
    let z : JIdx d → ℂ := fun l => if hl : l < k then y ⟨l, hl⟩ else 0
    refine ⟨coordEquiv d ((selMatrix d c)⁻¹ *ᵥ z), ?_⟩
    funext l
    simp only [Φ, LinearMap.pi_apply, rowFun, LinearMap.comp_apply]
    rw [← selMatrix_mulVec, mulVec_mulVec, mul_nonsing_inv _ (selMatrix_det_isUnit d c),
      one_mulVec]
    simp [z, l.2]
  have hrange : LinearMap.range Φ = ⊤ := LinearMap.range_eq_top.mpr hsurj
  have hrn := LinearMap.finrank_range_add_finrank_ker Φ
  rw [hrange, finrank_top, hker, Module.finrank_fintype_fun_eq_card,
    Module.finrank_fintype_fun_eq_card] at hrn
  have hcard : Fintype.card {l : JIdx d // l < k} = k.val := card_fin_lt k
  omega

/-! ### The Gram-determinant representation of the unchanged determinant -/

/-- The seven-block Gram matrix in the original monomial basis, listed in block order. -/
def sourceGram (d : ℕ) (Gd : Matrix (Fin d) (Fin d) ℂ) : Matrix (JIdx d) (JIdx d) ℂ :=
  (sevenBlockGram Gd).submatrix ((blockOrder d).symm.trans (blockPos d))
    ((blockOrder d).symm.trans (blockPos d))

theorem sourceGram_posDef (d : ℕ) {Gd : Matrix (Fin d) (Fin d) ℂ} (hG : Gd.PosDef) :
    (sourceGram d Gd).PosDef :=
  (relabel_gram _ (sevenBlockGram_posDef hG)).1

theorem sourceGram_det (d : ℕ) (Gd : Matrix (Fin d) (Fin d) ℂ) :
    (sourceGram d Gd).det = Gd.det ^ 7 := by
  rw [sourceGram, det_submatrix_equiv_self, sevenBlockGram_det]

/-- The `k`-th adapted source vector determined by the columns of `C`. -/
def adaptedVector (d : ℕ) (C : Matrix (JIdx d) (JIdx d) ℂ) (k : JIdx d) : Source d :=
  coordEquiv d (fun l => C l k)

/-- **C4 endpoint (exact representation).** For every positive definite weight Gram matrix `G_d`
on polynomials of degree `< d`, the unchanged determinant satisfies
`|D_d| = ∏_k |[x^{λ_k}] F_k| · (det G_d)^{7/2}`, where `F_k` are the images of an orthonormal
basis (for the seven-block Gram matrix) adapted to the vanishing flag; each `F_k` vanishes below
`x^{λ_k}`. -/
theorem actualDeterminant_gram_representation (d : ℕ) (c : ℚ)
    (Gd : Matrix (Fin d) (Fin d) ℂ) (hG : Gd.PosDef) :
    ∃ C : Matrix (JIdx d) (JIdx d) ℂ,
      Cᴴ * sourceGram d Gd * C = 1 ∧
      (∀ k, adaptedVector d C k ∈ flag d c k) ∧
      (∀ k, ∀ m < jump d c k, coeff m (sourceMap d c (adaptedVector d C k)) = 0) ∧
      |(actualCommonDeterminant d c : ℝ)| =
        (∏ k, ‖coeff (jump d c k) (sourceMap d c (adaptedVector d C k))‖) *
          Real.sqrt (Gd.det.re ^ 7) := by
  obtain ⟨C, hC, hlow, hnorm⟩ :=
    gram_det_representation (selMatrix d c) (sourceGram d Gd) (selMatrix_det_isUnit d c)
      (sourceGram_posDef d hG)
  have hentry : ∀ l k, (selMatrix d c * C) l k =
      coeff (jump d c l) (sourceMap d c (adaptedVector d C k)) := by
    intro l k
    rw [adaptedVector, ← selMatrix_mulVec]
    rfl
  have hflag : ∀ k, adaptedVector d C k ∈ flag d c k := by
    intro k
    refine mem_flag.mpr fun l hl => ?_
    rw [← hentry]
    exact hlow (by simpa using hl)
  refine ⟨C, hC, hflag, fun k m hm => flag_vanishing d c k _ (hflag k) m hm, ?_⟩
  rw [det_selMatrix, sourceGram_det, Complex.norm_ratCast] at hnorm
  obtain ⟨_, hgeq⟩ := complex_pos_re hG.det_pos
  have hre : (Gd.det ^ 7).re = Gd.det.re ^ 7 := by
    rw [hgeq, ← Complex.ofReal_pow, Complex.ofReal_re, Complex.ofReal_re]
  rw [hre] at hnorm
  rw [hnorm]
  congr 1
  exact Finset.prod_congr rfl fun k _ => by rw [hentry]

end Zeta7Arch

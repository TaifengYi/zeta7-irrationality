import Zeta7Proof.CanonicalJumpRows
import Zeta7Proof.CommonRationalGerms
import Zeta7Proof.RationalDeterminantProductFormula

/-! One canonical rational determinant and its three local contributions.
Nonvanishing is proved from the explicitly stated independence of the actual
seven monomial blocks. That independence is not assumed as a project axiom. -/

set_option autoImplicit false
noncomputable section
open PowerSeries Submodule
namespace Zeta7Common
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

def seriesCoefficients {K : Type*} [Field K] : K⟦X⟧ →ₗ[K] (ℕ → K) where
  toFun f n := coeff n f
  map_add' f g := by ext n; simp
  map_smul' a f := by ext n; simp

theorem seriesCoefficients_injective {K : Type*} [Field K] :
    Function.Injective (seriesCoefficients (K := K)) := by
  intro f g h
  ext n
  exact congrFun h n

theorem fullRank_of_block_independent {K : Type*} [Field K]
    (d : ℕ) (g : Fin 6 → K⟦X⟧) (h : LinearIndependent K (blockSeries d g)) :
    Zeta7Jump.FullRank (coefficientRow d g) := by
  have hc := h.map' seriesCoefficients
    (LinearMap.ker_eq_bot.mpr seriesCoefficients_injective)
  exact Zeta7Jump.exists_rowSpan_eq_top _ (span_flip_eq_top_iff_linearIndependent.mpr hc)

/-- The order is polynomial block first, then the six germs in their prescribed order. -/
def blockOrder (d : ℕ) : BlockIndex d ≃ Fin (Fintype.card (BlockIndex d)) :=
  ((Equiv.refl (Fin d)).sumCongr finProdFinEquiv).trans
    (finSumFinEquiv.trans (finCongr (by simp [BlockIndex, TailIndex])))

theorem blockOrder_inl (d : ℕ) (k : Fin d) : (blockOrder d (.inl k)).val = k.val := rfl

theorem blockOrder_inr (d : ℕ) (jk : TailIndex d) :
    (blockOrder d (.inr jk)).val = d + (jk.2.val + d * jk.1.val) := rfl

/-- Polynomial columns certify that every row before d is a jump. -/
theorem initial_row_notMem {K : Type*} [Field K] (d : ℕ) (g : Fin 6 → K⟦X⟧)
    (n : ℕ) (hn : n < d) :
    coefficientRow d g n ∉ Zeta7Jump.rowSpan (K := K) (coefficientRow d g) n := by
  let ev : (BlockIndex d → K) →ₗ[K] K := LinearMap.proj (.inl ⟨n, hn⟩)
  have hs : Zeta7Jump.rowSpan (K := K) (coefficientRow d g) n ≤ LinearMap.ker ev := by
    apply span_le.mpr
    rintro _ ⟨m, hm, rfl⟩
    have hmn : m ≠ n := Nat.ne_of_lt (Finset.mem_range.mp hm)
    simp [LinearMap.mem_ker, ev, coefficientRow, blockSeries, coeff_X_pow, hmn]
  intro h
  have hz := hs h
  simp [LinearMap.mem_ker, ev, coefficientRow, blockSeries, coeff_X_pow] at hz

theorem initial_rows_are_pivots {K : Type*} [Field K] (d : ℕ) (g : Fin 6 → K⟦X⟧)
    (h : Zeta7Jump.FullRank (coefficientRow d g)) (n : ℕ) (hn : n < d) :
    n ∈ Zeta7Jump.pivots (K := K) (coefficientRow d g)
      (Zeta7Jump.cutoff (coefficientRow d g) h) := by
  classical
  have hncut : n < Zeta7Jump.cutoff (coefficientRow d g) h := by
    by_contra hge
    have hfull := Zeta7Jump.cutoff_full (coefficientRow d g) h
    have hs := Zeta7Jump.rowSpan_mono (K := K) (coefficientRow d g) (Nat.le_of_not_gt hge)
    rw [hfull] at hs
    exact initial_row_notMem d g n hn (hs (by trivial))
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hncut, initial_row_notMem d g n hn⟩

def selectedTailRow (d : ℕ) (c : ℚ)
    (h : Zeta7Jump.FullRank (coefficientRow d (rationalGerms c))) : TailIndex d → ℕ :=
  fun jk => Zeta7Jump.fullJumpRow _ h (blockOrder d (.inr jk))

theorem selectedTailRow_lower (d : ℕ) (c : ℚ)
    (h : Zeta7Jump.FullRank (coefficientRow d (rationalGerms c))) (jk : TailIndex d) :
    d ≤ selectedTailRow d c h jk := by
  have hb := Zeta7Jump.fullJumpRow_lower _ h (blockOrder d (.inr jk))
  rw [blockOrder_inr] at hb
  exact (Nat.le_add_right _ _).trans hb

def commonMatrix (d : ℕ) (c : ℚ)
    (h : Zeta7Jump.FullRank (coefficientRow d (rationalGerms c))) :
    Matrix (BlockIndex d) (BlockIndex d) ℚ :=
  fun i => coefficientRow d (rationalGerms c) (Zeta7Jump.fullJumpRow _ h (blockOrder d i))

def commonDeterminant (d : ℕ) (c : ℚ)
    (h : Zeta7Jump.FullRank (coefficientRow d (rationalGerms c))) : ℚ :=
  (commonMatrix d c h).det

theorem commonDeterminant_ne_zero (d : ℕ) (c : ℚ)
    (h : Zeta7Jump.FullRank (coefficientRow d (rationalGerms c))) :
    commonDeterminant d c h ≠ 0 := by
  have hi := (Zeta7Jump.fullJumpRow_independent _ h).comp (blockOrder d) (blockOrder d).injective
  exact ((Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.linearIndependent_rows_iff_isUnit.mp hi)).ne_zero

theorem commonMatrix_eq_fullMatrix (d : ℕ) (c : ℚ)
    (h : Zeta7Jump.FullRank (coefficientRow d (rationalGerms c))) :
    commonMatrix d c h = fullMatrix d (rationalGerms c) (selectedTailRow d c h) := by
  ext i j
  cases i with
  | inl k =>
    have hk := Zeta7Jump.fullJumpRow_initial _ h d
      (initial_rows_are_pivots d (rationalGerms c) h) (blockOrder d (.inl k))
      (by simpa only [blockOrder_inl] using k.isLt)
    simp only [blockOrder_inl] at hk
    simp only [commonMatrix, hk, fullMatrix, Sum.elim_inl]
  | inr jk => rfl

/-- Exact seven-block/tail equality, without a permutation sign or clearing factor. -/
theorem commonDeterminant_eq_tail (d : ℕ) (c : ℚ)
    (h : Zeta7Jump.FullRank (coefficientRow d (rationalGerms c))) :
    commonDeterminant d c h =
      (tailMatrix d (rationalGerms c) (selectedTailRow d c h)).det := by
  rw [commonDeterminant, commonMatrix_eq_fullMatrix,
    det_fullMatrix d _ _ (selectedTailRow_lower d c h)]

theorem commonDeterminant_target (d : ℕ) (c : ℚ)
    (hc : (c : ℚ_[7]) = Zeta7Main.eta)
    (h : Zeta7Jump.FullRank (coefficientRow d (rationalGerms c))) :
    (tailMatrix d targetGerms (selectedTailRow d c h)).det =
      (commonDeterminant d c h : ℚ_[7]) := by
  rw [commonDeterminant_eq_tail, target_det_eq_ratCast d c hc]

theorem commonDeterminant_complex (d : ℕ) (c : ℚ)
    (h : Zeta7Jump.FullRank (coefficientRow d (rationalGerms c))) :
    (tailMatrix d (fun j => (rationalGerms c j).map (algebraMap ℚ ℂ))
      (selectedTailRow d c h)).det = (commonDeterminant d c h : ℂ) := by
  rw [det_tailMatrix_map, commonDeterminant_eq_tail]
  rfl

/-- Exact normalization reuses Stage2A on these modular germs and these jump rows. -/
theorem commonDeterminant_normalization (d : ℕ) (c : ℚ)
    (h : Zeta7Jump.FullRank (coefficientRow d (rationalGerms c))) :
    (Zeta7Stage2A.normalizedTailMatrix d
      (fun j n => coeff n (rationalGerms c j)) (selectedTailRow d c h)).det =
      (∏ i, (1 : ℚ) / 49 ^ selectedTailRow d c h i) * commonDeterminant d c h *
        (∏ j : TailIndex d, (49 : ℚ) ^ j.2.val) := by
  rw [Zeta7Stage2A.det_normalizedTailMatrix d _ _ (selectedTailRow_lower d c h),
    ← tailMatrix_eq_stage2 d c _ (selectedTailRow_lower d c h), commonDeterminant_eq_tail]

theorem target_jumpDeterminant_ne_zero (d : ℕ) (c : ℚ)
    (hc : (c : ℚ_[7]) = Zeta7Main.eta)
    (h : Zeta7Jump.FullRank (coefficientRow d (rationalGerms c))) :
    (tailMatrix d targetGerms (selectedTailRow d c h)).det ≠ 0 := by
  rw [commonDeterminant_target d c hc h]
  exact_mod_cast commonDeterminant_ne_zero d c h

/-- All three terms are computed from exactly the same constructed rational determinant. -/
theorem commonDeterminant_productFormula (d : ℕ) (c : ℚ)
    (h : Zeta7Jump.FullRank (coefficientRow d (rationalGerms c))) :
    Zeta7ProductFormula.arch (commonDeterminant d c h) +
      Zeta7ProductFormula.target (commonDeterminant d c h) +
      Zeta7ProductFormula.auxiliary (commonDeterminant d c h) = 0 :=
  Zeta7ProductFormula.productFormula _ (commonDeterminant_ne_zero d c h)

/-- Product formula with the target term written as the norm of the actual target matrix. -/
theorem commonDeterminant_productFormula_target (d : ℕ) (c : ℚ)
    (hc : (c : ℚ_[7]) = Zeta7Main.eta)
    (h : Zeta7Jump.FullRank (coefficientRow d (rationalGerms c))) :
    Real.log |(commonDeterminant d c h : ℝ)| +
      Real.log ‖(tailMatrix d targetGerms (selectedTailRow d c h)).det‖ +
      Zeta7ProductFormula.auxiliary (commonDeterminant d c h) = 0 := by
  rw [commonDeterminant_target d c hc h,
    ← Zeta7ProductFormula.localTerm_eq_log_norm 7 _ (commonDeterminant_ne_zero d c h)]
  exact commonDeterminant_productFormula d c h

/-- Under the explicit block-independence hypothesis, construct the rational
determinant, its nonvanishing proof, and its product formula simultaneously. -/
theorem exists_commonDeterminant (d : ℕ) (c : ℚ)
    (hc : (c : ℚ_[7]) = Zeta7Main.eta)
    (hind : LinearIndependent ℚ (blockSeries d (rationalGerms c))) :
    ∃ (D : ℚ) (row : TailIndex d → ℕ), D ≠ 0 ∧
      (∀ i, d ≤ row i) ∧
      D = (fullMatrix d (rationalGerms c) row).det ∧
      (tailMatrix d targetGerms row).det = (D : ℚ_[7]) ∧
      Real.log |(D : ℝ)| + Real.log ‖(tailMatrix d targetGerms row).det‖ +
        Zeta7ProductFormula.auxiliary D = 0 := by
  let h := fullRank_of_block_independent d (rationalGerms c) hind
  refine ⟨commonDeterminant d c h, selectedTailRow d c h,
    commonDeterminant_ne_zero d c h, selectedTailRow_lower d c h, ?_,
    commonDeterminant_target d c hc h, commonDeterminant_productFormula_target d c hc h⟩
  rw [commonDeterminant, commonMatrix_eq_fullMatrix]

end Zeta7Common

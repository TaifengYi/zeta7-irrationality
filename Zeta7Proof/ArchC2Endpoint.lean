import Zeta7Proof.ArchBoundary

/-! C2 endpoint: the coefficient bound (41) for the actual adapted flag vectors of the unchanged
determinant.

For the norm (39) with weight `e^{-2dU}` on `𝒦`, the Gram-determinant representation gives an
orthonormal basis `C` for the seven-block Gram matrix, adapted to the vanishing flag, with
`|D_d| = ∏ |[x^{λ_k}] F_k| · (det G_d)^{7/2}`. Orthonormality of the `k`-th column is exactly
`Σ_b ‖P_b‖_d² = 1` over its seven block polynomials (`gram_diag_eq_sum_blocks`), so every block has
`‖P_b‖_d ≤ 1`, and (41) applies to every adapted vector:

`log |[x^{λ_k}] F_k| ≤ d W_i - λ_k t_i + d ω(h) + C_h`,

with `C_h` independent of `d`, of `k` and of the vector. -/
noncomputable section
set_option autoImplicit false
namespace Zeta7Arch
open MeasureTheory Set Real Filter Topology Matrix

/-- The index relabelling used by `sourceGram`. -/
theorem sourceGram_apply (d : ℕ) (Gd : Matrix (Fin d) (Fin d) ℂ) (l l' : JIdx d) :
    sourceGram d Gd l l' =
      sevenBlockGram Gd ((Zeta7Common.blockOrder d).symm.trans (blockPos d) l)
        ((Zeta7Common.blockOrder d).symm.trans (blockPos d) l') := rfl

/-- The diagonal of `Cᴴ G_src C` is the sum of the seven block Gram forms of the column. -/
theorem gram_diag_eq_sum_blocks (d : ℕ) (Gd : Matrix (Fin d) (Fin d) ℂ)
    (C : Matrix (JIdx d) (JIdx d) ℂ) (k : JIdx d) :
    (Cᴴ * sourceGram d Gd * C) k k =
      ∑ b : Fin 7, dotProduct (star (blockPoly (adaptedVector d C k) b))
        (Gd.mulVec (blockPoly (adaptedVector d C k) b)) := by
  set e : JIdx d ≃ Fin 7 × Fin d := (Zeta7Common.blockOrder d).symm.trans (blockPos d) with he
  set x : Fin 7 → Fin d → ℂ := fun b => blockPoly (adaptedVector d C k) b with hxdef
  have hx : ∀ p : Fin 7 × Fin d, C (e.symm p) k = x p.1 p.2 := by
    intro p
    simp [he, hxdef, blockPoly, adaptedVector, coordEquiv_apply]
  have hG : ∀ p p' : Fin 7 × Fin d, sourceGram d Gd (e.symm p) (e.symm p') =
      if p.1 = p'.1 then Gd p.2 p'.2 else 0 := by
    intro p p'
    rw [sourceGram_apply, ← he, Equiv.apply_symm_apply, Equiv.apply_symm_apply,
      sevenBlockGram_apply]
  calc (Cᴴ * sourceGram d Gd * C) k k
      = ∑ l, ∑ l', star (C l' k) * sourceGram d Gd l' l * C l k := by
        simp only [mul_apply, conjTranspose_apply, Finset.sum_mul]
    _ = ∑ p : Fin 7 × Fin d, ∑ p' : Fin 7 × Fin d,
          star (x p'.1 p'.2) * (if p'.1 = p.1 then Gd p'.2 p.2 else 0) * x p.1 p.2 := by
        rw [← e.symm.sum_comp]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [← e.symm.sum_comp]
        refine Finset.sum_congr rfl fun p' _ => ?_
        rw [hG, hx, hx]
    _ = ∑ b : Fin 7, ∑ m : Fin d, ∑ m' : Fin d, star (x b m') * Gd m' m * x b m := by
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun b _ => ?_
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [Fintype.sum_prod_type]
        simp only [mul_ite, ite_mul, mul_zero, zero_mul]
        rw [Finset.sum_comm]
        simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    _ = ∑ b : Fin 7, dotProduct (star (x b)) (Gd.mulVec (x b)) := by
        refine Finset.sum_congr rfl fun b _ => ?_
        simp only [dotProduct, mulVec, Pi.star_apply, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun m' _ => Finset.sum_congr rfl fun m _ => ?_
        ring

/-- Orthonormal columns have every block norm at most one. -/
theorem adapted_block_norm_le (d : ℕ) {C : Matrix (JIdx d) (JIdx d) ℂ}
    (hC : Cᴴ * sourceGram d (weightedGram d discK (gramWeight d)) * C = 1) (k : JIdx d)
    (b : Fin 7) : normSqD d (blockPoly (adaptedVector d C k) b) ≤ 1 := by
  have h := gram_diag_eq_sum_blocks d (weightedGram d discK (gramWeight d)) C k
  rw [hC, one_apply_eq] at h
  simp only [normSqD_eq_gram] at h
  have hreal : (1 : ℝ) = ∑ b' : Fin 7, normSqD d (blockPoly (adaptedVector d C k) b') := by
    have := congrArg Complex.re h
    simpa using this
  rw [hreal]
  exact Finset.single_le_sum (fun b' _ => normSqD_nonneg d _) (Finset.mem_univ b)

/-- **C2 endpoint.** For the actual weight `e^{-2dU}` on `𝒦`: the exact Gram representation of
the unchanged determinant together with the bound (41) for all adapted flag vectors, with `C_h`
independent of `d` and `k`. -/
theorem actualDeterminant_adapted_coefficient_bound (c : ℚ) (i : Fin 6) {h : ℝ} (hh : 0 < h)
    (h1 : h ≤ 1) :
    ∃ Ch : ℝ, ∀ d : ℕ, ∃ C : Matrix (JIdx d) (JIdx d) ℂ,
      Cᴴ * sourceGram d (weightedGram d discK (gramWeight d)) * C = 1 ∧
      (∀ k, adaptedVector d C k ∈ flag d c k) ∧
      |(Zeta7Common.actualCommonDeterminant d c : ℝ)| =
        (∏ k, ‖PowerSeries.coeff (jump d c k) (sourceMap d c (adaptedVector d C k))‖) *
          Real.sqrt ((weightedGram d discK (gramWeight d)).det.re ^ 7) ∧
      ∀ k, PowerSeries.coeff (jump d c k) (sourceMap d c (adaptedVector d C k)) ≠ 0 →
        Real.log ‖PowerSeries.coeff (jump d c k) (sourceMap d c (adaptedVector d C k))‖ ≤
          d * energyW i - (jump d c k : ℝ) * circleT i + d * omegaU h + Ch := by
  obtain ⟨Ch, hCh⟩ := coefficient_bound c i hh h1
  refine ⟨Ch, fun d => ?_⟩
  have hK : discK = Metric.closedBall (0 : ℂ) (supR + 1) := rfl
  have hρ : (0 : ℝ) < supR + 1 := by linarith [supR_nonneg]
  obtain ⟨C, hC, hflag, _, hdet⟩ := actualDeterminant_weighted_representation d c 0 hρ
    ((gramWeight_continuous d).continuousOn) (fun z _ => gramWeight_pos d z)
  rw [← hK] at hC hdet
  exact ⟨C, hC, hflag, hdet, fun k hne =>
    hCh d k _ (hflag k) (fun b => adapted_block_norm_le d hC k b) hne⟩

end Zeta7Arch

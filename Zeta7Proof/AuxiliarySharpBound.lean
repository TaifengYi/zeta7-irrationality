import Zeta7Proof.AuxiliaryJointThird
import Zeta7Proof.AuxiliaryFlagBasis

/-! P7: one compatible integral source basis for the unchanged `actualCommonDeterminant`, and
the sharp local valuation bound.

The basis keeps the actual cap-one columns (the lifted reduced first kernel of P4 and the
selected resonance columns `x^j C^±` themselves), then extends their independent reductions
along the flag of cap-two and cap-three reductions of actual columns. The cap-two part has
dimension at least `3d + s - b₀` (joint third layer), the cap-three part at least `6d - q_p`
(joint fourth layer). Every column is an actual integral source vector with the stated cap,
and the source change is unimodular because the reductions of all columns are independent. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
namespace Zeta7Auxiliary
open PowerSeries Zeta7Common

variable {p : ℕ} [Fact p.Prime]

/-- Index type of the retained cap-one columns. -/
abbrev CapOneIdx (d p : ℕ) : Type :=
  Fin (derivativeOne d p) ⊕ (Fin (resPosCount d p) ⊕ Fin (resNegCount d p))

theorem capOneIdx_card (hp : 2 ≤ p) (d : ℕ) :
    Fintype.card (CapOneIdx d p) = simultaneousOne d p := by
  simp only [CapOneIdx, Fintype.card_sum, Fintype.card_fin]
  rw [resCount_eq hp d]
  rfl

/-- **The retained actual cap-one columns**, including every selected resonance column. -/
theorem capOne_family (hp : 11 ≤ p) (c : ℚ) (hc : ¬p ∣ c.den) (d N : ℕ) (hd : 1 ≤ d)
    (hN : N ≤ p^2) :
    ∃ G : CapOneIdx d p → TailIndex d → ℤ_[p],
      (∀ i, Cap N 1 (actualSourceSeries p d c (G i))) ∧
      LinearIndependent (ZMod p) (fun i => redV (p := p) (TailIndex d) (G i)) ∧
      (∀ r, G (Sum.inr r) = resFamily p d r) := by
  classical
  obtain ⟨k, c₁, m, Y, Z, hsum, hb, hnk, hY0, hY1, hind⟩ := derivative_block hp d hd
  have hk : derivativeOne d p ≤ k := by
    unfold derivativeOne derivativeTwo derivativeThree derivativeBudget at *
    omega
  let Y' : Fin (derivativeOne d p) → DIdx d → ℤ_[p] := fun j => Y (Sum.inl (Fin.castLE hk j))
  have hY' : LinearIndependent (ZMod p) (fun j => redV (p := p) (DIdx d) (Y' j)) :=
    hind.comp (fun j => Sum.inl (Sum.inl (Fin.castLE hk j)))
      (Sum.inl_injective.comp (Sum.inl_injective.comp (Fin.castLE_injective hk)))
  refine ⟨Sum.elim (fun j => embedD (Y' j)) (resFamily p d), ?_, ?_, fun r => rfl⟩
  · rintro (j | r)
    · exact embedD_cap_one hp c hc _ (hY0 _) (hY1 _) N hN
    · exact resFamily_cap_one hp c hc d N hN r
  · have h := derivative_resonance_independent hp d Y' hY'
    have hfam : (fun i => redV (p := p) (TailIndex d)
        (Sum.elim (fun j => embedD (Y' j)) (resFamily p d) i)) =
        Sum.elim (fun j => redV (p := p) (TailIndex d) (embedD (Y' j)))
          (fun r => redV (p := p) (TailIndex d) (resFamily p d r)) := by
      funext i
      cases i <;> rfl
    rw [hfam]
    exact h

theorem card_filter_equiv {κ τ : Type*} [Fintype κ] [Fintype τ] (e : κ ≃ τ) (w : κ → ℕ)
    (v : ℕ) :
    (Finset.univ.filter (fun t : τ => (w ∘ e.symm) t = v)).card =
      (Finset.univ.filter (fun x : κ => w x = v)).card := by
  classical
  rw [← Fintype.card_subtype, ← Fintype.card_subtype]
  exact Fintype.card_congr (e.symm.subtypeEquiv (fun _ => Iff.rfl))

/-- Cap counts of a four-block family. -/
theorem card_filter_blocks {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (v : ℕ) :
    (Finset.univ.filter (fun x : ((A ⊕ B) ⊕ C) ⊕ D =>
      (Sum.elim (Sum.elim (Sum.elim (fun _ => 1) (fun _ => 2)) (fun _ => 3)) (fun _ => 4) x : ℕ)
        = v)).card =
      (if 1 = v then Fintype.card A else 0) + (if 2 = v then Fintype.card B else 0) +
        (if 3 = v then Fintype.card C else 0) + (if 4 = v then Fintype.card D else 0) := by
  classical
  rw [Finset.card_filter, Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  split_ifs <;> simp

/-- **P7: a single compatible integral basis** of the actual `6d`-dimensional source, with the
cap multiplicities `(c₂ + t, c₁ + c₀ + s - t - b₀, 3d - s - q_p + b₀, q_p)`, containing every
selected actual resonance column. -/
theorem compatible_integral_basis (hp : 11 ≤ p) (c : ℚ) (hc : ¬p ∣ c.den) (d : ℕ)
    (hd : 2 ≤ d) (hN : 7 * d + 176 ≤ p^2) :
    ∃ (U : Matrix (TailIndex d) (TailIndex d) ℤ_[p]) (w : TailIndex d → ℕ),
      IsUnit U.det ∧ (∀ j, 1 ≤ w j ∧ w j ≤ 4) ∧
      (∀ j, Cap (7 * d + 176) (w j) (actualSourceSeries p d c (fun i => U i j))) ∧
      (Finset.univ.filter (fun j => w j = 1)).card = simultaneousOne d p ∧
      (Finset.univ.filter (fun j => w j = 2)).card = simultaneousTwo d p ∧
      (Finset.univ.filter (fun j => w j = 3)).card = simultaneousThree d p (7 * d + 176) ∧
      (Finset.univ.filter (fun j => w j = 4)).card = jointFourthRank d p (7 * d + 176) ∧
      (∀ r, ∃ j, (fun i => U i j) = resFamily p d r) := by
  classical
  set N := 7 * d + 176 with hNdef
  obtain ⟨G₁, hG₁cap, hG₁ind, hG₁res⟩ := capOne_family hp c hc d N (by omega) hN
  have hκ1 := capOneIdx_card (p := p) (by omega) d
  have hS1 : ∀ i, redV (p := p) (TailIndex d) (G₁ i) ∈ capRed (p := p) d c N 1 :=
    fun i => mem_capRed _ (hG₁cap i)
  have hsum := simultaneous_counts_sum d p N hd
  have hb2 := capRed_two_bound hp c hc d N (by omega) hN
  have hb3 := capRed_three_bound hp c hc d N hd hN
  have hc3 := derivative_counts_sum d p
  have ht := resonanceShifts_le_primitiveShifts d p
  have hb0 : jointThirdRank d p ≤ derivativeThree d p + primitiveShifts d - resonanceShifts d p :=
    min_le_left _ _
  have h2 : Fintype.card (CapOneIdx d p) + simultaneousTwo d p ≤
      Module.finrank (ZMod p) (capRed (p := p) d c N 2) := by
    rw [hκ1]
    unfold simultaneousOne simultaneousTwo at *
    omega
  have h3 : Fintype.card (CapOneIdx d p) + simultaneousTwo d p + simultaneousThree d p N ≤
      Module.finrank (ZMod p) (capRed (p := p) d c N 3) := by
    rw [hκ1]
    omega
  have hdim : Module.finrank (ZMod p) (TailIndex d → ZMod p) = 6 * d := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp
  have h4 : Fintype.card (CapOneIdx d p) + simultaneousTwo d p + simultaneousThree d p N +
      jointFourthRank d p N ≤ Module.finrank (ZMod p) (TailIndex d → ZMod p) := by
    rw [hκ1, hdim]
    omega
  obtain ⟨f₂, f₃, f₄, hf₂, hf₃, hind⟩ := flag_family (capRed (p := p) d c N 1)
    (capRed (p := p) d c N 2) (capRed (p := p) d c N 3) (capRed_mono (by norm_num))
    (capRed_mono (by norm_num)) _ hG₁ind hS1 _ _ _ h2 h3 h4
  choose G₂ hG₂cap hG₂red using hf₂
  choose G₃ hG₃cap hG₃red using hf₃
  let G₄ : Fin (jointFourthRank d p N) → TailIndex d → ℤ_[p] := fun i j => liftZ (f₄ i j)
  let κ := ((CapOneIdx d p ⊕ Fin (simultaneousTwo d p)) ⊕ Fin (simultaneousThree d p N)) ⊕
    Fin (jointFourthRank d p N)
  let V : κ → TailIndex d → ℤ_[p] := Sum.elim (Sum.elim (Sum.elim G₁ G₂) G₃) G₄
  let w : κ → ℕ := Sum.elim (Sum.elim (Sum.elim (fun _ => 1) (fun _ => 2)) (fun _ => 3))
    (fun _ => 4)
  have hcapκ : ∀ t, Cap N (w t) (actualSourceSeries p d c (V t)) := by
    rintro (((i | i) | i) | i)
    · exact hG₁cap i
    · exact hG₂cap i
    · exact hG₃cap i
    · exact actualSourceSeries_cap (p := p) c
        (fun g => actual_germs_cap_four (by omega) c hc N hN g) _
  have hindκ : LinearIndependent (ZMod p) (fun t => redV (p := p) (TailIndex d) (V t)) := by
    have hfam : (fun t => redV (p := p) (TailIndex d) (V t)) =
        Sum.elim (Sum.elim (Sum.elim (fun i => redV (p := p) (TailIndex d) (G₁ i)) f₂) f₃) f₄ := by
      funext t
      rcases t with ((i | i) | i) | i
      · rfl
      · exact hG₂red i
      · exact hG₃red i
      · ext j
        exact toZMod_liftZ _
    rw [hfam]
    exact hind
  have hcardκ : Fintype.card κ = Fintype.card (TailIndex d) := by
    simp only [κ, Fintype.card_sum, Fintype.card_fin, hκ1]
    simp only [TailIndex, Fintype.card_prod, Fintype.card_fin]
    omega
  let e : κ ≃ TailIndex d := Fintype.equivOfCardEq hcardκ
  let U : Matrix (TailIndex d) (TailIndex d) ℤ_[p] := fun i j => V (e.symm j) i
  have hU : IsUnit U.det := isUnit_det_of_reduced_cols U (hindκ.comp e.symm e.symm.injective)
  have hcount : ∀ v : ℕ, (Finset.univ.filter (fun x : κ => w x = v)).card =
      (if 1 = v then simultaneousOne d p else 0) + (if 2 = v then simultaneousTwo d p else 0) +
        (if 3 = v then simultaneousThree d p N else 0) +
        (if 4 = v then jointFourthRank d p N else 0) := by
    intro v
    rw [card_filter_blocks, hκ1, Fintype.card_fin, Fintype.card_fin, Fintype.card_fin]
  refine ⟨U, w ∘ e.symm, hU, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    simp only [Function.comp]
    generalize e.symm j = t
    rcases t with ((t | t) | t) | t <;> simp [w]
  · intro j
    exact hcapκ (e.symm j)
  · rw [card_filter_equiv, hcount]; simp
  · rw [card_filter_equiv, hcount]; simp
  · rw [card_filter_equiv, hcount]; simp
  · rw [card_filter_equiv, hcount]; simp
  · intro r
    refine ⟨e (Sum.inl (Sum.inl (Sum.inl (Sum.inr r)))), ?_⟩
    ext i
    simp only [U, Equiv.symm_apply_apply, V, Sum.elim_inl, hG₁res]

/-- **The sharp local determinant estimate** for the unchanged `actualCommonDeterminant`:
`-v_p(det) ≤ sharpThreshold d p (7d + 176)`, paper (35). -/
theorem actualCommonDeterminant_sharp_bound (hp : 11 ≤ p) (c : ℚ) (hc : ¬p ∣ c.den) (d : ℕ)
    (hd : 2 ≤ d) (hN : 7 * d + 176 ≤ p^2) :
    -padicValRat p (actualCommonDeterminant d c) ≤ (sharpThreshold d p (7 * d + 176) : ℤ) := by
  obtain ⟨U, w, hU, hw, hcap, -, h2, h3, h4, -⟩ := compatible_integral_basis hp c hc d hd hN
  have hmain := actualCommonDeterminant_bound_of_compatible_caps d c hc U hU w
    (fun j => (hw j).2)
    (by
      intro i j
      rw [actualPrimeMatrix_mul_col]
      have h := hcap j
      unfold Cap at h
      exact h _ (actualTailRow_lt d c i))
  rw [thresholdMass_eq_sharpThreshold d p (7 * d + 176) hd w hw (by simp) h2 h3 h4] at hmain
  exact hmain

end Zeta7Auxiliary

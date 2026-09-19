import Zeta7Proof.AuxiliaryLayerCalculus
import Zeta7Proof.AuxiliaryP3Complete

/-! P6, joint fourth layer. On the whole actual integral source, the fourth layers lie in
`K₀(X^p)·𝔽_p[x]_{≤d+1} + W(X^p)·𝔽_p[x]_{≤d}` truncated below `N`; this uses
`hasseShortK_eq_carry` and the initial orders of `K₀, U, W`. The derivative block and the
`primitiveShifts d` shifts of `Z_{h⁺}` have cap three, so they lie in the fourth-layer kernel.
Together these give at least `6d - q_p` independent reductions of cap-three columns. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
namespace Zeta7Auxiliary
open PowerSeries Zeta7Common

variable {p : ℕ} [Fact p.Prime]

/-- Frobenius expansion `f ↦ f(X^p)`. -/
abbrev fexp (f : PowerSeries (ZMod p)) : PowerSeries (ZMod p) :=
  expand p (Fact.out : p.Prime).ne_zero f

/-- Multiplication of a polynomial by a fixed series. -/
def polyMulL (g : PowerSeries (ZMod p)) : Polynomial (ZMod p) →ₗ[ZMod p] PowerSeries (ZMod p) where
  toFun A := (A : PowerSeries (ZMod p)) * g
  map_add' A B := by rw [Polynomial.coe_add, add_mul]
  map_smul' a A := by
    rw [Polynomial.smul_eq_C_mul, Polynomial.coe_mul, Polynomial.coe_C, RingHom.id_apply,
      smul_eq_C_mul, mul_assoc]

/-! ### Vectors vanishing below an order -/

/-- The coordinate subspace of vectors supported in `[m, N)`. -/
def orderSpace (N m : ℕ) : Submodule (ZMod p) (Fin N → ZMod p) :=
  Submodule.span (ZMod p) (Set.range fun i : Fin (N - m) =>
    (Pi.single (⟨m + i.val, by omega⟩ : Fin N) 1 : Fin N → ZMod p))

theorem orderSpace_finrank (N m : ℕ) :
    Module.finrank (ZMod p) (orderSpace (p := p) N m) ≤ N - m :=
  (finrank_range_le_card _).trans (by rw [Fintype.card_fin])

theorem mem_orderSpace {N m : ℕ} (v : Fin N → ZMod p) (hv : ∀ n : Fin N, n.val < m → v n = 0) :
    v ∈ orderSpace (p := p) N m := by
  classical
  have hsum : v = ∑ i : Fin (N - m),
      v ⟨m + i.val, by omega⟩ • (Pi.single (⟨m + i.val, by omega⟩ : Fin N) 1 : Fin N → ZMod p) := by
    ext n
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one,
      mul_zero]
    by_cases hn : n.val < m
    · rw [hv n hn]
      symm
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [if_neg]
      intro h
      have := congrArg Fin.val h
      simp at this
      omega
    · rw [Finset.sum_eq_single ⟨n.val - m, by omega⟩]
      · rw [if_pos (Fin.ext (by simp; omega))]
        congr 1
        exact Fin.ext (by simp; omega)
      · intro i _ hi
        rw [if_neg]
        intro h
        apply hi
        have := congrArg Fin.val h
        simp at this
        exact Fin.ext (by simp; omega)
      · intro h
        exact absurd (Finset.mem_univ _) h
  rw [hsum]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem truncL_mul_mem_orderSpace (N m : ℕ) (A : Polynomial (ZMod p)) (g : PowerSeries (ZMod p))
    (hg : ∀ j, j < m → coeff j g = 0) :
    truncL N ((A : PowerSeries (ZMod p)) * g) ∈ orderSpace (p := p) N m := by
  apply mem_orderSpace
  intro n hn
  show coeff n.val ((A : PowerSeries (ZMod p)) * g) = 0
  rw [coeff_mul]
  refine Finset.sum_eq_zero fun ij hij => ?_
  have hs : ij.1 + ij.2 = n.val := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  rw [hg ij.2 (by omega), mul_zero]

/-! ### Initial orders of `K₀(X^p)` and `W(X^p)` -/

theorem hasseShortK_coeff_one (hp : 11 ≤ p) : coeff 1 (hasseShortK p (by omega)) = 0 := by
  rw [hasseShortK_eq_carry hp, map_add, coeff_C_mul, (carryU_initial hp).2.1,
    (carryW_initial hp).2.1]
  ring

theorem fexp_coeff_below {f : PowerSeries (ZMod p)} {k : ℕ} (hf : ∀ i, i < k → coeff i f = 0)
    (j : ℕ) (hj : j < k * p) : coeff j (fexp f) = 0 := by
  rw [coeff_expand]
  split_ifs with h
  · apply hf
    have hp0 := (Fact.out : p.Prime).pos
    rw [Nat.div_lt_iff_lt_mul hp0]
    exact hj
  · rfl

theorem fexpK_order (hp : 11 ≤ p) (j : ℕ) (hj : j < 2 * p) :
    coeff j (fexp (hasseShortK p (by omega))) = 0 := by
  apply fexp_coeff_below _ j hj
  intro i hi
  interval_cases i
  · exact hasseShortK_coeff_zero _
  · exact hasseShortK_coeff_one hp

theorem fexpW_order (hp : 11 ≤ p) (j : ℕ) (hj : j < 3 * p) :
    coeff j (fexp (carryW p)) = 0 := by
  apply fexp_coeff_below _ j hj
  intro i hi
  obtain ⟨h0, h1, h2, -⟩ := carryW_initial (p := p) hp
  interval_cases i
  · exact h0
  · exact h1
  · exact h2

/-! ### The fourth-layer target -/

/-- `K₀(X^p) 𝔽_p[x]_{<d+2}`, truncated below `N`. -/
def fourthK (hp : 11 ≤ p) (N d : ℕ) : Submodule (ZMod p) (Fin N → ZMod p) :=
  (Polynomial.degreeLT (ZMod p) (d + 2)).map
    (truncL N ∘ₗ polyMulL (fexp (hasseShortK p (by omega))))

/-- `W(X^p) 𝔽_p[x]_{<d+1}`, truncated below `N`. -/
def fourthW (N d : ℕ) : Submodule (ZMod p) (Fin N → ZMod p) :=
  (Polynomial.degreeLT (ZMod p) (d + 1)).map (truncL N ∘ₗ polyMulL (fexp (carryW p)))

/-- The joint fourth-layer target. -/
def fourthTarget (hp : 11 ≤ p) (N d : ℕ) : Submodule (ZMod p) (Fin N → ZMod p) :=
  fourthK hp N d ⊔ fourthW N d

theorem degreeLT_finrank (n : ℕ) :
    Module.finrank (ZMod p) (Polynomial.degreeLT (ZMod p) n) = n := by
  rw [(Polynomial.degreeLTEquiv (ZMod p) n).finrank_eq, Module.finrank_fin_fun]

theorem fourthK_finrank (hp : 11 ≤ p) (N d : ℕ) :
    Module.finrank (ZMod p) (fourthK hp N d) ≤ min (d + 2) (N - 2 * p) := by
  apply le_min
  · exact (Submodule.finrank_map_le _ _).trans (degreeLT_finrank (p := p) _).le
  · refine (Submodule.finrank_mono ?_).trans (orderSpace_finrank (p := p) N (2 * p))
    rintro _ ⟨A, -, rfl⟩
    exact truncL_mul_mem_orderSpace N _ A _ (fexpK_order hp)

theorem fourthW_finrank (hp : 11 ≤ p) (N d : ℕ) :
    Module.finrank (ZMod p) (fourthW (p := p) N d) ≤ min (d + 1) (N - 3 * p) := by
  apply le_min
  · exact (Submodule.finrank_map_le _ _).trans (degreeLT_finrank (p := p) _).le
  · refine (Submodule.finrank_mono ?_).trans (orderSpace_finrank (p := p) N (3 * p))
    rintro _ ⟨A, -, rfl⟩
    exact truncL_mul_mem_orderSpace N _ A _ (fexpW_order hp)

theorem fourthTarget_finrank (hp : 11 ≤ p) (N d : ℕ) :
    Module.finrank (ZMod p) (fourthTarget hp N d) ≤
      min (d + 2) (N - 2 * p) + min (d + 1) (N - 3 * p) :=
  (Submodule.finrank_add_le_finrank_add_finrank _ _).trans
    (Nat.add_le_add (fourthK_finrank hp N d) (fourthW_finrank hp N d))

theorem monomial_mem_degreeLT {n k : ℕ} (hk : k < n) (a : ZMod p) :
    Polynomial.C a * Polynomial.X ^ k ∈ Polynomial.degreeLT (ZMod p) n := by
  rw [Polynomial.mem_degreeLT]
  refine (Polynomial.degree_C_mul_X_pow_le k a).trans_lt ?_
  exact_mod_cast hk

theorem mem_fourthTarget (hp : 11 ≤ p) {N d : ℕ} (A B : Polynomial (ZMod p))
    (hA : A ∈ Polynomial.degreeLT (ZMod p) (d + 2)) (hB : B ∈ Polynomial.degreeLT (ZMod p) (d + 1))
    (F : PowerSeries (ZMod p))
    (hF : EqBelow N F ((A : PowerSeries (ZMod p)) * fexp (hasseShortK p (by omega)) +
      (B : PowerSeries (ZMod p)) * fexp (carryW p))) :
    truncL N F ∈ fourthTarget hp N d := by
  rw [truncL_congr hF, map_add]
  exact Submodule.add_mem_sup ⟨A, hA, rfl⟩ ⟨B, hB, rfl⟩

/-! ### Fourth layers of the actual germs -/

theorem actualGerms_three (c : ℚ) :
    actualGerms p c 3 = (quadratic rationalPotential (rationalH c)).map (algebraMap ℚ ℚ_[p]) := by
  simp [actualGerms, rationalGerms, germs]

theorem actualGerms_four (c : ℚ) :
    actualGerms p c 4 =
      (primitive (quadratic rationalPotential (rationalH c))).map (algebraMap ℚ ℚ_[p]) := by
  simp [actualGerms, rationalGerms, germs]

theorem actualGerms_five (c : ℚ) :
    actualGerms p c 5 =
      (primitive (primitive (quadratic rationalPotential (rationalH c)))).map
        (algebraMap ℚ ℚ_[p]) := by
  simp [actualGerms, rationalGerms, germs]

theorem lay_K_fourth (hp : 11 ≤ p) (c : ℚ) (hc : ¬p ∣ c.den) (N : ℕ) (hN : N ≤ p^2) :
    EqBelow N (laySeries 4 (actualGerms p c 3)) (fexp (hasseShortK p (by omega))) := by
  intro n hn
  rw [actualGerms_three, laySeries_eq_layer (rationalK_cap_four c hc N hN) ⟨n, hn⟩]
  exact actualK_fourth_frobenius hp c hc N hN n hn

theorem lay_J1_fourth (hp : 11 ≤ p) (c : ℚ) (hc : ¬p ∣ c.den) (N : ℕ) (hN : N ≤ p^2) :
    EqBelow N (laySeries 4 (actualGerms p c 4))
      (X * fexp (hasseShortK p (by omega)) + fexp (carryC1 p hp)) := by
  intro n hn
  rw [actualGerms_four, laySeries_eq_layer (rationalJ1_cap_four c hc N hN) ⟨n, hn⟩]
  exact actualJ1_fourth_frobenius hp c hc N hN n hn

theorem lay_J2_fourth (hp : 11 ≤ p) (c : ℚ) (hc : ¬p ∣ c.den) (N : ℕ) (hN : N ≤ p^2) :
    EqBelow N (laySeries 4 (actualGerms p c 5))
      (C (2⁻¹ : ZMod p) * (X ^ 2 * fexp (hasseShortK p (by omega))) +
        X * fexp (carryC1 p hp) + fexp (carryC2 p hp)) := by
  intro n hn
  rw [actualGerms_five, laySeries_eq_layer (rationalJ2_cap_four (by omega) c hc N hN) ⟨n, hn⟩]
  exact actualJ2_fourth_frobenius hp c hc N hN n hn

/-- `U = K₀ - 10 W` after expansion. -/
theorem fexp_carryU (hp : 11 ≤ p) :
    fexp (carryU p) = fexp (hasseShortK p (by omega)) - C 10 * fexp (carryW p) := by
  rw [hasseShortK_eq_carry hp]
  simp only [fexp, map_add, map_mul, expand_C]
  ring

theorem fexp_carryC1 (hp : 11 ≤ p) :
    fexp (carryC1 p hp) =
      -(C (carryCoeff hp (p-1)) * fexp (hasseShortK p (by omega))) +
        C (10 * carryCoeff hp (p-1) - carryCoeff hp (2*p-1)) * fexp (carryW p) := by
  have hU := fexp_carryU hp
  simp only [fexp] at hU ⊢
  rw [carryC1]
  simp only [map_sub, map_neg, map_mul, expand_C, hU]
  ring

theorem fexp_carryC2 (hp : 11 ≤ p) :
    fexp (carryC2 p hp) =
      C (2⁻¹ * carryCoeff hp (p-2)) * fexp (hasseShortK p (by omega)) +
        C (2⁻¹ * (carryCoeff hp (2*p-2) - 10 * carryCoeff hp (p-2))) * fexp (carryW p) := by
  have hU := fexp_carryU hp
  simp only [fexp] at hU ⊢
  rw [carryC2]
  simp only [map_add, map_mul, expand_C, hU, map_sub, map_ofNat]
  ring

/-- **Fourth layers of the shifted `K, J₁, J₂` germs lie in the joint target.** -/
theorem germ_fourth_mem (hp : 11 ≤ p) (c : ℚ) (hc : ¬p ∣ c.den) (N : ℕ) (hN : N ≤ p^2)
    (d : ℕ) (x : TailIndex d) :
    truncL N (laySeries 4 (X ^ x.2.val * actualGerms p c x.1)) ∈ fourthTarget hp N d := by
  obtain ⟨k, j⟩ := x
  have hj := j.isLt
  rw [lay_X_pow_mul]
  simp only
  have hCX : ∀ (a : ZMod p) (m : ℕ),
      ((Polynomial.C a * Polynomial.X ^ m : Polynomial (ZMod p)) : PowerSeries (ZMod p)) =
        C a * X ^ m := fun a m => by
    rw [Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_pow, Polynomial.coe_X]
  by_cases hk3 : k.val < 3
  · have hcap : Cap N 3 (actualGerms p c k) := by
      have := actual_germs_ordinary_caps (p := p) (by omega) c hc N hN k
      rw [ordinaryGermCap, if_pos hk3] at this
      exact this
    rw [truncL_congr ((EqBelow.refl N _).mul (lay_succ_zero hcap)), mul_zero, map_zero]
    exact Submodule.zero_mem _
  obtain ⟨kv, hkv⟩ := k
  simp only at hk3
  interval_cases kv
  · -- `K`
    refine mem_fourthTarget hp (Polynomial.C 1 * Polynomial.X ^ j.val) 0
      (monomial_mem_degreeLT (by omega) 1) (Submodule.zero_mem _) _ ?_
    refine ((EqBelow.refl N _).mul (lay_K_fourth hp c hc N hN)).trans (EqBelow.of_eq ?_)
    rw [hCX]
    simp
  · -- `J₁`
    refine mem_fourthTarget hp
      (Polynomial.C 1 * Polynomial.X ^ (j.val + 1) +
        Polynomial.C (-carryCoeff hp (p-1)) * Polynomial.X ^ j.val)
      (Polynomial.C (10 * carryCoeff hp (p-1) - carryCoeff hp (2*p-1)) * Polynomial.X ^ j.val)
      (Submodule.add_mem _ (monomial_mem_degreeLT (by omega) _)
        (monomial_mem_degreeLT (by omega) _))
      (monomial_mem_degreeLT (by omega) _) _ ?_
    refine ((EqBelow.refl N _).mul (lay_J1_fourth hp c hc N hN)).trans (EqBelow.of_eq ?_)
    rw [Polynomial.coe_add, hCX, hCX, hCX, fexp_carryC1 hp]
    simp only [map_neg, map_one, one_mul]
    ring
  · -- `J₂`
    refine mem_fourthTarget hp
      (Polynomial.C (2⁻¹) * Polynomial.X ^ (j.val + 2) +
        Polynomial.C (-carryCoeff hp (p-1)) * Polynomial.X ^ (j.val + 1) +
        Polynomial.C (2⁻¹ * carryCoeff hp (p-2)) * Polynomial.X ^ j.val)
      (Polynomial.C (10 * carryCoeff hp (p-1) - carryCoeff hp (2*p-1)) *
          Polynomial.X ^ (j.val + 1) +
        Polynomial.C (2⁻¹ * (carryCoeff hp (2*p-2) - 10 * carryCoeff hp (p-2))) *
          Polynomial.X ^ j.val)
      (Submodule.add_mem _ (Submodule.add_mem _ (monomial_mem_degreeLT (by omega) _)
        (monomial_mem_degreeLT (by omega) _)) (monomial_mem_degreeLT (by omega) _))
      (Submodule.add_mem _ (monomial_mem_degreeLT (by omega) _)
        (monomial_mem_degreeLT (by omega) _)) _ ?_
    refine ((EqBelow.refl N _).mul (lay_J2_fourth hp c hc N hN)).trans (EqBelow.of_eq ?_)
    rw [Polynomial.coe_add, Polynomial.coe_add, Polynomial.coe_add, hCX, hCX, hCX, hCX, hCX,
      fexp_carryC1 hp, fexp_carryC2 hp]
    simp only [map_neg]
    ring

/-! ### Standard source vectors -/

theorem actualSourceSeries_single (d : ℕ) (c : ℚ) (x : TailIndex d) :
    actualSourceSeries p d c (Pi.single x 1) = X ^ x.2.val * actualGerms p c x.1 := by
  classical
  rw [actualSourceSeries, Finset.sum_eq_single x]
  · simp
  · intro y _ hy
    simp [Pi.single_apply, hy]
  · intro h; exact absurd (Finset.mem_univ x) h

theorem redV_single {d : ℕ} (x : TailIndex d) :
    redV (p := p) (TailIndex d) (Pi.single x 1) = Pi.single x 1 := by
  ext j
  simp only [redV_apply, Pi.single_apply]
  split_ifs <;> simp

/-- **Joint fourth layer**: `6d ≤ dim(cap-three reductions) + rank bound`. -/
theorem capRed_three_from_fourth (hp : 11 ≤ p) (c : ℚ) (hc : ¬p ∣ c.den) (d N : ℕ)
    (hN : N ≤ p^2) :
    6 * d ≤ Module.finrank (ZMod p) (capRed (p := p) d c N 3) +
      (min (d + 2) (N - 2 * p) + min (d + 1) (N - 3 * p)) := by
  classical
  have h := capRed_kernel_bound (p := p) d c N 3 (fun x : TailIndex d => Pi.single x 1)
    (fun x => by
      rw [actualSourceSeries_single]
      exact (actualSourceSeries_cap (p := p) (d := 1) c
        (fun g => actual_germs_cap_four (by omega) c hc N hN g) (Pi.single (x.1, 0) 1)).mono_range
        le_rfl |> fun _ => ((actual_germs_cap_four (p := p) (by omega) c hc N hN x.1).X_pow_mul _))
    (by
      simp only [redV_single]
      exact Pi.linearIndependent_single_one (TailIndex d) (ZMod p))
    (fourthTarget hp N d)
    (fun x => by
      rw [actualSourceSeries_single]
      exact germ_fourth_mem hp c hc N hN d x)
  have hcard : Fintype.card (TailIndex d) = 6 * d := by simp
  rw [hcard] at h
  exact h.trans (Nat.add_le_add_left (fourthTarget_finrank hp N d) _)

/-! ### The derivative block and the `Z_{h⁺}` shifts have cap three -/

/-- The derivative standard vectors. -/
def dStd (d : ℕ) (x : DIdx d) : TailIndex d → ℤ_[p] := embedD (Pi.single x 1)

theorem capRed_three_from_shifts (hp : 11 ≤ p) (c : ℚ) (hc : ¬p ∣ c.den) (d N : ℕ)
    (hN : N ≤ p^2) :
    3 * d + primitiveShifts d ≤ Module.finrank (ZMod p) (capRed (p := p) d c N 3) := by
  classical
  let f := Sum.elim (fun x : DIdx d => redV (p := p) (TailIndex d) (dStd d x))
    (fun t : Fin (primitiveShifts d) => redV (p := p) (TailIndex d) (zFamily p d t))
  have hind : LinearIndependent (ZMod p) f := by
    apply linearIndependent_sum_of_proj _ _ (kPolyL (p := p) d)
    · have : (fun x : DIdx d => redV (p := p) (TailIndex d) (dStd d x)) =
          fun x => embedR d (Pi.single x 1) := by
        ext1 x
        rw [dStd, redV_embedD]
        congr 1
        ext y
        simp only [redV_apply, Pi.single_apply]
        split_ifs <;> simp
      rw [this]
      exact (Pi.linearIndependent_single_one (DIdx d) (ZMod p)).map' (embedR d) (embedR_ker d)
    · intro x
      exact kPolyL_embedD _
    · exact zFamily_kPoly_independent hp d
  have h := card_le_finrank_of_family (capRed (p := p) d c N 3) f hind (by
    rintro (x | t)
    · exact mem_capRed _ (embedD_cap_three hp c hc _ N hN)
    · exact mem_capRed _ (zFamily_cap_three hp c hc d N hN t))
  simpa [Fintype.card_sum] using h

/-- The cap-three `Z_{h⁺}` shifts lie in the fourth-layer kernel. -/
theorem zFamily_fourth_zero (hp : 11 ≤ p) (c : ℚ) (hc : ¬p ∣ c.den) (d N : ℕ) (hN : N ≤ p^2)
    (t : Fin (primitiveShifts d)) :
    EqBelow N (laySeries 4 (actualSourceSeries p d c (zFamily p d t))) 0 :=
  lay_succ_zero (zFamily_cap_three hp c hc d N hN t)

/-- **P6: joint fourth-rank bound.** At least `6d - q_p` independent reductions of actual
cap-three source vectors exist, where `q_p = jointFourthRank d p N`. -/
theorem capRed_three_bound (hp : 11 ≤ p) (c : ℚ) (hc : ¬p ∣ c.den) (d N : ℕ) (hd : 2 ≤ d)
    (hN : N ≤ p^2) :
    6 * d - jointFourthRank d p N ≤ Module.finrank (ZMod p) (capRed (p := p) d c N 3) := by
  have h1 := capRed_three_from_fourth hp c hc d N hN
  have h2 := capRed_three_from_shifts hp c hc d N hN
  unfold jointFourthRank
  unfold primitiveShifts at h2
  omega

end Zeta7Auxiliary

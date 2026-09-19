import Zeta7Proof.AuxiliaryGammaNumerators

/-! P6, joint third layer, for the actual source columns of the unchanged determinant.

The third layers of all `3d` derivative columns and of the `primitiveShifts d` shifts of
`Z_{h⁺}` lie in the single space
`{ trunc_N (A · P̄^{-(2σ+2)} · F(X^p)) : deg A < d + 4σ + 4 }`,
of dimension at most `b = derivativeBudget d p`. For the derivative columns this is (25) with
the numerators of `Γ, DΓ, D²Γ`; for `Z_{h⁺}` it is `p³ Z_{h⁺} ≡ ℰ F(X^p)` with
`ℰ = P̄^{-2σ} 𝒥(ā⁺)` and `deg 𝒥(ā⁺) ≤ 4σ + 2`. Kernel lifting then gives the joint bound on
cap-two reductions; the exact first kernel of P4 and the cap-one resonances give the other. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
namespace Zeta7Auxiliary
open PowerSeries Zeta7Common

variable {p : ℕ} [Fact p.Prime]

attribute [local irreducible] Cap

/-! ### Reductions of integral multipliers -/

theorem bandP_zpMap : (bandP : PowerSeries ℚ_[p]) = zpMap (p := p) (bandP : PowerSeries ℤ_[p]) := by
  simp [bandP, map_ofNat]

theorem bandW_zpMap : (bandW : PowerSeries ℚ_[p]) = zpMap (p := p) (bandW : PowerSeries ℤ_[p]) := by
  simp [bandW, map_ofNat]

theorem zred_bandP : zred p (bandP : PowerSeries ℤ_[p]) = bandP := by
  simp [bandP, map_ofNat]

theorem zred_bandW : zred p (bandW : PowerSeries ℤ_[p]) = bandW := by
  simp [bandW, map_ofNat]

theorem eqBelow_all_eq {f g : PowerSeries (ZMod p)} (h : ∀ N, EqBelow N f g) : f = g := by
  ext n
  exact h (n + 1) n (Nat.lt_succ_self n)

/-- The reduction of the actual potential is `V̄ = W̄ / P̄²`. -/
theorem laySeries_padicV : laySeries 0 (padicV p) = redV2 p := by
  have hB : ∀ N, EqBelow N ((bandP : PowerSeries (ZMod p)) ^ 2 * laySeries 0 (padicV p))
      bandW := by
    intro N
    have hcap : Cap N 0 ((bandP : PowerSeries ℚ_[p]) ^ 2) := by
      simpa [pow_two] using (bandP_padic_cap (p := p) N).mul (bandP_padic_cap N)
    have h1 := lay_mul hcap (padicV_cap (p := p) N)
    rw [padicV_band, bandW_zpMap, laySeries_zero_zpMap, zred_bandW] at h1
    have h2 : laySeries 0 ((bandP : PowerSeries ℚ_[p]) ^ 2) = (bandP : PowerSeries (ZMod p)) ^ 2 := by
      rw [bandP_zpMap, ← map_pow, laySeries_zero_zpMap, map_pow, zred_bandP]
    rw [h2] at h1
    exact h1.symm
  have h := eqBelow_all_eq hB
  have hu : IsUnit ((bandP : PowerSeries (ZMod p)) ^ 2) := (bandP_isUnit (R := ZMod p)).pow 2
  apply hu.mul_left_cancel
  rw [h, redV2_band]

/-- The reduced positive resonance `v̄⁺ = P̄ ā⁺`. -/
theorem laySeries_vPos :
    laySeries 0 (bandP * zpMap (p := p) (posA p)) =
      ((hassePolyP * redPosA p : Polynomial (ZMod p)) : PowerSeries (ZMod p)) := by
  rw [bandP_zpMap, ← map_mul, laySeries_zero_zpMap, map_mul, zred_bandP, bandP_zmod,
    ← posAPoly_coe, zred_coe, Polynomial.coe_mul, hassePolyP_coe']

/-! ### Layers of a concomitant -/

theorem concomitant_zero_eq {R : Type*} [CommRing R] (V f g : PowerSeries R) :
    concomitant V (0 : R) f g =
      euler (euler g) * f - euler g * euler f + g * euler (euler f) - (V * g) * f := by
  unfold concomitant
  simp only [thetaS_zero_eq]
  ring

theorem concomitant_congr {N : ℕ} (V g : PowerSeries (ZMod p)) {F F' : PowerSeries (ZMod p)}
    (h : EqBelow N F F') :
    EqBelow N (concomitant V (0 : ZMod p) F g) (concomitant V (0 : ZMod p) F' g) := by
  rw [concomitant_zero_eq, concomitant_zero_eq]
  exact ((((EqBelow.refl N _).mul h).sub ((EqBelow.refl N _).mul h.euler)).add
    ((EqBelow.refl N _).mul h.euler.euler)).sub ((EqBelow.refl N _).mul h)

theorem Cap.mul0 {N e : ℕ} {G F : PowerSeries ℚ_[p]} (hG : Cap N 0 G) (hF : Cap N e F) :
    Cap N e (G * F) := by
  have h := hG.mul hF
  rwa [zero_add] at h

/-- Layers of a concomitant with integral multipliers. -/
theorem lay_concomitant {N e : ℕ} {V F g : PowerSeries ℚ_[p]} (hV : Cap N 0 V) (hF : Cap N e F)
    (hg : Cap N 0 g) :
    EqBelow N (laySeries e (concomitant V (0 : ℚ_[p]) F g))
      (concomitant (laySeries 0 V) (0 : ZMod p) (laySeries e F) (laySeries 0 g)) := by
  rw [concomitant_zero_eq, concomitant_zero_eq]
  have h1 : Cap N e (euler (euler g) * F) := hg.euler.euler.mul0 hF
  have h2 : Cap N e (euler g * euler F) := hg.euler.mul0 hF.euler
  have h3 : Cap N e (g * euler (euler F)) := hg.mul0 hF.euler.euler
  have h4 : Cap N e (V * g * F) := (hV.mul0 hg).mul0 hF
  have h12 : Cap N e (euler (euler g) * F - euler g * euler F) := h1.sub h2
  have h123 : Cap N e (euler (euler g) * F - euler g * euler F + g * euler (euler F)) :=
    h12.add h3
  have s1 : EqBelow N
      (laySeries e (euler (euler g) * F - euler g * euler F + g * euler (euler F) - V * g * F))
      (laySeries e (euler (euler g) * F - euler g * euler F + g * euler (euler F)) -
        laySeries e (V * g * F)) := lay_sub h123 h4
  have s2 : EqBelow N
      (laySeries e (euler (euler g) * F - euler g * euler F + g * euler (euler F)))
      (laySeries e (euler (euler g) * F - euler g * euler F) +
        laySeries e (g * euler (euler F))) := lay_add h12 h3
  have s3 : EqBelow N (laySeries e (euler (euler g) * F - euler g * euler F))
      (laySeries e (euler (euler g) * F) - laySeries e (euler g * euler F)) := lay_sub h1 h2
  have e1 : EqBelow N (laySeries e (euler (euler g) * F))
      (euler (euler (laySeries 0 g)) * laySeries e F) :=
    (lay_mul hg.euler.euler hF).trans
      (((lay_euler hg.euler).trans (lay_euler hg).euler).mul (EqBelow.refl N _))
  have e2 : EqBelow N (laySeries e (euler g * euler F))
      (euler (laySeries 0 g) * euler (laySeries e F)) :=
    (lay_mul hg.euler hF.euler).trans ((lay_euler hg).mul (lay_euler hF))
  have e3 : EqBelow N (laySeries e (g * euler (euler F)))
      (laySeries 0 g * euler (euler (laySeries e F))) :=
    (lay_mul hg hF.euler.euler).trans
      ((EqBelow.refl N _).mul ((lay_euler hF.euler).trans (lay_euler hF).euler))
  have hVg : Cap N 0 (V * g) := hV.mul0 hg
  have e4 : EqBelow N (laySeries e (V * g * F))
      (laySeries 0 V * laySeries 0 g * laySeries e F) :=
    (lay_mul hVg hF).trans ((lay_mul hV hg).mul (EqBelow.refl N _))
  exact s1.trans ((s2.trans ((s3.trans (e1.sub e2)).add e3)).sub e4)

/-! ### The joint third-layer target -/

/-- `F(X^p)`, the reduced short Frobenius series. -/
abbrev fShort (p : ℕ) [Fact p.Prime] : PowerSeries (ZMod p) := fexp (hasseShortSeries p)

/-- The joint third-layer space: `trunc_N (A P̄^{-(2σ+2)} F(X^p))`, `deg A < b`. -/
def thirdTarget (p : ℕ) [Fact p.Prime] (N d : ℕ) : Submodule (ZMod p) (Fin N → ZMod p) :=
  (Polynomial.degreeLT (ZMod p) (derivativeBudget d p)).map
    (truncL N ∘ₗ polyMulL (Pinv p ^ (gm p + 2) * fShort p))

theorem thirdTarget_finrank (N d : ℕ) :
    Module.finrank (ZMod p) (thirdTarget p N d) ≤ derivativeBudget d p :=
  (Submodule.finrank_map_le _ _).trans (degreeLT_finrank (p := p) _).le

theorem mem_thirdTarget {N d : ℕ} (A : Polynomial (ZMod p)) (hA : A.natDegree < derivativeBudget d p)
    (F : PowerSeries (ZMod p))
    (hF : EqBelow N F ((A : PowerSeries (ZMod p)) * (Pinv p ^ (gm p + 2) * fShort p))) :
    truncL N F ∈ thirdTarget p N d := by
  rw [truncL_congr hF]
  refine ⟨A, (?_ : A ∈ Polynomial.degreeLT (ZMod p) (derivativeBudget d p)), rfl⟩
  rw [Polynomial.mem_degreeLT]
  exact Polynomial.degree_le_natDegree.trans_lt (by exact_mod_cast hA)

omit [Fact p.Prime] in
theorem budget_eq (d : ℕ) : derivativeBudget d p = d + 2 * gm p + 4 := by
  unfold derivativeBudget gm
  ring

/-- The third layers of `H, DH, D²H`. -/
theorem lay_H_third (hp : 11 ≤ p) (c : ℚ) (hc : ¬p ∣ c.den) (N : ℕ) (hN : N ≤ p^2) :
    EqBelow N (laySeries 3 (padicH p c)) (hasseGammaSeries p (by omega) * fShort p) := by
  intro n hn
  rw [laySeries_eq_layer (rationalH_cap_three c hc N hN) ⟨n, hn⟩]
  exact rationalH_third_layer_gamma hp c hc N hN ⟨n, hn⟩

theorem lay_H_third_iter (hp : 11 ≤ p) (c : ℚ) (hc : ¬p ∣ c.den) (N : ℕ) (hN : N ≤ p^2)
    (k : Fin 3) :
    EqBelow N (laySeries 3 ((euler^[k.val]) (padicH p c)))
      ((euler^[k.val]) (hasseGammaSeries p (by omega)) * fShort p) := by
  intro n hn
  fin_cases k
  · exact lay_H_third hp c hc N hN n hn
  · show coeff n (laySeries 3 (euler (padicH p c))) =
      coeff n (euler (hasseGammaSeries p (by omega)) * fShort p)
    rw [laySeries_eq_layer (rationalH_cap_three c hc N hN).euler ⟨n, hn⟩]
    exact (rationalH_third_jets_gamma hp c hc N hN ⟨n, hn⟩).1
  · show coeff n (laySeries 3 (euler (euler (padicH p c)))) =
      coeff n (euler (euler (hasseGammaSeries p (by omega))) * fShort p)
    rw [laySeries_eq_layer (rationalH_cap_three c hc N hN).euler.euler ⟨n, hn⟩]
    exact (rationalH_third_jets_gamma hp c hc N hN ⟨n, hn⟩).2

theorem actualGerms_derivative (c : ℚ) (k : Fin 3) :
    actualGerms p c ⟨k.val, by omega⟩ = (euler^[k.val]) (padicH p c) := by
  obtain ⟨g0, g1, g2, -⟩ := actualGerms_six (p := p) c
  fin_cases k
  · exact g0
  · exact g1
  · exact g2

theorem embedD_single {d : ℕ} (x : DIdx d) :
    (embedD (Pi.single x 1) : TailIndex d → ℤ_[p]) = Pi.single (⟨x.1.val, by omega⟩, x.2) 1 := by
  classical
  obtain ⟨xk, xj⟩ := x
  ext ⟨k, j⟩
  by_cases hk : k.val < 3
  · simp only [embedD, dif_pos hk, Pi.single_apply, Prod.mk.injEq, Fin.ext_iff]
  · simp only [embedD, dif_neg hk, Pi.single_apply, Prod.mk.injEq, Fin.ext_iff]
    rw [if_neg]
    intro h
    exact hk (by have := xk.isLt; omega)

/-- **Third layers of the derivative columns.** -/
theorem dStd_third_mem (hp : 11 ≤ p) (c : ℚ) (hc : ¬p ∣ c.den) (N : ℕ) (hN : N ≤ p^2)
    (d : ℕ) (x : DIdx d) :
    truncL N (laySeries 3 (actualSourceSeries p d c (dStd d x))) ∈ thirdTarget p N d := by
  obtain ⟨k, j⟩ := x
  rw [dStd, embedD_single, actualSourceSeries_single]
  simp only
  rw [actualGerms_derivative, lay_X_pow_mul]
  refine mem_thirdTarget (Polynomial.X ^ j.val * gammaNum p (by omega) k) ?_ _ ?_
  · have h1 := gammaNum_natDegree hp k
    have h2 : (Polynomial.X ^ j.val * gammaNum p (by omega) k).natDegree ≤ j.val + (gammaNum p (by omega) k).natDegree :=
      natDegree_mul_le' (Polynomial.natDegree_X_pow_le _) le_rfl
    rw [budget_eq]
    have := j.isLt
    omega
  · refine ((EqBelow.refl N _).mul (lay_H_third_iter hp c hc N hN k)).trans (EqBelow.of_eq ?_)
    rw [eulerIter_gamma, Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_X]
    ring

/-- **Third layers of the `Z_{h⁺}` shifts**: `p³ x^t Z_{h⁺} ≡ x^t ℰ F(X^p)`. -/
theorem zFamily_third_mem (hp : 11 ≤ p) (c : ℚ) (hc : ¬p ∣ c.den) (N : ℕ) (hN : N ≤ p^2)
    (d : ℕ) (t : Fin (primitiveShifts d)) :
    truncL N (laySeries 3 (actualSourceSeries p d c (zFamily p d t))) ∈ thirdTarget p N d := by
  rw [zFamily, zSrc_series c (zFamily_bound t), lay_X_pow_mul]
  refine mem_thirdTarget
    (Polynomial.X ^ t.val * (hassePolyP ^ 2 * Jpoly p (by omega) (redPosA p))) ?_ _ ?_
  · have hJ := Jpoly_posA_natDegree (p := p) hp
    have hP := hassePolyP_natDegree_le (p := p)
    have h1 : (hassePolyP ^ 2 * Jpoly p (by omega) (redPosA p)).natDegree ≤ 4 + (2 * gm p + 2) :=
      natDegree_mul_le' (Polynomial.natDegree_pow_le.trans (by omega)) hJ
    have h2 : (Polynomial.X ^ t.val * (hassePolyP ^ 2 * Jpoly p (by omega) (redPosA p))).natDegree ≤
        t.val + (4 + (2 * gm p + 2)) :=
      natDegree_mul_le' (Polynomial.natDegree_X_pow_le _) h1
    have := zFamily_bound t
    rw [budget_eq]
    omega
  · have hz : zPart c (posH p) = resY c 0 (posH p) (posA p) +
        concomitant (padicV p) (0 : ℚ_[p]) (padicH p c) (bandP * zpMap (p := p) (posA p)) := by
      rw [resY]; simp
    have hY : Cap N 1 (resY c 0 (posH p) (posA p)) := posY_cap_one hp c hc N hN
    have hH : Cap N 3 (padicH p c) := rationalH_cap_three c hc N hN
    have hconc := concomitant_cap_three c hc N hN _ (vTilde_cap (p := p) (posA p) N)
    have hlay : EqBelow N (laySeries 3 (zPart c (posH p)))
        (fShort p * concomitant (redV2 p) (0 : ZMod p) (hasseGammaSeries p (by omega))
          (((hassePolyP * redPosA p : Polynomial (ZMod p))) : PowerSeries (ZMod p))) := by
      rw [hz]
      refine (lay_add ((hY.mono (by norm_num : 1 ≤ 3))) hconc).trans ?_
      have hY0 : EqBelow N (laySeries 3 (resY c 0 (posH p) (posA p))) 0 :=
        lay_succ_zero (hY.mono (by norm_num : 1 ≤ 2))
      refine (hY0.add (lay_concomitant (padicV_cap N) hH (vTilde_cap (posA p) N))).trans ?_
      rw [zero_add, laySeries_padicV, laySeries_vPos]
      refine (concomitant_congr _ _ (lay_H_third hp c hc N hN)).trans (EqBelow.of_eq ?_)
      rw [concomitant_zero_eq, concomitant_zero_eq]
      have hE : euler (fShort p) = 0 := by
        have := euler_mul_expand (p := p) 1 (hasseShortSeries p)
        simpa [euler_one_zmod] using this
      have hEM : ∀ M : PowerSeries (ZMod p), euler (M * fShort p) = euler M * fShort p :=
        fun M => euler_mul_expand (p := p) M (hasseShortSeries p)
      simp only [hEM]
      ring
    refine ((EqBelow.refl N _).mul hlay).trans (EqBelow.of_eq ?_)
    rw [gamma_concomitant_pos hp]
    simp only [Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_X]
    ring

/-! ### The joint bound -/

theorem dz_independent (hp : 11 ≤ p) (d : ℕ) :
    LinearIndependent (ZMod p) (Sum.elim
      (fun x : DIdx d => redV (p := p) (TailIndex d) (dStd d x))
      (fun t : Fin (primitiveShifts d) => redV (p := p) (TailIndex d) (zFamily p d t))) := by
  classical
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

/-- **P6: joint third-layer bound.** The kernel of the combined third-image map of all derivative
columns and all `s` shifts of `Z_{h⁺}` lifts to cap two. -/
theorem capRed_two_from_third (hp : 11 ≤ p) (c : ℚ) (hc : ¬p ∣ c.den) (d N : ℕ)
    (hN : N ≤ p^2) :
    3 * d + primitiveShifts d ≤ Module.finrank (ZMod p) (capRed (p := p) d c N 2) +
      derivativeBudget d p := by
  classical
  let G : DIdx d ⊕ Fin (primitiveShifts d) → TailIndex d → ℤ_[p] :=
    Sum.elim (fun x => dStd d x) (fun t => zFamily p d t)
  have h := capRed_kernel_bound (p := p) d c N 2 G
    (by
      rintro (x | t)
      · exact embedD_cap_three hp c hc _ N hN
      · exact zFamily_cap_three hp c hc d N hN t)
    (by
      convert dz_independent (p := p) hp d using 1
      ext1 i
      rcases i with x | t <;> rfl)
    (thirdTarget p N d)
    (by
      rintro (x | t)
      · exact dStd_third_mem hp c hc N hN d x
      · exact zFamily_third_mem hp c hc N hN d t)
  have hcard : Fintype.card (DIdx d ⊕ Fin (primitiveShifts d)) = 3 * d + primitiveShifts d := by
    simp [Fintype.card_sum]
  rw [hcard] at h
  exact h.trans (Nat.add_le_add_left (thirdTarget_finrank N d) _)

/-! ### Cap-two and cap-one reductions from P4 and the resonances -/

theorem derivative_resonance_independent (hp : 11 ≤ p) (d : ℕ) {κ : Type*}
    (Y : κ → DIdx d → ℤ_[p])
    (hY : LinearIndependent (ZMod p) (fun j => redV (p := p) (DIdx d) (Y j))) :
    LinearIndependent (ZMod p) (Sum.elim
      (fun j => redV (p := p) (TailIndex d) (embedD (Y j)))
      (fun i => redV (p := p) (TailIndex d) (resFamily p d i))) := by
  apply linearIndependent_sum_of_proj _ _ (kPolyL (p := p) d)
  · have : (fun j => redV (p := p) (TailIndex d) (embedD (Y j))) =
        fun j => embedR d (redV (p := p) (DIdx d) (Y j)) := by
      ext1 j; exact redV_embedD _
    rw [this]
    exact hY.map' (embedR d) (embedR_ker d)
  · intro j
    exact kPolyL_embedD _
  · exact resFamily_kPoly_independent hp d

/-- Cap-two reductions: the exact first kernel of P4 together with the resonance columns. -/
theorem capRed_two_from_resonance (hp : 11 ≤ p) (c : ℚ) (hc : ¬p ∣ c.den) (d N : ℕ)
    (hd : 1 ≤ d) (hN : N ≤ p^2) :
    3 * d - derivativeThree d p + resonanceShifts d p ≤
      Module.finrank (ZMod p) (capRed (p := p) d c N 2) := by
  classical
  obtain ⟨k, c₁, m, Y, Z, hsum, hb, hnk, hY0, hY1, hind⟩ := derivative_block hp d hd
  have hYind : LinearIndependent (ZMod p) (fun j => redV (p := p) (DIdx d) (Y j)) := by
    exact hind.comp Sum.inl Sum.inl_injective
  have h := card_le_finrank_of_family (capRed (p := p) d c N 2) _
    (derivative_resonance_independent hp d Y hYind) (by
      rintro (j | i)
      · exact mem_capRed _ (embedD_cap_two hp c hc _ (hY0 j) N hN)
      · exact mem_capRed _ ((resFamily_cap_one hp c hc d N hN i).mono (by norm_num)))
  have hcount := resCount_eq (by omega : 2 ≤ p) d
  simp only [Fintype.card_sum, Fintype.card_fin] at h
  unfold derivativeThree at *
  omega

/-- Cap-one reductions: the lifted reduced first kernel of P4 together with the resonances. -/
theorem capRed_one_bound (hp : 11 ≤ p) (c : ℚ) (hc : ¬p ∣ c.den) (d N : ℕ)
    (hd : 1 ≤ d) (hN : N ≤ p^2) :
    simultaneousOne d p ≤ Module.finrank (ZMod p) (capRed (p := p) d c N 1) := by
  classical
  obtain ⟨k, c₁, m, Y, Z, hsum, hb, hnk, hY0, hY1, hind⟩ := derivative_block hp d hd
  have hYind : LinearIndependent (ZMod p)
      (fun j : Fin k => redV (p := p) (DIdx d) (Y (Sum.inl j))) := by
    exact hind.comp (fun j : Fin k => Sum.inl (Sum.inl j))
      (Sum.inl_injective.comp Sum.inl_injective)
  have h := card_le_finrank_of_family (capRed (p := p) d c N 1) _
    (derivative_resonance_independent hp d (fun j : Fin k => Y (Sum.inl j)) hYind) (by
      rintro (j | i)
      · exact mem_capRed _ (embedD_cap_one hp c hc _ (hY0 _) (hY1 j) N hN)
      · exact mem_capRed _ (resFamily_cap_one hp c hc d N hN i))
  have hcount := resCount_eq (by omega : 2 ≤ p) d
  simp only [Fintype.card_sum, Fintype.card_fin] at h
  unfold simultaneousOne derivativeOne derivativeTwo derivativeThree derivativeBudget at *
  omega

/-- **Joint cap-two bound**: at least `3d + s - b₀` independent cap-two reductions,
`b₀ = jointThirdRank d p`. -/
theorem capRed_two_bound (hp : 11 ≤ p) (c : ℚ) (hc : ¬p ∣ c.den) (d N : ℕ)
    (hd : 1 ≤ d) (hN : N ≤ p^2) :
    3 * d + primitiveShifts d - jointThirdRank d p ≤
      Module.finrank (ZMod p) (capRed (p := p) d c N 2) := by
  have h1 := capRed_two_from_third hp c hc d N hN
  have h2 := capRed_two_from_resonance hp c hc d N hd hN
  have h3 := resonanceShifts_le_primitiveShifts d p
  have h4 : derivativeThree d p ≤ 3 * d := min_le_left _ _
  unfold jointThirdRank
  omega

end Zeta7Auxiliary

import Zeta7Proof.AuxiliaryResonanceSource

/-! P5, item 7 (continued): the primitive (`K`-germ) projections of the reduced resonance
source vectors, their independence, the exact shift intervals and the count
`resonanceShifts d p`, and the `primitiveShifts d` shifts of `Z_{h⁺}`. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
namespace Zeta7Auxiliary
open PowerSeries Zeta7Main Zeta7Common

variable {p : ℕ} [Fact p.Prime]

/-! ### The primitive projection -/

/-- The polynomial carried by the `K`-germ coordinates of a reduced source vector. -/
def kPolyL (d : ℕ) : (TailIndex d → ZMod p) →ₗ[ZMod p] Polynomial (ZMod p) where
  toFun w := ∑ i : Fin d, Polynomial.C (w (3, i)) * Polynomial.X ^ (i : ℕ)
  map_add' a b := by simp [add_mul, Finset.sum_add_distrib]
  map_smul' c a := by
    simp [Finset.smul_sum, Polynomial.smul_eq_C_mul, mul_assoc]

theorem redV_polySrc {d : ℕ} (Q : Fin 6 → Polynomial ℤ_[p]) (j : TailIndex d) :
    redV (p := p) (TailIndex d) (polySrc d Q) j = PadicInt.toZMod ((Q j.1).coeff j.2) := rfl

theorem kPolyL_polySrc {d : ℕ} (Q : Fin 6 → Polynomial ℤ_[p]) (hQ : (Q 3).natDegree < d) :
    kPolyL (p := p) d (redV (p := p) (TailIndex d) (polySrc d Q)) = redZ p (Q 3) := by
  have hd : (redZ p (Q 3)).natDegree < d := Polynomial.natDegree_map_le.trans_lt hQ
  conv_rhs => rw [Polynomial.as_sum_range' (redZ p (Q 3)) d hd]
  rw [← Fin.sum_univ_eq_sum_range]
  simp only [kPolyL, LinearMap.coe_mk, AddHom.coe_mk]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [redV_polySrc, ← Polynomial.C_mul_X_pow_eq_monomial]
  simp [Polynomial.coeff_map]

theorem kPolyL_embedD {d : ℕ} (x : DIdx d → ℤ_[p]) :
    kPolyL (p := p) d (redV (p := p) (TailIndex d) (embedD x)) = 0 := by
  simp only [kPolyL, LinearMap.coe_mk, AddHom.coe_mk]
  refine Finset.sum_eq_zero fun i _ => ?_
  have h0 : redV (p := p) (TailIndex d) (embedD x) (3, i) = 0 := by
    rw [redV_apply]
    simp [embedD]
  rw [h0, map_zero, zero_mul]

/-- The reduced primitive vector `u₀ = P̄ h̄⁺` (first primitive coordinate). -/
def resU (p : ℕ) [Fact p.Prime] : Polynomial (ZMod p) := redZ p (intPolyP p) * redZ p (posH p)

theorem hassePolyP_ne_zero' : redZ p (intPolyP p) ≠ 0 := by
  rw [redZ_intPolyP]; exact hassePolyP_ne_zero_zmod

theorem resU_ne_zero (hp : 11 ≤ p) : resU p ≠ 0 :=
  mul_ne_zero hassePolyP_ne_zero' (posH_red_ne_zero hp)

theorem kPoly_posSrc (hp : 11 ≤ p) {d t : ℕ} (ht : t + p + 2 < d) :
    kPolyL (p := p) d (redV (p := p) (TailIndex d) (posSrc (p := p) d t)) =
      Polynomial.X ^ t * resU p := by
  rw [posSrc, kPolyL_polySrc]
  · show redZ p (Polynomial.X ^ t * (intPolyP p * Polynomial.X ^ 0 * posH p)) = _
    simp [resU]
  · have := shiftQ_natDegree t _ (posQ_natDegree hp) 3
    omega

theorem kPoly_negSrc (hp : 11 ≤ p) {d t : ℕ} (ht : t + p + 4 < d) :
    kPolyL (p := p) d (redV (p := p) (TailIndex d) (negSrc (p := p) d t)) =
      Polynomial.C (resLambda p hp) * (Polynomial.X ^ (p + t) * resU p) := by
  rw [negSrc, kPolyL_polySrc]
  · show redZ p (Polynomial.X ^ t * (intPolyP p * Polynomial.X ^ p * negH p)) = _
    have hX : redZ p (Polynomial.X : Polynomial ℤ_[p]) = Polynomial.X := Polynomial.map_X _
    rw [map_mul, map_mul, map_mul, map_pow, map_pow, hX,
      (resonance_proportional hp).2.1, resU, pow_add]
    ring
  · have := shiftQ_natDegree t _ (negQ_natDegree (p := p)) 3
    omega

theorem kPoly_zSrc {d t : ℕ} (ht : t + 2 < d) :
    kPolyL (p := p) d (redV (p := p) (TailIndex d) (zSrc (p := p) d t)) =
      Polynomial.X ^ t * redZ p (posH p) := by
  rw [zSrc, kPolyL_polySrc]
  · show redZ p (Polynomial.X ^ t * posH p) = _
    simp
  · have := shiftQ_natDegree t _ (zQ_natDegree (posH p) posH_natDegree) 3
    omega

/-! ### Independence of shifted multiples -/

/-- Shifts of a fixed nonzero polynomial, with nonzero scalars, are independent. -/
theorem shifts_independent {K : Type*} [Field K] {ι : Type*} (τ : ι → ℕ)
    (hτ : Function.Injective τ) (u : Polynomial K) (hu : u ≠ 0) (w : ι → Kˣ) :
    LinearIndependent K (fun i => (w i : K) • (Polynomial.X ^ τ i * u)) := by
  have hmon : LinearIndependent K (fun n : ℕ => (Polynomial.X ^ n : Polynomial K)) := by
    have := (Polynomial.basisMonomials K).linearIndependent
    rw [Polynomial.coe_basisMonomials] at this
    convert this using 1
    ext1 n
    exact Polynomial.X_pow_eq_monomial n
  have h1 := (hmon.comp τ hτ).map' (LinearMap.mulRight K u)
    (LinearMap.ker_eq_bot.mpr (mul_left_injective₀ hu))
  exact h1.units_smul w

/-- Independence of a sum family whose second part is detected by a projection that kills the
first part. -/
theorem linearIndependent_sum_of_proj {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] {ι κ : Type*} [Fintype κ]
    (f : ι → V) (g : κ → V) (π : V →ₗ[K] W) (hf : LinearIndependent K f)
    (hπf : ∀ i, π (f i) = 0) (hg : LinearIndependent K (fun j => π (g j))) :
    LinearIndependent K (Sum.elim f g) := by
  classical
  have hg' : LinearIndependent K g := LinearIndependent.of_comp π hg
  apply hf.sum_type hg'
  rw [Submodule.disjoint_def]
  intro x hx hy
  have hker : x ∈ LinearMap.ker π := by
    have hle : Submodule.span K (Set.range f) ≤ LinearMap.ker π := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact hπf i
    exact hle hx
  obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hy
  rw [LinearMap.mem_ker, map_sum] at hker
  simp only [map_smul] at hker
  have ha := (linearIndependent_iff'.mp hg) Finset.univ a hker
  simp [ha]

/-! ### The resonance family and its shift intervals -/

/-- Number of permitted positive shifts actually selected: `[0, min(p, t⁺))`. -/
def resPosCount (d p : ℕ) : ℕ := min p (d - p - 2)

/-- Number of permitted negative shifts: `[p, p + t⁻)`, with `t⁻ = (d - p - 4)₊`. -/
def resNegCount (d p : ℕ) : ℕ := d - p - 4

omit [Fact p.Prime] in
/-- **Exact count (32)**: the selected distinct shifts number `resonanceShifts d p`. -/
theorem resCount_eq (hp : 2 ≤ p) (d : ℕ) :
    resPosCount d p + resNegCount d p = resonanceShifts d p := by
  unfold resPosCount resNegCount resonanceShifts
  omega

/-- The primitive shift position of a selected resonance column. -/
def resPos (d p : ℕ) : Fin (resPosCount d p) ⊕ Fin (resNegCount d p) → ℕ :=
  Sum.elim (fun j => j.val) (fun j => p + j.val)

theorem resPos_injective (d p : ℕ) : Function.Injective (resPos d p) := by
  rintro (i | i) (j | j) h <;> simp only [resPos, Sum.elim_inl, Sum.elim_inr] at h
  · exact congrArg Sum.inl (Fin.ext h)
  · have := i.isLt; unfold resPosCount at this; omega
  · have := j.isLt; unfold resPosCount at this; omega
  · exact congrArg Sum.inr (Fin.ext (by omega))

omit [Fact p.Prime] in
/-- Every selected shift position is below `d - 4`, so `P` times it stays below `d - 2`. -/
theorem resPos_lt (hp : 2 ≤ p) (d : ℕ) (i : Fin (resPosCount d p) ⊕ Fin (resNegCount d p)) :
    resPos d p i + 4 < d := by
  rcases i with i | i
  · have := i.isLt; unfold resPosCount at this; simp only [resPos, Sum.elim_inl]; omega
  · have := i.isLt; unfold resNegCount at this; simp only [resPos, Sum.elim_inr]; omega

/-- The selected actual resonance columns: `x^j C⁺` and `x^j C⁻`. -/
def resFamily (p : ℕ) [Fact p.Prime] (d : ℕ) :
    Fin (resPosCount d p) ⊕ Fin (resNegCount d p) → (TailIndex d → ℤ_[p]) :=
  Sum.elim (fun j => posSrc (p := p) d j.val) (fun j => negSrc (p := p) d j.val)

theorem resFamily_pos_bound {d p : ℕ} (j : Fin (resPosCount d p)) : j.val + p + 2 < d := by
  have := j.isLt; unfold resPosCount at this; omega

theorem resFamily_neg_bound {d p : ℕ} (j : Fin (resNegCount d p)) : j.val + p + 4 < d := by
  have := j.isLt; unfold resNegCount at this; omega

/-- All selected resonance columns have cap one. -/
theorem resFamily_cap_one (hp : 11 ≤ p) (c : ℚ) (hc : ¬p ∣ c.den) (d : ℕ)
    (N : ℕ) (hN : N ≤ p^2) (i : Fin (resPosCount d p) ⊕ Fin (resNegCount d p)) :
    Cap N 1 (actualSourceSeries p d c (resFamily p d i)) := by
  rcases i with j | j
  · exact posSrc_cap_one hp c hc (resFamily_pos_bound j) N hN
  · exact negSrc_cap_one hp c hc (resFamily_neg_bound j) N hN

/-- The resonance scalar in front of the shifted `u₀`. -/
def resScalar (p : ℕ) [Fact p.Prime] (hp : 11 ≤ p) (d : ℕ) :
    Fin (resPosCount d p) ⊕ Fin (resNegCount d p) → (ZMod p)ˣ :=
  Sum.elim (fun _ => 1) (fun _ => Units.mk0 (resLambda p hp) (resLambda_ne_zero hp))

/-- **Primitive reductions**: every selected column projects to a nonzero multiple of
`x^τ P̄ h̄⁺`, with `τ` its shift position. -/
theorem kPoly_resFamily (hp : 11 ≤ p) (d : ℕ)
    (i : Fin (resPosCount d p) ⊕ Fin (resNegCount d p)) :
    kPolyL (p := p) d (redV (p := p) (TailIndex d) (resFamily p d i)) =
      ((resScalar p hp d i : ZMod p)) • (Polynomial.X ^ resPos d p i * resU p) := by
  rcases i with j | j
  · simp only [resFamily, resScalar, resPos, Sum.elim_inl, Units.val_one, one_smul]
    exact kPoly_posSrc hp (resFamily_pos_bound j)
  · simp only [resFamily, resScalar, resPos, Sum.elim_inr, Units.val_mk0]
    rw [kPoly_negSrc hp (resFamily_neg_bound j), Polynomial.smul_eq_C_mul]

/-- **Independence of the selected resonance projections.** -/
theorem resFamily_kPoly_independent (hp : 11 ≤ p) (d : ℕ) :
    LinearIndependent (ZMod p)
      (fun i => kPolyL (p := p) d (redV (p := p) (TailIndex d) (resFamily p d i))) := by
  simp only [kPoly_resFamily hp d]
  exact shifts_independent (resPos d p) (resPos_injective d p) _ (resU_ne_zero hp) _

/-! ### The primitive shifts of `Z_{h⁺}` -/

/-- The `primitiveShifts d = d - 2` shifts `x^t Z_{h⁺}`, `t < d - 2`. -/
def zFamily (p : ℕ) [Fact p.Prime] (d : ℕ) : Fin (primitiveShifts d) → (TailIndex d → ℤ_[p]) :=
  fun t => zSrc (p := p) d t.val

theorem zFamily_bound {d : ℕ} (t : Fin (primitiveShifts d)) : t.val + 2 < d := by
  have := t.isLt; unfold primitiveShifts at this; omega

theorem zFamily_cap_three (hp : 11 ≤ p) (c : ℚ) (hc : ¬p ∣ c.den) (d : ℕ)
    (N : ℕ) (hN : N ≤ p^2) (t : Fin (primitiveShifts d)) :
    Cap N 3 (actualSourceSeries p d c (zFamily p d t)) :=
  zSrc_cap_three hp c hc (zFamily_bound t) N hN

/-- **Independent primitive projections of the shifts of `Z_{h⁺}`.** -/
theorem zFamily_kPoly_independent (hp : 11 ≤ p) (d : ℕ) :
    LinearIndependent (ZMod p)
      (fun t => kPolyL (p := p) d (redV (p := p) (TailIndex d) (zFamily p d t))) := by
  have h := shifts_independent (fun t : Fin (primitiveShifts d) => t.val) Fin.val_injective
    (redZ p (posH p)) (posH_red_ne_zero hp) (fun _ => 1)
  simp only [Units.val_one, one_smul] at h
  convert h using 1
  ext1 t
  exact kPoly_zSrc (zFamily_bound t)

/-- **Resonance projections lie in the span of the `Z_{h⁺}` projections** (paper, end of P5):
`x^τ P̄ h̄⁺` is a combination of `x^{τ}, x^{τ+1}, x^{τ+2}` times `h̄⁺`, all permitted shifts. -/
theorem resFamily_kPoly_mem_span (hp : 11 ≤ p) (d : ℕ)
    (i : Fin (resPosCount d p) ⊕ Fin (resNegCount d p)) :
    kPolyL (p := p) d (redV (p := p) (TailIndex d) (resFamily p d i)) ∈
      Submodule.span (ZMod p)
        (Set.range fun t => kPolyL (p := p) d (redV (p := p) (TailIndex d) (zFamily p d t))) := by
  have hlt := resPos_lt (by omega) d i
  rw [kPoly_resFamily hp d]
  apply Submodule.smul_mem
  have hP := intPolyP_natDegree (p := p)
  have hPd : (redZ p (intPolyP p)).natDegree ≤ 2 := Polynomial.natDegree_map_le.trans hP
  have hexp : Polynomial.X ^ resPos d p i * resU p =
      ∑ k ∈ Finset.range 3, (redZ p (intPolyP p)).coeff k •
        (Polynomial.X ^ (resPos d p i + k) * redZ p (posH p)) := by
    conv_lhs => rw [resU, Polynomial.as_sum_range' (redZ p (intPolyP p)) 3 (by omega)]
    simp only [Finset.sum_mul, Finset.mul_sum, Polynomial.smul_eq_C_mul, pow_add,
      ← Polynomial.C_mul_X_pow_eq_monomial]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [hexp]
  refine Submodule.sum_mem _ fun k hk => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  have hk3 := Finset.mem_range.mp hk
  refine ⟨⟨resPos d p i + k, by unfold primitiveShifts; omega⟩, ?_⟩
  exact kPoly_zSrc (t := resPos d p i + k) (by omega)

end Zeta7Auxiliary

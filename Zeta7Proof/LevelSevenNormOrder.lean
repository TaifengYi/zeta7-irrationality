import Zeta7Proof.LevelSevenNorm

/-! The translated factors of the norm use the common width-seven parameter. -/
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open Matrix.SpecialLinearGroup UpperHalfPlane Function Filter
open scoped MatrixGroups ModularForm Manifold
namespace Zeta7LevelSeven

theorem principal_seven_le_Gamma0 :
    CongruenceSubgroup.Gamma 7 ≤ CongruenceSubgroup.Gamma0 7 := by
  intro γ hγ
  exact CongruenceSubgroup.Gamma0_mem.mpr (CongruenceSubgroup.Gamma_mem.mp hγ).2.2.1

def slashPrincipal {k : ℤ} (f : ModularForm GammaSeven k) (γ : SL(2, ℤ)) :
    SlashInvariantForm (CongruenceSubgroup.Gamma 7) k where
  toFun := (f : ℍ → ℂ) ∣[k] mapGL ℝ γ
  slash_action_eq' δ hδ := by
    obtain ⟨d, hd, rfl⟩ := hδ
    have hconj : γ * d * γ⁻¹ ∈ CongruenceSubgroup.Gamma0 7 :=
      principal_seven_le_Gamma0 ((CongruenceSubgroup.Gamma_normal 7).conj_mem d hd γ)
    have hf := SlashInvariantForm.slash_action_eqn f (mapGL ℝ (γ * d * γ⁻¹))
      (show mapGL ℝ (γ * d * γ⁻¹) ∈ GammaSeven from ⟨_, hconj, rfl⟩)
    rw [← SlashAction.slash_mul]
    calc
      _ = ((f : ℍ → ℂ) ∣[k] mapGL ℝ (γ * d * γ⁻¹)) ∣[k] mapGL ℝ γ := by
        rw [← SlashAction.slash_mul]
        simp [map_mul, map_inv, mul_assoc]
      _ = _ := by rw [hf]

theorem slash_periodic_seven {k : ℤ} (f : ModularForm GammaSeven k) (γ : SL(2, ℤ)) :
    Periodic (((f : ℍ → ℂ) ∣[k] mapGL ℝ γ) ∘ ofComplex) 7 := by
  exact SlashInvariantFormClass.periodic_comp_ofComplex (slashPrincipal f γ)
    (by simp [CongruenceSubgroup.strictPeriods_Gamma])

theorem slash_cusp_seven_analytic {k : ℤ} (f : ModularForm GammaSeven k)
    (γ : SL(2, ℤ)) :
    AnalyticAt ℂ (cuspFunction 7 ((f : ℍ → ℂ) ∣[k] mapGL ℝ γ)) 0 := by
  apply analyticAt_cuspFunction_zero (by norm_num) (slash_periodic_seven f γ)
    ((ModularFormClass.holo f).slash k (mapGL ℝ γ))
  exact ModularFormClass.bdd_at_infty_slash f γ

theorem quotientFactor_cusp_seven_analytic {k : ℤ} (f : ModularForm GammaSeven k)
    (q : 𝒮ℒ ⧸ GammaSeven.subgroupOf 𝒮ℒ) :
    AnalyticAt ℂ (cuspFunction 7 (SlashInvariantForm.quotientFunc f q)) 0 := by
  induction q using Quotient.inductionOn with
  | h g =>
    obtain ⟨γ, hγ⟩ := g.property
    rw [SlashInvariantForm.quotientFunc_mk, ← hγ, ← map_inv]
    exact slash_cusp_seven_analytic f γ⁻¹

theorem cuspFunction_finsetProd_analytic {ι : Type*} (s : Finset ι) (f : ι → ℍ → ℂ)
    (hf : ∀ i ∈ s, AnalyticAt ℂ (cuspFunction 7 (f i)) 0) :
    AnalyticAt ℂ (cuspFunction 7 (∏ i ∈ s, f i)) 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h : cuspFunction 7 (1 : ℍ → ℂ) = 1 := by
      simpa [cuspFunction, Periodic.cuspFunction] using!
        (tendsto_const_nhds.mono_left nhdsWithin_le_nhds).limUnder_eq
    simp only [Finset.prod_empty, h]
    change AnalyticAt ℂ (fun _ : ℂ => (1 : ℂ)) 0
    exact analyticAt_const
  | @insert i s hi ih =>
    have ha := hf i (Finset.mem_insert_self i s)
    have hb := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    rw [Finset.prod_insert hi, cuspFunction_mul ha.continuousAt hb.continuousAt]
    exact ha.mul hb

theorem qExpansion_finsetProd_seven {ι : Type*} (s : Finset ι) (f : ι → ℍ → ℂ)
    (hf : ∀ i ∈ s, AnalyticAt ℂ (cuspFunction 7 (f i)) 0) :
    qExpansion 7 (∏ i ∈ s, f i) = ∏ i ∈ s, qExpansion 7 (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [qExpansion_one]
  | @insert i s hi ih =>
    have ha := hf i (Finset.mem_insert_self i s)
    have hb := fun j hj => hf j (Finset.mem_insert_of_mem hj)
    rw [Finset.prod_insert hi, Finset.prod_insert hi,
      qExpansion_mul ha (cuspFunction_finsetProd_analytic s f hb), ih hb]

theorem norm_qExpansion_seven {k : ℤ} (f : ModularForm GammaSeven k) :
    qExpansion 7 (levelSevenNorm f) =
      letI := Fintype.ofFinite (𝒮ℒ ⧸ GammaSeven.subgroupOf 𝒮ℒ)
      ∏ q : 𝒮ℒ ⧸ GammaSeven.subgroupOf 𝒮ℒ,
        qExpansion 7 (SlashInvariantForm.quotientFunc f q) := by
  classical
  letI := Fintype.ofFinite (𝒮ℒ ⧸ GammaSeven.subgroupOf 𝒮ℒ)
  change qExpansion 7 (∏ q : 𝒮ℒ ⧸ GammaSeven.subgroupOf 𝒮ℒ,
    SlashInvariantForm.quotientFunc f q) = _
  exact qExpansion_finsetProd_seven Finset.univ _
    (fun q _ => quotientFactor_cusp_seven_analytic f q)

theorem qExpansion_seven_dvd_norm {k : ℤ} (f : ModularForm GammaSeven k) :
    qExpansion 7 f ∣ qExpansion 7 (levelSevenNorm f) := by
  classical
  letI := Fintype.ofFinite (𝒮ℒ ⧸ GammaSeven.subgroupOf 𝒮ℒ)
  rw [norm_qExpansion_seven]
  have h := Finset.dvd_prod_of_mem
    (fun q : 𝒮ℒ ⧸ GammaSeven.subgroupOf 𝒮ℒ =>
      qExpansion 7 (SlashInvariantForm.quotientFunc f q))
    (Finset.mem_univ (⟦(1 : 𝒮ℒ)⟧ : 𝒮ℒ ⧸ GammaSeven.subgroupOf 𝒮ℒ))
  simpa using h

/-- Includes the zero case: the comparison takes place in `ℕ∞`. -/
theorem order_le_levelSevenNorm {k : ℤ} (f : ModularForm GammaSeven k) :
    (qExpansion 1 f).order ≤ (qExpansion 1 (levelSevenNorm f)).order := by
  obtain ⟨g, hg⟩ := qExpansion_seven_dvd_norm f
  have ho : (qExpansion 7 f).order ≤ (qExpansion 7 (levelSevenNorm f)).order := by
    rw [hg, PowerSeries.order_mul]
    exact le_self_add
  have hf := qExpansion_seven_of_one
    (SlashInvariantFormClass.periodic_comp_ofComplex f
      (by simp [GammaSeven, CongruenceSubgroup.strictPeriods_Gamma0]))
    (ModularFormClass.holo f) (ModularFormClass.bdd_at_infty f)
  have hn := qExpansion_seven_of_one
    (SlashInvariantFormClass.periodic_comp_ofComplex (levelSevenNorm f) (by simp))
    (ModularFormClass.holo (levelSevenNorm f))
    (ModularFormClass.bdd_at_infty (levelSevenNorm f))
  rw [hf, hn, PowerSeries.order_expand, PowerSeries.order_expand,
    nsmul_eq_mul, nsmul_eq_mul] at ho
  exact (ENat.mul_le_mul_left_iff (by norm_num : (7 : ℕ∞) ≠ 0) (by simp)).mp ho

/-- The weight-ten level-seven vanishing theorem, via the genuine weight-eighty norm. -/
theorem weightTen_eq_zero_of_order (f : ModularForm GammaSeven 10)
    (hf : (7 : ℕ∞) ≤ (qExpansion 1 f).order) : f = 0 := by
  apply (levelSevenNorm_eq_zero_iff f).mp
  apply ModularForm.sturm_bound_levelOne_nat (k := 80)
  exact lt_of_lt_of_le (by norm_num : ((80 / 12 : ℕ) : ℕ∞) < 7)
    (hf.trans (order_le_levelSevenNorm f))

end Zeta7LevelSeven

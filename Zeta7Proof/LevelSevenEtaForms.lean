import Zeta7Proof.LevelSevenEtaCharacter

/-! Actual analytic eta quotients, with their Γ₀(7) transformation laws.
Holomorphy at the cusps is a separate obligation; the slash-invariant forms here
do not purport to package that obligation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open Complex hiding eta
open ModularForm UpperHalfPlane
open Matrix.SpecialLinearGroup HeckeRing.GL2
open scoped MatrixGroups ModularForm Manifold
namespace Zeta7LevelSeven

def etaTwoSeven (τ : ℍ) : ℂ := etaTwo (levelRaiseMatrix 7 • τ)
def etaCoordinate (τ : ℍ) : ℂ := etaTwoSeven τ ^ 2 / etaTwo τ ^ 2
def phi (i : Fin 3) (τ : ℍ) : ℂ :=
  etaTwo τ ^ (3 - 2 * (i.val : ℤ)) * etaTwoSeven τ ^ (3 + 2 * (i.val : ℤ))

theorem etaTwoSeven_value (τ : ℍ) : etaTwoSeven τ = eta (7 * (τ : ℂ)) ^ 2 := by
  simp [etaTwoSeven, etaTwo, coe_levelRaiseMatrix_smul]

theorem etaTwoSeven_ne_zero (τ : ℍ) : etaTwoSeven τ ≠ 0 := etaTwo_ne_zero _

theorem etaCoordinate_value (τ : ℍ) :
    etaCoordinate τ = eta (7 * (τ : ℂ)) ^ 4 / eta τ ^ 4 := by
  simp [etaCoordinate, etaTwoSeven_value, etaTwo, ← pow_mul]

theorem phi_value (i : Fin 3) (τ : ℍ) :
    phi i τ = eta τ ^ (6 - 4 * (i.val : ℤ)) *
      eta (7 * (τ : ℂ)) ^ (6 + 4 * (i.val : ℤ)) := by
  simp only [phi, etaTwo, etaTwoSeven_value, ← zpow_natCast, ← zpow_mul]
  congr 2 <;> ring

theorem phi_ne_zero (i : Fin 3) (τ : ℍ) : phi i τ ≠ 0 :=
  mul_ne_zero (zpow_ne_zero _ (etaTwo_ne_zero τ)) (zpow_ne_zero _ (etaTwoSeven_ne_zero τ))

theorem phi_eq_phi_zero_mul_coordinate (i : Fin 3) (τ : ℍ) :
    phi i τ = phi 0 τ * etaCoordinate τ ^ i.val := by
  fin_cases i <;>
    norm_num [phi, etaCoordinate, zpow_neg, zpow_ofNat]
  all_goals field_simp [etaTwo_ne_zero τ]
  all_goals try ring
  all_goals
    have hc : etaTwo τ ^ 4 * (etaTwo τ)⁻¹ ^ 4 = 1 := by
      calc
        _ = (etaTwo τ * (etaTwo τ)⁻¹) ^ 4 := by ring
        _ = 1 := by rw [mul_inv_cancel₀ (etaTwo_ne_zero τ)]; norm_num
    linear_combination -(etaTwoSeven τ ^ 7) * hc

theorem eta_seven_differentiableAt {z : ℂ} (hz : 0 < z.im) :
    DifferentiableAt ℂ (fun w : ℂ ↦ eta (7 * w)) z := by
  have h7 : 0 < (7 * z).im := by simp; linarith
  exact (differentiableAt_eta_of_mem_upperHalfPlaneSet h7).comp z
    (differentiableAt_id.const_mul (7 : ℂ))

theorem phi_holo (i : Fin 3) : MDiff (phi i) := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  refine DifferentiableOn.congr (f := fun z : ℂ ↦
    eta z ^ (6 - 4 * (i.val : ℤ)) * eta (7 * z) ^ (6 + 4 * (i.val : ℤ))) ?_ ?_
  · intro z hz
    change 0 < z.im at hz
    have h7 : 0 < (7 * z).im := by simp; linarith
    exact (((differentiableAt_eta_of_mem_upperHalfPlaneSet hz).zpow
      (Or.inl (eta_ne_zero hz))).mul ((eta_seven_differentiableAt hz).zpow
      (Or.inl (eta_ne_zero h7)))).differentiableWithinAt
  · intro z hz
    simp [phi_value, ofComplex_apply_of_im_pos hz]

theorem etaCoordinate_holo : MDiff etaCoordinate := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  refine DifferentiableOn.congr (f := fun z : ℂ ↦ eta (7 * z) ^ 4 / eta z ^ 4) ?_ ?_
  · intro z hz
    exact ((eta_seven_differentiableAt hz).pow 4 |>.div
      ((differentiableAt_eta_of_mem_upperHalfPlaneSet hz).pow 4)
      (pow_ne_zero 4 (eta_ne_zero hz))).differentiableWithinAt
  · intro z hz
    simp [etaCoordinate_value, ofComplex_apply_of_im_pos hz]

theorem etaTwoSeven_eq_levelRaise : etaTwoSeven = levelRaiseFun 7 1 etaTwo := by
  ext τ
  exact (levelRaiseFun_apply 7 1 etaTwo τ).symm

theorem etaTwoSeven_slash (γ : CongruenceSubgroup.Gamma0 7) {μ : ℂ}
    (h : etaTwo ∣[(1 : ℤ)] sevenConjHom γ = μ • etaTwo) :
    etaTwoSeven ∣[(1 : ℤ)] γ.val = μ • etaTwoSeven := by
  rw [etaTwoSeven_eq_levelRaise, SL_slash]
  change levelRaiseFun 7 1 etaTwo ∣[(1 : ℤ)] mapGL ℝ γ.val = _
  rw [slash_mapGL_levelRaiseFun 7 1 γ.val
    ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (CongruenceSubgroup.Gamma0_mem.mp γ.property))]
  change levelRaiseFun 7 1 (etaTwo ∣[(1 : ℤ)] sevenConjHom γ) = _
  rw [h]
  ext τ
  simp [levelRaiseFun_apply]

theorem weight_one_value {f : ℍ → ℂ} {γ : SL(2, ℤ)} {μ : ℂ}
    (h : f ∣[(1 : ℤ)] γ = μ • f) (τ : ℍ) :
    f (γ • τ) = μ * denom γ τ * f τ := by
  have ht := congrFun h τ
  rw [SL_slash_apply] at ht
  simp only [Pi.smul_apply, smul_eq_mul, zpow_neg_one] at ht
  have hd := denom_ne_zero (mapGL ℝ γ) τ
  field_simp [hd] at ht
  linear_combination ht

theorem etaCoordinate_slash (γ : CongruenceSubgroup.Gamma0 7) :
    etaCoordinate ∣[(0 : ℤ)] γ.val = etaCoordinate := by
  obtain ⟨μ, hμ, h, h7⟩ := etaTwo_correlated γ
  have h7' := etaTwoSeven_slash γ h7
  have hn : μ ≠ 0 := by intro hz; simpa [hz] using hμ
  have hp : μ ^ 14 = μ ^ 2 := by calc
    μ ^ 14 = μ ^ 12 * μ ^ 2 := by ring
    _ = μ ^ 2 := by rw [hμ, one_mul]
  ext τ
  simp only [SL_slash_apply, neg_zero, zpow_zero, mul_one, etaCoordinate]
  rw [weight_one_value h7' τ, weight_one_value h τ]
  field_simp [hn, denom_ne_zero (mapGL ℝ γ.val) τ, etaTwo_ne_zero τ]
  ring_nf
  rw [hμ, one_mul]

theorem phi_slash (i : Fin 3) (γ : CongruenceSubgroup.Gamma0 7) :
    phi i ∣[(6 : ℤ)] γ.val = phi i := by
  obtain ⟨μ, hμ, h, h7⟩ := etaTwo_correlated γ
  have h7' := etaTwoSeven_slash γ h7
  have hn : μ ≠ 0 := by intro hz; simpa [hz] using hμ
  have hp24 : μ ^ 24 = 1 := by
    calc
      μ ^ 24 = (μ ^ 12) ^ 2 := by ring
      _ = 1 := by rw [hμ]; norm_num
  have hp36 : μ ^ 36 = 1 := by
    calc
      μ ^ 36 = (μ ^ 12) ^ 3 := by ring
      _ = 1 := by rw [hμ]; norm_num
  have hp48 : μ ^ 48 = 1 := by
    calc
      μ ^ 48 = (μ ^ 12) ^ 4 := by ring
      _ = 1 := by rw [hμ]; norm_num
  have hp49 : μ ^ 49 = μ := by
    calc
      μ ^ 49 = (μ ^ 12) ^ 4 * μ := by ring
      _ = μ := by rw [hμ]; simp
  ext τ
  simp only [SL_slash_apply, phi]
  rw [weight_one_value h τ, weight_one_value h7' τ]
  fin_cases i <;> norm_num only [Fin.val_zero, Fin.val_one, Fin.val_two, Int.reduceMul,
    Int.reduceAdd, Int.reduceSub, zpow_ofNat, zpow_neg, zpow_one]
  all_goals
    field_simp [hn, denom_ne_zero (mapGL ℝ γ.val) τ, etaTwo_ne_zero τ]
    ring_nf
    simp [hp24, hp36, hp48, hp49]

def phiSlashInvariant (i : Fin 3) :
    SlashInvariantForm (CongruenceSubgroup.Gamma0 7 : Subgroup (GL (Fin 2) ℝ)) 6 where
  toFun := phi i
  slash_action_eq' γ hγ := by
    obtain ⟨δ, hδ, rfl⟩ := hγ
    simpa [SL_slash, mapGL] using phi_slash i ⟨δ, hδ⟩

theorem phi_periodic (i : Fin 3) : Function.Periodic (phi i ∘ ofComplex) 1 := by
  exact SlashInvariantFormClass.periodic_comp_ofComplex (phiSlashInvariant i)
    (by simp [CongruenceSubgroup.strictPeriods_Gamma0])

def coordinateSlashInvariant :
    SlashInvariantForm (CongruenceSubgroup.Gamma0 7 : Subgroup (GL (Fin 2) ℝ)) 0 where
  toFun := etaCoordinate
  slash_action_eq' γ hγ := by
    obtain ⟨δ, hδ, rfl⟩ := hγ
    simpa [SL_slash, mapGL] using etaCoordinate_slash ⟨δ, hδ⟩

theorem etaCoordinate_periodic : Function.Periodic (etaCoordinate ∘ ofComplex) 1 := by
  exact SlashInvariantFormClass.periodic_comp_ofComplex coordinateSlashInvariant
    (by simp [CongruenceSubgroup.strictPeriods_Gamma0])

end Zeta7LevelSeven

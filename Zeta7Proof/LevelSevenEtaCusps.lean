import Zeta7Proof.LevelSevenEtaForms

/-! Actual Euler products in the cusp parameters. Integer powers are retained
throughout, including the inverse Euler factor of Φ₂. -/
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open Complex hiding eta
open ModularForm
open UpperHalfPlane hiding I
open Filter Function
open scoped Real Topology ModularForm Manifold
namespace Zeta7LevelSeven

def analyticEuler (q : ℂ) : ℂ := ∏' n : ℕ, (1 - q ^ (n + 1))

theorem analyticEuler_zero : analyticEuler 0 = 1 := by simp [analyticEuler]

theorem analyticEuler_analyticAt_zero : AnalyticAt ℂ analyticEuler 0 := by
  exact differentiableOn_tprod_one_sub_pow.analyticAt (Metric.ball_mem_nhds _ zero_lt_one)

theorem eta_zpow_euler (z : ℂ) (a : ℤ) :
    eta z ^ a = exp ((a : ℂ) * (2 * π * I * z / 24)) *
      analyticEuler (Periodic.qParam 1 z) ^ a := by
  simp only [eta, mul_zpow, Periodic.qParam, ← exp_int_mul, eta_q, analyticEuler]
  norm_num

theorem qParam_one_seven (z : ℂ) :
    Periodic.qParam 1 (7 * z) = Periodic.qParam 1 z ^ 7 := by
  simp only [Periodic.qParam, ← exp_nat_mul]
  congr 1
  norm_num
  ring

/-- Exact identity for the actual eta products, before any Taylor comparison. -/
theorem eta_product_expansion (z : ℂ) (a b : ℤ) (n : ℕ)
    (hab : a + 7 * b = 24 * n) :
    eta z ^ a * eta (7 * z) ^ b = Periodic.qParam 1 z ^ n *
      (analyticEuler (Periodic.qParam 1 z) ^ a *
        analyticEuler (Periodic.qParam 1 z ^ 7) ^ b) := by
  rw [eta_zpow_euler, eta_zpow_euler, qParam_one_seven]
  rw [mul_mul_mul_comm, ← exp_add]
  congr 1
  rw [Periodic.qParam, ← exp_nat_mul]
  have hab' : (a : ℂ) + 7 * b = 24 * n := by exact_mod_cast hab
  norm_num only [ofReal_one, div_one, Nat.cast_ofNat]
  congr 1
  linear_combination (2 * π * I * z / 24) * hab'

def phiUnit (i : Fin 3) (q : ℂ) : ℂ :=
  analyticEuler q ^ (6 - 4 * (i.val : ℤ)) *
    analyticEuler (q ^ 7) ^ (6 + 4 * (i.val : ℤ))

theorem phiUnit_zero (i : Fin 3) : phiUnit i 0 = 1 := by
  simp [phiUnit, analyticEuler_zero]

theorem phiUnit_continuousAt_zero (i : Fin 3) : ContinuousAt (phiUnit i) 0 := by
  have he := analyticEuler_analyticAt_zero.continuousAt
  have he7 : ContinuousAt (fun q : ℂ ↦ analyticEuler (q ^ 7)) 0 := by
    exact he.comp_of_eq ((continuousAt_id : ContinuousAt (fun z : ℂ ↦ z) 0).pow 7) (by simp)
  exact (he.zpow₀ _ (Or.inl (by simp [analyticEuler_zero]))).mul
    (he7.zpow₀ _ (Or.inl (by simp [analyticEuler_zero])))

theorem phi_q_expansion (i : Fin 3) (τ : ℍ) :
    phi i τ = Periodic.qParam 1 τ ^ (2 + i.val) * phiUnit i (Periodic.qParam 1 τ) := by
  rw [phi_value]
  exact eta_product_expansion τ _ _ _ (by omega)

/-- The nonzero leading factor at infinity. This also covers the negative eta exponent. -/
theorem phi_cusp_infty_leading (i : Fin 3) :
    Tendsto (fun τ : ℍ ↦ phi i τ / Periodic.qParam 1 τ ^ (2 + i.val))
      atImInfty (𝓝 1) := by
  have h := (phiUnit_continuousAt_zero i).tendsto.comp
    (qParam_tendsto_atImInfty (by norm_num : (0 : ℝ) < 1))
  simp only [phiUnit_zero] at h
  convert h using 1
  ext τ
  change phi i τ / Periodic.qParam 1 τ ^ (2 + i.val) = phiUnit i (Periodic.qParam 1 τ)
  rw [phi_q_expansion]
  field_simp [Periodic.qParam, exp_ne_zero]

theorem phi_tendsto_zero (i : Fin 3) : Tendsto (phi i) atImInfty (𝓝 0) := by
  have hq := qParam_tendsto_atImInfty (by norm_num : (0 : ℝ) < 1)
  have he := (phiUnit_continuousAt_zero i).tendsto.comp hq
  have h := (hq.pow (2 + i.val)).mul he
  simpa only [Function.comp_apply, ← phi_q_expansion, zero_pow (by omega : 2 + i.val ≠ 0), zero_mul] using h

theorem phi_bounded_at_infty (i : Fin 3) : IsBoundedAtImInfty (phi i) :=
  (show IsZeroAtImInfty (phi i) from phi_tendsto_zero i).isBoundedAtImInfty

theorem phi_cusp_analytic (i : Fin 3) : AnalyticAt ℂ (cuspFunction 1 (phi i)) 0 :=
  analyticAt_cuspFunction_zero (by norm_num) (phi_periodic i) (phi_holo i)
    (phi_bounded_at_infty i)

def divSeven (τ : ℍ) : ℍ := ⟨(τ : ℂ) / 7, by simpa using τ.im_pos⟩

theorem etaTwoSeven_S_value (τ : ℍ) :
    etaTwoSeven (ModularGroup.S • τ) = -I * ((τ : ℂ) / 7) * etaTwo (divSeven τ) := by
  rw [etaTwoSeven_value, modular_S_smul]
  convert etaTwo_S_value (divSeven τ) using 2
  · change eta (7 * (-(τ : ℂ))⁻¹) = eta (-1 / ((τ : ℂ) / 7))
    congr 1
    field_simp
  · rfl

/-- The S transform uses the width-seven parameter; its eta exponents are reversed. -/
theorem phi_S_value (i : Fin 3) (τ : ℍ) :
    (phi i ∣[(6 : ℤ)] ModularGroup.S) τ =
      -(7 : ℂ) ^ (-(3 + 2 * (i.val : ℤ))) *
        (etaTwo τ ^ (3 - 2 * (i.val : ℤ)) *
          etaTwo (divSeven τ) ^ (3 + 2 * (i.val : ℤ))) := by
  have hy : etaTwo (ModularGroup.S • τ) = -I * τ * etaTwo τ := by
    simpa [denom, ModularGroup.S] using weight_one_value etaTwo_S τ
  rw [SL_slash_apply]
  simp only [phi, hy, etaTwoSeven_S_value]
  have hd : denom ModularGroup.S τ = (τ : ℂ) := by simp [denom, ModularGroup.S]
  rw [hd]
  fin_cases i <;> norm_num only [Fin.val_zero, Fin.val_one, Fin.val_two, Int.reduceMul,
    Int.reduceAdd, Int.reduceSub, zpow_ofNat, zpow_neg, zpow_one]
  all_goals
    field_simp [τ.ne_zero, etaTwo_ne_zero τ]
    ring_nf
    simp [I_sq]

def phiZeroUnit (i : Fin 3) (q : ℂ) : ℂ :=
  analyticEuler (q ^ 7) ^ (6 - 4 * (i.val : ℤ)) *
    analyticEuler q ^ (6 + 4 * (i.val : ℤ))

theorem phiZeroUnit_zero (i : Fin 3) : phiZeroUnit i 0 = 1 := by
  simp [phiZeroUnit, analyticEuler_zero]

theorem phiZeroUnit_continuousAt_zero (i : Fin 3) : ContinuousAt (phiZeroUnit i) 0 := by
  have he := analyticEuler_analyticAt_zero.continuousAt
  have he7 : ContinuousAt (fun q : ℂ ↦ analyticEuler (q ^ 7)) 0 :=
    he.comp_of_eq ((continuousAt_id : ContinuousAt (fun z : ℂ ↦ z) 0).pow 7) (by simp)
  exact (he7.zpow₀ _ (Or.inl (by simp [analyticEuler_zero]))).mul
    (he.zpow₀ _ (Or.inl (by simp [analyticEuler_zero])))

theorem qParam_divSeven (τ : ℍ) : Periodic.qParam 1 (divSeven τ) = Periodic.qParam 7 τ := by
  simp [Periodic.qParam, divSeven]
  congr 1
  ring

theorem phi_S_q_expansion (i : Fin 3) (τ : ℍ) :
    (phi i ∣[(6 : ℤ)] ModularGroup.S) τ =
      -(7 : ℂ) ^ (-(3 + 2 * (i.val : ℤ))) *
        (Periodic.qParam 7 τ ^ (2 - i.val) * phiZeroUnit i (Periodic.qParam 7 τ)) := by
  rw [phi_S_value]
  congr 1
  have h := eta_product_expansion (divSeven τ) (6 + 4 * (i.val : ℤ))
    (6 - 4 * (i.val : ℤ)) (2 - i.val) (by have := i.isLt; omega)
  have he : eta (7 * (divSeven τ : ℂ)) = eta τ := by
    congr 1
    change 7 * ((τ : ℂ) / 7) = (τ : ℂ)
    ring
  rw [he, qParam_divSeven] at h
  conv_lhs => simp only [etaTwo, ← zpow_natCast, ← zpow_mul]
  norm_num only [Nat.cast_ofNat]
  rw [show (2 : ℤ) * (3 - 2 * i.val) = 6 - 4 * i.val by ring,
    show (2 : ℤ) * (3 + 2 * i.val) = 6 + 4 * i.val by ring]
  simpa only [phiZeroUnit, mul_comm] using h

theorem phi_cusp_zero_leading (i : Fin 3) :
    Tendsto (fun τ : ℍ ↦ (phi i ∣[(6 : ℤ)] ModularGroup.S) τ /
      Periodic.qParam 7 τ ^ (2 - i.val)) atImInfty
      (𝓝 (-(7 : ℂ) ^ (-(3 + 2 * (i.val : ℤ))))) := by
  have h := (phiZeroUnit_continuousAt_zero i).tendsto.comp
    (qParam_tendsto_atImInfty (by norm_num : (0 : ℝ) < 7))
  have hc := h.const_mul (-(7 : ℂ) ^ (-(3 + 2 * (i.val : ℤ))))
  simp only [phiZeroUnit_zero, mul_one] at hc
  convert hc using 1
  ext τ
  change (phi i ∣[(6 : ℤ)] ModularGroup.S) τ / Periodic.qParam 7 τ ^ (2 - i.val) =
    -(7 : ℂ) ^ (-(3 + 2 * (i.val : ℤ))) * phiZeroUnit i (Periodic.qParam 7 τ)
  rw [phi_S_q_expansion]
  field_simp [Periodic.qParam, exp_ne_zero]

theorem phi_S_tendsto (i : Fin 3) :
    Tendsto (phi i ∣[(6 : ℤ)] ModularGroup.S) atImInfty
      (𝓝 (-(7 : ℂ) ^ (-(3 + 2 * (i.val : ℤ))) * 0 ^ (2 - i.val))) := by
  have hq := qParam_tendsto_atImInfty (by norm_num : (0 : ℝ) < 7)
  have he := (phiZeroUnit_continuousAt_zero i).tendsto.comp hq
  have h := ((hq.pow (2 - i.val)).mul he).const_mul
    (-(7 : ℂ) ^ (-(3 + 2 * (i.val : ℤ))))
  simpa only [Function.comp_apply, ← phi_S_q_expansion, phiZeroUnit_zero, mul_one] using h

theorem phi_S_bounded (i : Fin 3) : IsBoundedAtImInfty (phi i ∣[(6 : ℤ)] ModularGroup.S) :=
  (phi_S_tendsto i).isBigO_one ℝ

/-- The eight representatives reduce every cusp bound to the two actual calculations. -/
theorem phi_bounded_slash (i : Fin 3) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    IsBoundedAtImInfty (phi i ∣[(6 : ℤ)] γ) := by
  obtain ⟨δ, hδ, j, rfl⟩ := schreier_decomposition γ
  rw [SlashAction.slash_mul, phi_slash i ⟨δ, schreierGroup_le hδ⟩]
  by_cases hj : j = 0
  · subst j
    simpa [cosetRep] using phi_bounded_at_infty i
  · rw [cosetRep, if_neg hj, SlashAction.slash_mul, SL_slash]
    apply IsBoundedAtImInfty.slash 6 ?_ (phi_S_bounded i)
    change (((ModularGroup.T ^ ((j.val : ℤ) - 1)).val 1 0 : ℤ) : ℝ) = 0
    rw [ModularGroup.coe_T_zpow]
    norm_num

/-- Each Φᵢ is an actual holomorphic modular form, including Φ₂ with η(τ)⁻². -/
def phiModularForm (i : Fin 3) :
    ModularForm (CongruenceSubgroup.Gamma0 7 : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)) 6 where
  __ := phiSlashInvariant i
  holo' := phi_holo i
  bdd_at_cusps' hc := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    intro γ _
    exact phi_bounded_slash i γ

theorem phiModularForm_ne_zero (i : Fin 3) : phiModularForm i ≠ 0 := by
  intro h
  have hτ := congrArg (fun f : ModularForm
    (CongruenceSubgroup.Gamma0 7 : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)) 6 ↦
      f UpperHalfPlane.I) h
  exact phi_ne_zero i UpperHalfPlane.I hτ

theorem phi_cusp_zero_leading_ne_zero (i : Fin 3) :
    -(7 : ℂ) ^ (-(3 + 2 * (i.val : ℤ))) ≠ 0 :=
  neg_ne_zero.mpr (zpow_ne_zero _ (by norm_num))

end Zeta7LevelSeven

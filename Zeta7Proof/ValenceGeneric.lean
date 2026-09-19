import Zeta7Proof.ValenceLattice
import Zeta7Proof.LevelSevenGenerators

/-! Generic points of a horocycle: the fibres of `x` are exactly `Γ₀(7)`-orbits.

Write `X(z) = η(7z)⁴/η(z)⁴` on the upper half-plane (`X τ = etaCoordinate τ`).

* `horocycle_ae`: an analytic function on the upper half-plane which is not identically zero is
  nonzero at almost every point `u + iy` of every horocycle.
* `Xf_S`: `X(-1/z) = 1/(49 X(z/7))`, so `X(S Tᵏ z) → ∞` at the cusp while `X(z) → 0`.
* `generic_fiber`: for almost every `u`, with `τ' = u + iy`,
  every `τ` with `x(τ) = x(τ')` is `γ τ'` for some `γ ∈ Γ₀(7)`; moreover `X'(τ') ≠ 0` and
  `P(x(τ')) ≠ 0`. The proof combines `sl2_of_x_eq` with the eight right cosets of `Γ₀(7)`. -/
noncomputable section
set_option autoImplicit false
namespace Zeta7Valence
open Complex Filter Topology Zeta7LevelSeven MeasureTheory ModularForm
open UpperHalfPlane hiding I
open scoped MatrixGroups

/-- The upper half-plane as a subset of `ℂ`. -/
abbrev Hset : Set ℂ := {z : ℂ | 0 < z.im}

theorem Hset_isOpen : IsOpen Hset := isOpen_upperHalfPlaneSet

theorem Hset_isConnected : IsConnected Hset := by
  refine ⟨⟨I, by simp⟩, (convex_halfSpace_im_gt 0).isPreconnected⟩

/-- `X(z) = η(7z)⁴/η(z)⁴`. -/
def Xf (z : ℂ) : ℂ := ModularForm.eta (7 * z) ^ 4 / ModularForm.eta z ^ 4

theorem Xf_eq (τ : ℍ) : Xf τ = etaCoordinate τ := (etaCoordinate_value τ).symm

theorem Xf_ne_zero {z : ℂ} (hz : 0 < z.im) : Xf z ≠ 0 := by
  have h7 : 0 < (7 * z).im := by simp; linarith
  exact div_ne_zero (pow_ne_zero 4 (eta_ne_zero h7)) (pow_ne_zero 4 (eta_ne_zero hz))

theorem Xf_differentiableOn : DifferentiableOn ℂ Xf Hset := by
  intro z hz
  change 0 < z.im at hz
  exact ((eta_seven_differentiableAt hz).pow 4 |>.div
    ((differentiableAt_eta_of_mem_upperHalfPlaneSet hz).pow 4)
    (pow_ne_zero 4 (eta_ne_zero hz))).differentiableWithinAt

theorem Xf_analytic : AnalyticOnNhd ℂ Xf Hset :=
  Xf_differentiableOn.analyticOnNhd Hset_isOpen

/-- **A nonzero analytic function is nonzero at almost every point of a horocycle.** -/
theorem horocycle_ae {F : ℂ → ℂ} (hF : AnalyticOnNhd ℂ F Hset) {z₀ : ℂ} (hz₀ : 0 < z₀.im)
    (hF₀ : F z₀ ≠ 0) {y : ℝ} (hy : 0 < y) : ∀ᵐ u : ℝ, F (u + y * I) ≠ 0 := by
  set g : ℝ → ℂ := fun u => F (u + y * I) with hg
  have hmem : ∀ u : ℝ, ((u : ℂ) + y * I) ∈ Hset := fun u => by simp [hy]
  have hga : AnalyticOnNhd ℝ g Set.univ := by
    intro u _
    have h1 : AnalyticAt ℝ (fun v : ℝ => (v : ℂ) + y * I) u :=
      (ofRealCLM.analyticAt u).add analyticAt_const
    have h2 : AnalyticAt ℝ F ((fun v : ℝ => (v : ℂ) + y * I) u) :=
      (hF _ (hmem u)).restrictScalars (𝕜 := ℝ)
    exact AnalyticAt.comp (g := F) (f := fun v : ℝ => (v : ℂ) + y * I) (x := u) h2 h1
  -- `g` is not identically zero
  have hne : ∃ u, g u ≠ 0 := by
    by_contra hall
    push Not at hall
    have hfreq : ∃ᶠ z in 𝓝[≠] ((0 : ℝ) + y * I : ℂ), F z = 0 := by
      have ht : Tendsto (fun u : ℝ => (u : ℂ) + y * I) (𝓝[≠] (0 : ℝ))
          (𝓝[≠] ((0 : ℝ) + y * I : ℂ)) := by
        refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
        · have hc : Continuous (fun u : ℝ => (u : ℂ) + y * I) := by fun_prop
          exact (hc.tendsto 0).mono_left nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin] with u hu
          intro h
          apply hu
          have := congrArg Complex.re h
          simpa using this
      exact ht.frequently (Frequently.of_forall fun u => hall u)
    have h0 := hF.eqOn_zero_of_preconnected_of_frequently_eq_zero Hset_isConnected.isPreconnected
      (hmem 0) hfreq
    exact hF₀ (h0 hz₀)
  obtain ⟨u₀, hu₀⟩ := hne
  have hcod := hga.preimage_zero_mem_codiscreteWithin hu₀ (Set.mem_univ _) isConnected_univ
  have hae := ae_restrict_le_codiscreteWithin (μ := (volume : Measure ℝ)) MeasurableSet.univ hcod
  rw [Measure.restrict_univ] at hae
  filter_upwards [hae] with u hu
  exact hu

/-! ### The transformation under `S` -/

theorem eta_S_sq {z : ℂ} (hz : 0 < z.im) :
    ModularForm.eta (-1 / z) ^ 2 = -I * z * ModularForm.eta z ^ 2 := by
  have h := etaTwo_S_value ⟨z, hz⟩
  simpa [etaTwo] using h

/-- `X(-1/z) = 1/(49 X(z/7))`. -/
theorem Xf_S {z : ℂ} (hz : 0 < z.im) : Xf (-1 / z) = (49 * Xf (z / 7))⁻¹ := by
  have hz7 : 0 < (z / 7).im := by simp; linarith
  have h1 := eta_S_sq hz
  have h2 := eta_S_sq hz7
  have hz0 : z ≠ 0 := fun h => by rw [h] at hz; simp at hz
  have he : ModularForm.eta z ≠ 0 := eta_ne_zero hz
  have he7 : ModularForm.eta (z / 7) ≠ 0 := eta_ne_zero hz7
  have hm : (7 : ℂ) * (-1 / z) = -1 / (z / 7) := by field_simp
  have hm2 : (7 : ℂ) * (z / 7) = z := by field_simp
  unfold Xf
  rw [hm, hm2, show ModularForm.eta (-1 / (z / 7)) ^ 4 = (ModularForm.eta (-1 / (z / 7)) ^ 2) ^ 2 by ring,
    show ModularForm.eta (-1 / z) ^ 4 = (ModularForm.eta (-1 / z) ^ 2) ^ 2 by ring, h1, h2]
  field_simp
  ring_nf

theorem cosetRep_succ (k : ℕ) (hk : k < 7) :
    cosetRep ⟨k + 1, by omega⟩ = ModularGroup.S * ModularGroup.T ^ (k : ℤ) := by
  unfold cosetRep
  rw [if_neg (by intro h; have := congrArg Fin.val h; simp at this)]
  simp

theorem cosetRep_smul (k : ℕ) (hk : k < 7) (τ : ℍ) :
    ((cosetRep ⟨k + 1, by omega⟩ • τ : ℍ) : ℂ) = -1 / ((τ : ℂ) + k) := by
  rw [cosetRep_succ k hk, mul_smul, modular_S_smul, modular_T_zpow_smul]
  simp [coe_vadd, add_comm, neg_div]
  rw [← neg_add, inv_neg]

/-- `Hₖ(z) = X(S Tᵏ z) - X(z)`, written with the transformation formula. -/
def Hk (k : ℕ) (z : ℂ) : ℂ := (49 * Xf ((z + k) / 7))⁻¹ - Xf z

theorem Hk_eq (k : ℕ) (hk : k < 7) (τ : ℍ) :
    Hk k τ = etaCoordinate (cosetRep ⟨k + 1, by omega⟩ • τ) - etaCoordinate τ := by
  have hpos : 0 < ((τ : ℂ) + k).im := by simp [τ.im_pos]
  rw [← Xf_eq, ← Xf_eq, cosetRep_smul k hk, Xf_S hpos, Hk]

theorem Hk_analytic (k : ℕ) : AnalyticOnNhd ℂ (Hk k) Hset := by
  apply DifferentiableOn.analyticOnNhd _ Hset_isOpen
  intro z hz
  change 0 < z.im at hz
  have hw : 0 < ((z + k) / 7).im := by simp; linarith
  have hd : DifferentiableAt ℂ (Xf ∘ fun z : ℂ => (z + k) / 7) z :=
    (Xf_differentiableOn.differentiableAt (Hset_isOpen.mem_nhds hw)).comp z
      ((differentiableAt_id.add_const _).div_const _)
  exact ((hd.const_mul 49).inv (mul_ne_zero (by norm_num) (Xf_ne_zero hw))).sub
    (Xf_differentiableOn.differentiableAt (Hset_isOpen.mem_nhds hz)) |>.differentiableWithinAt

theorem etaCoordinate_tendsto' : Tendsto (fun z : ℍ => Xf z) atImInfty (𝓝 0) := by
  simpa [Xf_eq] using etaCoordinate_tendsto

/-- The shifted point `(τ + k)/7` of the upper half-plane. -/
def shiftSeven (k : ℕ) (τ : ℍ) : ℍ := ⟨((τ : ℂ) + k) / 7, by simp [τ.im_pos]⟩

theorem shiftSeven_tendsto (k : ℕ) : Tendsto (shiftSeven k) atImInfty atImInfty := by
  rw [atImInfty, tendsto_comap_iff]
  have : (fun τ : ℍ => (shiftSeven k τ).im) = fun τ => τ.im / 7 := by
    funext τ
    change (((τ : ℂ) + k) / 7).im = (τ : ℂ).im / 7
    simp
  change Tendsto (fun τ : ℍ => (shiftSeven k τ).im) atImInfty atTop
  rw [this]
  exact (tendsto_comap.atTop_div_const (by norm_num))

theorem Hk_exists_ne (k : ℕ) : ∃ z : ℂ, 0 < z.im ∧ Hk k z ≠ 0 := by
  have h1 := etaCoordinate_tendsto'.eventually (Metric.ball_mem_nhds (0 : ℂ) (by norm_num :
    (0 : ℝ) < 1 / 2))
  have h2 := ((etaCoordinate_tendsto'.comp (shiftSeven_tendsto k)).eventually
    (Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1 / 98)))
  obtain ⟨τ, hτ1, hτ2⟩ := (h1.and h2).exists
  refine ⟨τ, τ.im_pos, ?_⟩
  simp only [Function.comp, Metric.mem_ball, dist_zero_right] at hτ1 hτ2
  have hs : Xf ((τ + k) / 7) = Xf (shiftSeven k τ) := rfl
  intro h0
  unfold Hk at h0
  rw [hs] at h0
  have hne : Xf (shiftSeven k τ) ≠ 0 := Xf_ne_zero (shiftSeven k τ).im_pos
  have heq : (49 * Xf (shiftSeven k τ))⁻¹ = Xf τ := by linear_combination h0
  have hb : ‖(49 * Xf (shiftSeven k τ))⁻¹‖ > 2 := by
    rw [norm_inv, norm_mul]
    have hp : 0 < ‖Xf (shiftSeven k τ)‖ := norm_pos_iff.mpr hne
    rw [gt_iff_lt, lt_inv_comm₀ (by norm_num) (mul_pos (by norm_num) hp)]
    norm_num
    linarith
  rw [heq] at hb
  linarith

/-! ### Generic points -/

theorem deriv_Xf_exists_ne : ∃ z : ℂ, 0 < z.im ∧ deriv Xf z ≠ 0 := by
  by_contra hall
  push Not at hall
  have hconst : ∀ x ∈ Hset, ∀ w ∈ Hset, Xf x = Xf w := fun x hx w hw =>
    Hset_isOpen.is_const_of_deriv_eq_zero Hset_isConnected.isPreconnected
      Xf_differentiableOn (fun z hz => hall z hz) hx hw
  -- `X` would be constant, but it tends to `0` and never vanishes
  have h1 := etaCoordinate_tendsto'
  have hc : ∀ τ : ℍ, Xf τ = Xf I := fun τ => hconst τ τ.im_pos I (by simp)
  have hlim : Tendsto (fun _ : ℍ => Xf I) atImInfty (𝓝 0) := by
    simpa [hc] using h1
  have := tendsto_nhds_unique hlim tendsto_const_nhds
  exact Xf_ne_zero (by simp : (0 : ℝ) < (I : ℂ).im) this.symm

theorem polyP_Xf_exists_ne : ∃ z : ℂ, 0 < z.im ∧ polyP (Xf z) ≠ 0 := by
  have h1 := etaCoordinate_tendsto'.eventually (Metric.ball_mem_nhds (0 : ℂ) (by norm_num :
    (0 : ℝ) < 1 / 100))
  obtain ⟨τ, hτ⟩ := h1.exists
  refine ⟨τ, τ.im_pos, ?_⟩
  simp only [Metric.mem_ball, dist_zero_right] at hτ
  intro h0
  unfold polyP at h0
  have : ‖13 * Xf τ + 49 * Xf τ ^ 2‖ < 1 := by
    calc ‖13 * Xf τ + 49 * Xf τ ^ 2‖ ≤ 13 * ‖Xf τ‖ + 49 * ‖Xf τ‖ ^ 2 := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_mul, norm_pow]; norm_num
      _ < 1 := by nlinarith [norm_nonneg (Xf τ)]
  have e : 13 * Xf τ + 49 * Xf τ ^ 2 = -1 := by linear_combination h0
  rw [e] at this
  simp at this

/-- The point `u + iy` of the upper half-plane. -/
def horPt {y : ℝ} (hy : 0 < y) (u : ℝ) : ℍ := ⟨u + y * I, by simp [hy]⟩

theorem x_gamma (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 7) (τ : ℍ) :
    etaCoordinate (γ • τ) = etaCoordinate τ := by
  have h := congrFun (etaCoordinate_slash ⟨γ, hγ⟩) τ
  simpa [SL_slash_apply] using h

/-- **Generic fibres are `Γ₀(7)`-orbits.** -/
theorem generic_fiber {y : ℝ} (hy : 0 < y) : ∀ᵐ u : ℝ,
    (∀ τ : ℍ, etaCoordinate τ = etaCoordinate (horPt hy u) →
      ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 7 ∧ τ = γ • horPt hy u) ∧
    deriv Xf (u + y * I) ≠ 0 ∧ polyP (Xf (u + y * I)) ≠ 0 := by
  have hHk : ∀ k : Fin 7, ∀ᵐ u : ℝ, Hk k (u + y * I) ≠ 0 := by
    intro k
    obtain ⟨z, hz, hne⟩ := Hk_exists_ne k
    exact horocycle_ae (Hk_analytic k) hz hne hy
  have hHall : ∀ᵐ u : ℝ, ∀ k : Fin 7, Hk k (u + y * I) ≠ 0 := ae_all_iff.mpr hHk
  have hD : ∀ᵐ u : ℝ, deriv Xf (u + y * I) ≠ 0 := by
    obtain ⟨z, hz, hne⟩ := deriv_Xf_exists_ne
    exact horocycle_ae Xf_analytic.deriv hz hne hy
  have hP : ∀ᵐ u : ℝ, polyP (Xf (u + y * I)) ≠ 0 := by
    obtain ⟨z, hz, hne⟩ := polyP_Xf_exists_ne
    refine horocycle_ae (F := fun z => polyP (Xf z)) ?_ hz hne hy
    intro z hz'
    unfold polyP
    have := Xf_analytic z hz'
    fun_prop
  filter_upwards [hHall, hD, hP] with u hu hdu hpu
  refine ⟨fun τ hx => ?_, hdu, hpu⟩
  have hP' : polyP (etaCoordinate (horPt hy u)) ≠ 0 := by
    rw [← Xf_eq]; exact hpu
  obtain ⟨γ, hγ⟩ := sl2_of_x_eq hx hP'
  -- decompose `γ` along the right cosets of `Γ₀(7)`
  obtain ⟨i, hi⟩ := rightCoset_bijective.2
    (Quotient.mk (QuotientGroup.rightRel (CongruenceSubgroup.Gamma0 7)) γ)
  have hrel := QuotientGroup.rightRel_apply.mp (Quotient.exact hi)
  set h := γ * (cosetRep i)⁻¹ with hh
  have hγeq : γ = h * cosetRep i := by rw [hh]; group
  by_cases hi0 : i = 0
  · subst hi0
    refine ⟨γ, ?_, hγ⟩
    have : cosetRep 0 = 1 := by simp [cosetRep]
    rw [hγeq, this, mul_one]
    exact hrel
  · exfalso
    obtain ⟨k, hk7, hik⟩ : ∃ k : ℕ, ∃ hk : k < 7, i = ⟨k + 1, by omega⟩ := by
      refine ⟨i.val - 1, by omega, Fin.ext ?_⟩
      have : i.val ≠ 0 := fun h0 => hi0 (Fin.ext h0)
      simp; omega
    subst hik
    have hx2 : etaCoordinate (cosetRep ⟨k + 1, by omega⟩ • horPt hy u) =
        etaCoordinate (horPt hy u) := by
      rw [← hx, hγ, hγeq, mul_smul, x_gamma h hrel]
    have := Hk_eq k hk7 (horPt hy u)
    rw [hx2, sub_self] at this
    exact hu ⟨k, hk7⟩ this

end Zeta7Valence

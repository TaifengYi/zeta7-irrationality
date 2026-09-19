import Zeta7Proof.ArchSourceFlag

/-! C2 (Jensen step): leading coefficients of flag vectors through the modular pullback.

For a source vector `v` with image `F = sourceMap d c v`, the pole-cleared pullback
`a(q) F(x(q))` is the explicit finite combination `Σ v_i x(q)^m (a g_j)(x(q))` of holomorphic
functions on the unit disc (`pulledSource_eq`). If `v` lies in the flag at `k`, then
`a(q) F(x(q)) = q^{λ_k} h(q)` with `h` holomorphic and `h(0) = [x^{λ_k}] F`
(`flag_pulled_factor`). Jensen's formula (Mathlib) then gives, for every `0 < r < 1`,

  `log |[x^{λ_k}] F| ≤ (mean of log |a(q) F(x(q))| on |q| = r) - λ_k log r`,

which is inequality (41) before the potential-theoretic bound of the boundary mean. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
namespace Zeta7Arch
open PowerSeries Zeta7Main Zeta7Common Filter Topology

/-! ### Generic leading-coefficient transport -/

theorem constantCoeff_subst_of_zero {R : Type*} [CommRing R] {b : R⟦X⟧}
    (hb : constantCoeff b = 0) (f : R⟦X⟧) :
    constantCoeff (f.subst b) = constantCoeff f := by
  have hB : HasSubst b := HasSubst.of_constantCoeff_zero' hb
  have h := constantCoeff_subst_eq_zero hb (f - C (constantCoeff f)) (by simp)
  change constantCoeff ((f - C (constantCoeff f)).subst b) = 0 at h
  have hs : (f - C (constantCoeff f)).subst b = f.subst b - C (constantCoeff f) := by
    rw [subst_sub hB, subst_C]; rfl
  rw [hs, map_sub, constantCoeff_C] at h
  exact sub_eq_zero.mp h

/-- If `f` vanishes below `xⁿ`, then `a · f(X u) = Xⁿ g` with `g(0) = [xⁿ] f`
whenever `a(0) = u(0) = 1`. -/
theorem subst_leading {R : Type*} [CommRing R] (u a f : R⟦X⟧) (hu : constantCoeff u = 1)
    (ha : constantCoeff a = 1) (n : ℕ) (hf : ∀ k < n, coeff k f = 0) :
    ∃ g : R⟦X⟧, a * f.subst (X * u) = X ^ n * g ∧ constantCoeff g = coeff n f := by
  have hb : constantCoeff (X * u) = 0 := by simp
  have hB : HasSubst (X * u) := HasSubst.of_constantCoeff_zero' hb
  obtain ⟨g, rfl⟩ : X ^ n ∣ f := X_pow_dvd_iff.mpr hf
  refine ⟨a * u ^ n * g.subst (X * u), ?_, ?_⟩
  · rw [subst_mul hB, subst_pow hB, subst_X hB]; ring
  · rw [map_mul, map_mul, map_pow, constantCoeff_subst_of_zero hb, ha, hu,
      coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self, coeff_zero_eq_constantCoeff_apply]
    ring

theorem Tempered.of_X_pow_mul {n : ℕ} {g : ℂ⟦X⟧} (h : Tempered (X ^ n * g)) : Tempered g := by
  intro r hr0 hr1
  rcases hr0.eq_or_lt with rfl | hrpos
  · apply summable_of_ne_finset_zero (s := {0})
    intro k hk
    have hk0 : k ≠ 0 := by simpa using hk
    simp [zero_pow hk0]
  · have hs := (summable_nat_add_iff n).mpr (h r hr0 hr1)
    refine (hs.div_const (r ^ n)).congr fun k => ?_
    rw [coeff_X_pow_mul', if_pos (by omega), Nat.add_sub_cancel, pow_add]
    field_simp

theorem tempered_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ⟦X⟧)
    (h : ∀ i ∈ s, Tempered (f i)) : Tempered (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using tempered_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (by simp)).add (ih fun i hi => h i (by simp [hi]))

theorem Tempered.smul {f : ℂ⟦X⟧} (hf : Tempered f) (a : ℂ) : Tempered (a • f) := by
  rw [smul_eq_C_mul]; exact hf.smul_C a

/-! ### The complex pullback data -/

/-- The coordinate `x(q)` over `ℂ`. -/
def xC : ℂ⟦X⟧ := xSeries.map (algebraMap ℚ ℂ)
/-- `x(q)/q` over `ℂ`. -/
def uC : ℂ⟦X⟧ := xUnit.map (algebraMap ℚ ℂ)
/-- The clearing factor `a(q) = A(q)^3` over `ℂ`. -/
def aC : ℂ⟦X⟧ := clearingFactor.map (algebraMap ℚ ℂ)

theorem xC_eq : xC = X * uC := by
  simp [xC, uC, xSeries]

theorem constantCoeff_map_rat (f : ℚ⟦X⟧) :
    constantCoeff (f.map (algebraMap ℚ ℂ)) = ((constantCoeff f : ℚ) : ℂ) := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_map_rat, coeff_zero_eq_constantCoeff_apply]

theorem uC_constant : constantCoeff uC = 1 := by
  rw [uC, constantCoeff_map_rat, xUnit_constant]; simp

theorem aC_constant : constantCoeff aC = 1 := by
  rw [aC, constantCoeff_map_rat, clearingFactor_constant]; simp

theorem xC_hasSubst : HasSubst xC :=
  HasSubst.of_constantCoeff_zero' (by rw [xC_eq]; simp)

theorem map_subst_x (g : ℚ⟦X⟧) :
    (g.map (algebraMap ℚ ℂ)).subst xC =
      PowerSeries.map (algebraMap ℚ ℂ) (g.subst xSeries : ℚ⟦X⟧) :=
  (map_subst x_hasSubst g).symm

/-- The pole-cleared pullbacks of the source monomials. -/
def clearedBlock (d : ℕ) (c : ℚ) : BlockIndex d → ℂ⟦X⟧
  | .inl m => xC ^ m.val * aC
  | .inr jm => xC ^ jm.2.val * (clearedGerm c jm.1).map (algebraMap ℚ ℂ)

/-- `a(q) F_v(x(q))`. -/
def pulledSource (d : ℕ) (c : ℚ) (v : Source d) : ℂ⟦X⟧ :=
  aC * (sourceMap d c v).subst xC

theorem aC_mul_subst_block (d : ℕ) (c : ℚ) (i : BlockIndex d) :
    aC * (blockSeries d (complexGerms c) i).subst xC = clearedBlock d c i := by
  rcases i with m | ⟨j, m⟩
  · simp only [blockSeries, clearedBlock]
    rw [subst_pow xC_hasSubst, subst_X xC_hasSubst]
    ring
  · simp only [blockSeries, clearedBlock, complexGerms]
    rw [subst_mul xC_hasSubst, subst_pow xC_hasSubst, subst_X xC_hasSubst, map_subst_x,
      ← clearing_identity]
    simp only [map_mul, aC, pulledGerm]
    ring

/-- **The pulled-back image is the explicit cleared combination.** -/
theorem pulledSource_eq (d : ℕ) (c : ℚ) (v : Source d) :
    pulledSource d c v = ∑ i, v i • clearedBlock d c i := by
  unfold pulledSource
  change aC * (∑ i, v i • blockSeries d (complexGerms c) i).subst xC = _
  rw [← coe_substAlgHom xC_hasSubst, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, mul_smul_comm, coe_substAlgHom, aC_mul_subst_block]

theorem xC_tempered : Tempered xC := xSeries_tempered
theorem aC_tempered : Tempered aC := clearingFactor_tempered

theorem clearedBlock_tempered (d : ℕ) (c : ℚ) (i : BlockIndex d) :
    Tempered (clearedBlock d c i) := by
  rcases i with m | ⟨j, m⟩
  · exact (xC_tempered.pow _).mul aC_tempered
  · exact (xC_tempered.pow _).mul (clearedGerm_tempered c j)

theorem pulledSource_tempered (d : ℕ) (c : ℚ) (v : Source d) :
    Tempered (pulledSource d c v) := by
  rw [pulledSource_eq]
  exact tempered_sum _ _ fun i _ => (clearedBlock_tempered d c i).smul (v i)

/-- The pulled-back image is holomorphic on the unit disc. -/
theorem pulledSource_holomorphic (d : ℕ) (c : ℚ) (v : Source d) :
    AnalyticOnNhd ℂ (evalQ (pulledSource d c v)) (Metric.ball 0 1) :=
  (pulledSource_tempered d c v).analyticOnNhd

/-- **Factorization at a flag vector.** -/
theorem flag_pulled_factor (d : ℕ) (c : ℚ) (k : JIdx d) (v : Source d)
    (hv : v ∈ flag d c k) :
    ∃ h : ℂ⟦X⟧, Tempered h ∧ pulledSource d c v = X ^ (jump d c k) * h ∧
      evalQ h 0 = coeff (jump d c k) (sourceMap d c v) := by
  obtain ⟨g, hg, hg0⟩ := subst_leading uC aC (sourceMap d c v) uC_constant aC_constant
    (jump d c k) (flag_vanishing d c k v hv)
  have hp : pulledSource d c v = X ^ jump d c k * g := by rw [pulledSource, xC_eq, hg]
  have ht := pulledSource_tempered d c v
  rw [hp] at ht
  exact ⟨g, ht.of_X_pow_mul, hp, by rw [evalQ_zero_point, hg0]⟩

/-! ### Jensen's inequality for the leading coefficient -/

theorem jensen_leading {F h : ℂ → ℂ} {n : ℕ} {r : ℝ} (hr : 0 < r)
    (hF : AnalyticOnNhd ℂ F (Metric.closedBall 0 r)) (hh : AnalyticAt ℂ h 0) (h0 : h 0 ≠ 0)
    (heq : ∀ᶠ z in 𝓝 (0 : ℂ), F z = z ^ n * h z) :
    Real.log ‖h 0‖ ≤ Real.circleAverage (fun z => Real.log ‖F z‖) 0 r - n * Real.log r := by
  have habs : |r| = r := abs_of_pos hr
  have hF' : AnalyticOnNhd ℂ F (Metric.closedBall 0 |r|) := by rwa [habs]
  have hj := hF'.meromorphicOn.circleAverage_log_norm (c := 0) hr.ne'
  have hpres : ∀ᶠ z in 𝓝[≠] (0 : ℂ), F z = (z - 0) ^ (n : ℤ) • h z := by
    filter_upwards [nhdsWithin_le_nhds heq] with z hz
    rw [hz, sub_zero, zpow_natCast, smul_eq_mul]
  have hmer : MeromorphicAt F 0 := (hF' 0 (by simp)).meromorphicAt
  have hord : meromorphicOrderAt F 0 = (n : ℤ) :=
    (meromorphicOrderAt_eq_int_iff hmer).mpr ⟨h, hh, h0, hpres⟩
  have hdiv : MeromorphicOn.divisor F (Metric.closedBall 0 |r|) 0 = n := by
    rw [MeromorphicOn.divisor_apply hF'.meromorphicOn (by simp), hord]
    rfl
  have htr : meromorphicTrailingCoeffAt F 0 = h 0 :=
    hh.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE h0 hpres
  have hsum : 0 ≤ ∑ᶠ u, (MeromorphicOn.divisor F (Metric.closedBall 0 |r|) u : ℝ) *
      Real.log (r * ‖0 - u‖⁻¹) := by
    apply finsum_nonneg
    intro u
    by_cases hu : u ∈ Metric.closedBall (0 : ℂ) |r|
    · refine mul_nonneg (by exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg hF' u) ?_
      by_cases hu0 : u = 0
      · simp [hu0]
      · apply Real.log_nonneg
        have hn : 0 < ‖u‖ := norm_pos_iff.mpr hu0
        have hle : ‖u‖ ≤ r := by simpa [habs] using hu
        rw [zero_sub, norm_neg, ← div_eq_mul_inv, one_le_div hn]
        exact hle
    · simp [hu]
  rw [hj, hdiv, htr] at *
  push_cast
  linarith

/-- **Inequality (41), Jensen form.** For a flag vector with nonzero leading coefficient and any
`0 < r < 1`, `log |[x^{λ_k}] F| ≤ mean_{|q|=r} log |a(q) F(x(q))| - λ_k log r`. -/
theorem flag_leading_jensen (d : ℕ) (c : ℚ) (k : JIdx d) (v : Source d)
    (hv : v ∈ flag d c k) (hlead : coeff (jump d c k) (sourceMap d c v) ≠ 0)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    Real.log ‖coeff (jump d c k) (sourceMap d c v)‖ ≤
      Real.circleAverage (fun q => Real.log ‖evalQ (pulledSource d c v) q‖) 0 r -
        (jump d c k : ℝ) * Real.log r := by
  obtain ⟨g, hg, hp, hg0⟩ := flag_pulled_factor d c k v hv
  have hball : Metric.closedBall (0 : ℂ) r ⊆ Metric.ball 0 1 :=
    Metric.closedBall_subset_ball hr1
  have hF := (pulledSource_holomorphic d c v).mono hball
  have hgA : AnalyticAt ℂ (evalQ g) 0 := hg.analyticOnNhd 0 (by simp)
  have heq : ∀ᶠ z in 𝓝 (0 : ℂ), evalQ (pulledSource d c v) z = z ^ jump d c k * evalQ g z := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) one_pos] with z hz
    have hz' : ‖z‖ < 1 := by simpa using hz
    rw [hp, evalQ_mul (tempered_X_pow _) hg hz', evalQ_X_pow]
  have := jensen_leading hr0 hF hgA (by rw [hg0]; exact hlead) heq
  rwa [hg0] at this

end Zeta7Arch

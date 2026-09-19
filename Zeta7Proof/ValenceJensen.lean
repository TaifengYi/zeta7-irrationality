import Zeta7Proof.ValenceCosets

/-! The pointwise Jensen bound on a circle of the q-disc.

Fix heights `y, t > 0`, `r = e^{-2πt}`, a generic `u ∈ [0, 1]` (in the sense of `generic_fiber`) and
`q' = e^{2πi(u + iy)}`. Jensen's formula for `q ↦ x(q) - x(q')` on `|q| ≤ r` gives

`(1/2π) ∫ log |x(r e^{iθ}) - x(q')| dθ ≤ log |x(q')| + Σ_{(c,d)} 2π (y/((cu + d)² + c²y²) - t)₊`,

the sum running over the admissible lower rows of `Γ_∞ \ Γ₀(7)` in an explicit finite box.
Every zero inside the disc is `e^{2πiγτ'}` with `γ ∈ Γ₀(7)` (`generic_fiber`), it is simple
(`X'(γτ') = X'(τ')(cτ' + d)² ≠ 0`), and it only depends on the lower row of `γ`. -/
noncomputable section
set_option autoImplicit false
namespace Zeta7Valence
open Complex Zeta7LevelSeven Zeta7Arch Metric Real
open UpperHalfPlane hiding I
open scoped MatrixGroups

/-- `2π (y/((cu + d)² + c²y²) - t)₊`. -/
def orbitTerm (y t u : ℝ) (p : ℤ × ℤ) : ℝ :=
  2 * π * max 0 (y / (((p.1 : ℝ) * u + p.2) ^ 2 + (p.1 : ℝ) ^ 2 * y ^ 2) - t)

theorem orbitTerm_nonneg (y t u : ℝ) (p : ℤ × ℤ) : 0 ≤ orbitTerm y t u p := by
  unfold orbitTerm; have := pi_pos; positivity

def boxM (y t : ℝ) : ℕ := ⌈(y * t)⁻¹⌉₊
def boxN (y t : ℝ) : ℕ := boxM y t + ⌈y / t⌉₊ + 1

/-- The finite box of admissible lower rows. -/
def cosetBox (y t : ℝ) : Finset (ℤ × ℤ) :=
  ((Finset.Icc (0 : ℤ) (boxM y t)) ×ˢ (Finset.Icc (-(boxN y t : ℤ)) (boxN y t))).filter
    bottomShape

/-- A representative of the coset with lower row `p` applied to `τ'`, as a point of the q-disc. -/
def Phi {y : ℝ} (hy : 0 < y) (u : ℝ) (p : ℤ × ℤ) : ℂ :=
  if h : bottomShape p then Function.Periodic.qParam 1 ((Classical.choose (exists_rep h)) • horPt hy u : ℍ)
  else 0

theorem norm_qParam_smul (γ : SL(2, ℤ)) (τ : ℍ) :
    ‖Function.Periodic.qParam 1 ((γ • τ : ℍ) : ℂ)‖ = Real.exp (-(2 * π * (γ • τ).im)) := by
  rw [Function.Periodic.norm_qParam, UpperHalfPlane.coe_im, div_one]
  ring_nf

theorem Phi_eq {y : ℝ} (hy : 0 < y) (u : ℝ) {γ : SL(2, ℤ)}
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 7) :
    Phi hy u ((normSL γ) 1 0, (normSL γ) 1 1) =
      Function.Periodic.qParam 1 ((γ • horPt hy u : ℍ) : ℂ) := by
  have hs := bottomShape_of_Gamma0 hγ
  unfold Phi
  rw [dif_pos hs]
  have hc := Classical.choose_spec (exists_rep hs)
  rw [qParam_eq_of_bottom (γ := normSL γ) hc.2.1 hc.2.2, normSL_smul]

theorem log_Phi {y t : ℝ} (hy : 0 < y) (u : ℝ) {p : ℤ × ℤ} (hp : bottomShape p) :
    max 0 (Real.log (Real.exp (-(2 * π * t)) * ‖Phi hy u p‖⁻¹)) = orbitTerm y t u p := by
  unfold Phi
  rw [dif_pos hp]
  set γ := Classical.choose (exists_rep hp)
  have hc := Classical.choose_spec (exists_rep hp)
  rw [norm_qParam_smul, im_smul_horPt, hc.2.1, hc.2.2, ← Real.exp_neg, ← Real.exp_add,
    Real.log_exp, orbitTerm]
  have h2 : (0 : ℝ) < 2 * π := by positivity
  rw [show -(2 * π * t) + -(-(2 * π * (y / (((p.1 : ℝ) * u + p.2) ^ 2 + (p.1 : ℝ) ^ 2 * y ^ 2)))) =
    2 * π * (y / (((p.1 : ℝ) * u + p.2) ^ 2 + (p.1 : ℝ) ^ 2 * y ^ 2) - t) by ring]
  rw [mul_max_of_nonneg _ _ h2.le, mul_zero]

/-- Bounds for admissible rows coming from zeros inside the circle of height `t`. -/
theorem mem_cosetBox {y t : ℝ} (hy : 0 < y) (ht : 0 < t) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma0 7) (hIm : t < (γ • horPt hy u).im) :
    ((normSL γ) 1 0, (normSL γ) 1 1) ∈ cosetBox y t := by
  have hs := bottomShape_of_Gamma0 hγ
  set c := (normSL γ) 1 0 with hcdef
  set d := (normSL γ) 1 1 with hddef
  rw [← normSL_smul γ, im_smul_horPt] at hIm
  rw [← hcdef, ← hddef] at hIm
  have hc0 : 0 ≤ c := by
    rcases hs with ⟨h1, _⟩ | ⟨h1, _⟩
    · simp only at h1; rw [h1]
    · exact h1.le
  set Q : ℝ := ((c : ℝ) * u + d) ^ 2 + (c : ℝ) ^ 2 * y ^ 2 with hQ
  have hQpos : 0 < Q := by
    by_contra hQ0
    push Not at hQ0
    have : y / Q ≤ 0 := div_nonpos_of_nonneg_of_nonpos hy.le hQ0
    linarith
  have hkey : t * Q < y := by
    have := (lt_div_iff₀ hQpos).mp hIm
    linarith
  have hcy : (c : ℝ) ^ 2 * (y * t) < 1 := by
    have h1 : (c : ℝ) ^ 2 * y ^ 2 ≤ Q := by rw [hQ]; nlinarith [sq_nonneg ((c : ℝ) * u + d)]
    have h2 : t * ((c : ℝ) ^ 2 * y ^ 2) < y := lt_of_le_of_lt (mul_le_mul_of_nonneg_left h1 ht.le)
      hkey
    have : (c : ℝ) ^ 2 * (y * t) * y < 1 * y := by nlinarith
    exact lt_of_mul_lt_mul_right this hy.le
  have hcM : c ≤ boxM y t := by
    have hc' : (c : ℝ) ≤ (y * t)⁻¹ := by
      rcases (show (c : ℝ) = 0 ∨ 1 ≤ (c : ℝ) by
        rcases eq_or_lt_of_le hc0 with h | h
        · left; rw [← h]; simp
        · right; exact_mod_cast h) with h | h
      · rw [h]; positivity
      · have hyt : 0 < y * t := mul_pos hy ht
        have hlt : (c : ℝ) * (y * t) < 1 := by nlinarith
        calc (c : ℝ) = ((c : ℝ) * (y * t)) * (y * t)⁻¹ := by field_simp
          _ ≤ 1 * (y * t)⁻¹ := by gcongr
          _ = (y * t)⁻¹ := one_mul _
    have := Nat.le_ceil ((y * t)⁻¹)
    have h3 : (c : ℝ) ≤ (boxM y t : ℝ) := by unfold boxM; linarith
    exact_mod_cast h3
  have hd : |(d : ℝ)| ≤ boxN y t := by
    have h1 : ((c : ℝ) * u + d) ^ 2 < y / t := by
      rw [lt_div_iff₀ ht]
      have : ((c : ℝ) * u + d) ^ 2 ≤ Q := by rw [hQ]; nlinarith [sq_nonneg ((c : ℝ) * y)]
      nlinarith
    have h2 : |(c : ℝ) * u + d| ≤ 1 + y / t := by
      rw [abs_le]
      constructor <;> nlinarith [sq_nonneg ((c : ℝ) * u + d - 1), sq_nonneg ((c : ℝ) * u + d + 1),
        div_pos hy ht]
    have h3 : |(c : ℝ) * u| ≤ c := by
      rw [abs_mul, abs_of_nonneg (by exact_mod_cast hc0 : (0 : ℝ) ≤ c), abs_of_nonneg hu0]
      nlinarith [show (0 : ℝ) ≤ c by exact_mod_cast hc0]
    have h4 : |(d : ℝ)| ≤ c + 1 + y / t := by
      have := abs_sub (((c : ℝ) * u + d)) ((c : ℝ) * u)
      simp only [add_sub_cancel_left] at this
      linarith
    have h5 : (c : ℝ) ≤ boxM y t := by exact_mod_cast hcM
    have h6 := Nat.le_ceil (y / t)
    unfold boxN
    push_cast
    linarith
  unfold cosetBox
  rw [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
  refine ⟨⟨⟨hc0, by exact_mod_cast hcM⟩, ?_⟩, hs⟩
  rw [abs_le] at hd
  constructor
  · have := hd.1; exact_mod_cast (show ((-(boxN y t : ℤ) : ℤ) : ℝ) ≤ d by push_cast; linarith)
  · have := hd.2; exact_mod_cast this

/-- **The structure of the zeros** at a generic point. -/
theorem zero_structure {y : ℝ} (hy : 0 < y) {u : ℝ}
    (hfib : ∀ τ : ℍ, etaCoordinate τ = etaCoordinate (horPt hy u) →
      ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 7 ∧ τ = γ • horPt hy u)
    (hder : deriv Xf ((horPt hy u : ℍ) : ℂ) ≠ 0) {a : ℂ} (ha1 : ‖a‖ < 1) (ha0 : a ≠ 0)
    (hxa : xFun a = xFun (Function.Periodic.qParam 1 (horPt hy u))) :
    ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 7 ∧
      a = Function.Periodic.qParam 1 ((γ • horPt hy u : ℍ) : ℂ) ∧ deriv xFun a ≠ 0 := by
  have hpos := invQParam_im_pos ha0 ha1
  set τa : ℍ := ⟨Function.Periodic.invQParam 1 a, hpos⟩
  have hqa : Function.Periodic.qParam 1 (τa : ℂ) = a :=
    Function.Periodic.qParam_right_inv one_ne_zero ha0
  have hx : etaCoordinate τa = etaCoordinate (horPt hy u) := by
    rw [← xFun_qParam, ← xFun_qParam, hqa, hxa]
  obtain ⟨γ, hγ, hτ⟩ := hfib τa hx
  refine ⟨γ, hγ, by rw [← hτ, hqa], ?_⟩
  have hz := (γ • horPt hy u).im_pos
  have hd1 := deriv_Xf_eq (z := ((γ • horPt hy u : ℍ) : ℂ)) hz
  rw [mob_coe, deriv_Xf_mob hγ (horPt hy u).im_pos, ← mob_coe, ← hτ, hqa] at hd1
  intro h0
  rw [h0, zero_mul] at hd1
  have hden := denom_ne (γ := γ) (horPt hy u).im_pos
  exact mul_ne_zero hder (pow_ne_zero 2 hden) hd1


/-- **The pointwise Jensen bound** at a generic point of the horocycle of height `y`. -/
theorem jensen_bound {y t : ℝ} (hy : 0 < y) (ht : 0 < t) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hfib : ∀ τ : ℍ, etaCoordinate τ = etaCoordinate (horPt hy u) →
      ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 7 ∧ τ = γ • horPt hy u)
    (hder : deriv Xf ((horPt hy u : ℍ) : ℂ) ≠ 0) :
    circleAverage (fun q => Real.log ‖xFun q - xFun (Function.Periodic.qParam 1 (horPt hy u))‖) 0
        (Real.exp (-(2 * π * t))) ≤
      Real.log ‖xFun (Function.Periodic.qParam 1 (horPt hy u))‖ +
        ∑ p ∈ cosetBox y t, orbitTerm y t u p := by
  set q' := Function.Periodic.qParam 1 ((horPt hy u : ℍ) : ℂ) with hq'
  set w := xFun q' with hw
  set r := Real.exp (-(2 * π * t)) with hr
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := by
    rw [hr, ← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by have := pi_pos; nlinarith)
  have habs : |r| = r := abs_of_pos hr0
  set F : ℂ → ℂ := fun q => xFun q - w with hF
  have hball : closedBall (0 : ℂ) |r| ⊆ ball 0 1 := fun z hz => by
    rw [habs, mem_closedBall, dist_zero_right] at hz
    rw [mem_ball, dist_zero_right]; linarith
  have hFa : AnalyticOnNhd ℂ F (closedBall 0 |r|) := fun z hz =>
    (xFun_analytic z (hball hz)).sub analyticAt_const
  have hq'0 : q' ≠ 0 := Function.Periodic.qParam_ne_zero _
  have hq'1 : ‖q'‖ < 1 := Function.Periodic.norm_qParam_lt_one one_pos (horPt hy u).im_pos
  have hw0 : w ≠ 0 := xFun_ne_zero hq'0 hq'1
  have hF0 : F 0 ≠ 0 := by simp [hF, xFun_zero, hw0]
  have hJ := hFa.circleAverage_log_norm hr0.ne' hF0
  change circleAverage (fun q => Real.log ‖F q‖) 0 r ≤ _
  rw [hJ]
  have hlogF0 : Real.log ‖F 0‖ = Real.log ‖w‖ := by simp [hF, xFun_zero]
  rw [hlogF0, add_comm]
  gcongr
  -- the divisor sum
  set D := MeromorphicOn.divisor F (closedBall 0 |r|) with hD
  have hfin := D.finiteSupport (isCompact_closedBall (0 : ℂ) |r|)
  set S := hfin.toFinset with hS
  set L : ℂ → ℝ := fun a => Real.log (r * ‖(0 : ℂ) - a‖⁻¹) with hL
  rw [finsum_eq_sum_of_support_subset (f := fun a => (D a : ℝ) * Real.log (r * ‖(0 : ℂ) - a‖⁻¹))
    (s := S) (fun a ha => by
    rw [Set.Finite.coe_toFinset]
    intro h0
    apply ha
    simp [h0])]
  -- zeros inside the disc
  have hzero : ∀ a ∈ S, F a = 0 := by
    intro a ha
    rw [Set.Finite.mem_toFinset] at ha
    have hmem := D.supportWithinDomain ha
    by_contra hne
    apply ha
    change D a = 0
    rw [hD, MeromorphicOn.AnalyticOnNhd.divisor_apply hFa hmem]
    rw [((hFa a hmem).analyticOrderAt_eq_zero).mpr hne]
    simp
  have hsimple : ∀ a ∈ S, ‖a‖ < r → (D a : ℝ) = 1 ∧ ∃ γ : SL(2, ℤ),
      γ ∈ CongruenceSubgroup.Gamma0 7 ∧ a = Function.Periodic.qParam 1 ((γ • horPt hy u : ℍ) : ℂ) := by
    intro a ha har
    have hFz := hzero a ha
    have ha0 : a ≠ 0 := by rintro rfl; exact hF0 hFz
    have hxa : xFun a = w := by simpa [hF, sub_eq_zero] using hFz
    obtain ⟨γ, hγ, hag, hda⟩ := zero_structure hy hfib hder (by linarith) ha0 hxa
    refine ⟨?_, γ, hγ, hag⟩
    have hmem : a ∈ closedBall (0 : ℂ) |r| := by
      rw [habs, mem_closedBall, dist_zero_right]; linarith
    have hdF : deriv F a ≠ 0 := by
      simp only [hF, deriv_sub_const]
      exact hda
    have hord := (hFa a hmem).analyticOrderAt_eq_one_of_zero_deriv_ne_zero hFz hdF
    rw [hD, MeromorphicOn.AnalyticOnNhd.divisor_apply hFa hmem, hord]
    simp
  have hterm : ∀ a ∈ S, (D a : ℝ) * L a ≤ if ‖a‖ < r then L a else 0 := by
    intro a ha
    have hmem := D.supportWithinDomain ((Set.Finite.mem_toFinset hfin).mp ha)
    rw [habs, mem_closedBall, dist_zero_right] at hmem
    split_ifs with h
    · rw [(hsimple a ha h).1, one_mul]
    · have hnr : ‖a‖ = r := le_antisymm hmem (not_lt.mp h)
      have : L a = 0 := by
        simp only [hL, zero_sub, norm_neg, hnr]
        rw [mul_inv_cancel₀ hr0.ne', Real.log_one]
      rw [this, mul_zero]
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.sum_filter]
  set S' := S.filter (fun a => ‖a‖ < r) with hS'
  -- every interior zero is `Φ(p)` for a row in the box
  have hsub : S' ⊆ (cosetBox y t).image (Phi hy u) := by
    intro a ha
    rw [hS', Finset.mem_filter] at ha
    obtain ⟨_, γ, hγ, hag⟩ := hsimple a ha.1 ha.2
    rw [Finset.mem_image]
    refine ⟨((normSL γ) 1 0, (normSL γ) 1 1), mem_cosetBox hy ht hu0 hu1 hγ ?_, ?_⟩
    · have hn := norm_qParam_smul γ (horPt hy u)
      rw [← hag] at hn
      have h2 := ha.2
      rw [hn, hr, Real.exp_lt_exp] at h2
      have := pi_pos
      nlinarith
    · rw [Phi_eq hy u hγ, hag]
  have hLnn : ∀ a, 0 ≤ max 0 (L a) := fun a => le_max_left _ _
  calc ∑ a ∈ S', L a ≤ ∑ a ∈ S', max 0 (L a) := Finset.sum_le_sum fun a _ => le_max_right _ _
    _ ≤ ∑ a ∈ (cosetBox y t).image (Phi hy u), max 0 (L a) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun a _ _ => hLnn a
    _ ≤ ∑ p ∈ cosetBox y t, max 0 (L (Phi hy u p)) :=
        Finset.sum_image_le_of_nonneg fun a _ => hLnn a
    _ = ∑ p ∈ cosetBox y t, orbitTerm y t u p := by
        refine Finset.sum_congr rfl fun p hp => ?_
        have hps : bottomShape p := (Finset.mem_filter.mp hp).2
        show max 0 (Real.log (r * ‖(0 : ℂ) - Phi hy u p‖⁻¹)) = _
        rw [zero_sub, norm_neg, hr, log_Phi hy u hps]

end Zeta7Valence

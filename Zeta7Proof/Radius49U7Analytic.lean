import Zeta7Proof.ValenceGeneric
import Zeta7Proof.LevelSevenTwoCusps
import Zeta7Proof.LevelSevenE6Quotient
import Zeta7Proof.LevelSevenFunctionIdentities

/-! Radius internalization, HM analytic input: the level-one trace method for `U₇`.

For `h_m = (49 x)^{-m}` (a `Γ₀(7)`-invariant function) the sum over the eight cosets
`Tr h_m (τ) = h_m(τ) + Σ_{k<7} x((τ+k)/7)^m` is `SL₂(ℤ)`-invariant (`traceFun_smul`), using the
explicit representatives `1, S Tᵏ` and `x(-1/z) = 1/(49 x(z/7))`. Subtracting a polynomial in
`j = 1728 E₄³/(E₄³ - E₆²)` that cancels the pole at `i∞` gives a level-one weight-zero modular
form tending to `0`, which therefore vanishes. With `j = P N³/x` (from the proved level-seven
`E₄`, `E₆` identities) this yields, for every certificate
`X^m p(X) = Σ_i q_i (P N³)^i X^{m-i} - 49^{-m}`,
the power-sum identity `Σ_{k<7} x((τ+k)/7)^m = p(x(τ))` near `i∞` (`powerSum_eventually`).
No published radius input is used. -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
open UpperHalfPlane Matrix.SpecialLinearGroup ModularForm Complex Filter Topology
open scoped MatrixGroups ModularForm Manifold
namespace Zeta7Radius49
open Zeta7LevelSeven Zeta7Valence

/-- `h_m = (49 x)^{-m}`. -/
def hfun (m : ℕ) (τ : ℍ) : ℂ := ((49 : ℂ) * etaCoordinate τ)⁻¹ ^ m

theorem hfun_gamma (m : ℕ) (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 7) (τ : ℍ) :
    hfun m (γ • τ) = hfun m τ := by
  simp only [hfun, x_gamma γ hγ τ]

/-- The level-one trace of `h_m` over the eight cosets of `Γ₀(7)`. -/
def traceFun (m : ℕ) (τ : ℍ) : ℂ := ∑ i : Fin 8, hfun m (cosetRep i • τ)

theorem cosetRep_mul_S (i : Fin 8) :
    cosetRep i * ModularGroup.S = schreierS i * cosetRep (nextS i) := by
  simp [schreierS, mul_assoc]

theorem cosetRep_mul_T (i : Fin 8) :
    cosetRep i * ModularGroup.T = schreierT i * cosetRep (nextT i) := by
  simp [schreierT, mul_assoc]

theorem nextT_bijective : Function.Bijective nextT := by
  have hs : Function.Surjective nextT := fun i => ⟨prevT i, nextT_prevT i⟩
  exact ⟨Finite.injective_iff_surjective.mpr hs, hs⟩

theorem traceFun_S (m : ℕ) (τ : ℍ) : traceFun m (ModularGroup.S • τ) = traceFun m τ := by
  unfold traceFun
  have h : ∀ i, hfun m (cosetRep i • ModularGroup.S • τ) = hfun m (cosetRep (nextS i) • τ) := by
    intro i
    rw [← mul_smul, cosetRep_mul_S, mul_smul, hfun_gamma _ _ (schreierS_mem i)]
  simp_rw [h]
  exact (Function.Involutive.bijective (fun i => nextS_involutive i)).sum_comp
    (fun i => hfun m (cosetRep i • τ))

theorem traceFun_T (m : ℕ) (τ : ℍ) : traceFun m (ModularGroup.T • τ) = traceFun m τ := by
  unfold traceFun
  have h : ∀ i, hfun m (cosetRep i • ModularGroup.T • τ) = hfun m (cosetRep (nextT i) • τ) := by
    intro i
    rw [← mul_smul, cosetRep_mul_T, mul_smul, hfun_gamma _ _ (schreierT_mem i)]
  simp_rw [h]
  exact nextT_bijective.sum_comp (fun i => hfun m (cosetRep i • τ))

/-- **`SL₂(ℤ)`-invariance of the trace.** -/
theorem traceFun_smul (m : ℕ) (γ : SL(2, ℤ)) (τ : ℍ) : traceFun m (γ • τ) = traceFun m τ := by
  have hγ : γ ∈ Subgroup.closure {ModularGroup.S, ModularGroup.T} := by
    simp [SpecialLinearGroup.SL2Z_generators]
  induction hγ using Subgroup.closure_induction generalizing τ with
  | mem g hg =>
    rcases hg with rfl | rfl
    · exact traceFun_S m τ
    · exact traceFun_T m τ
  | one => simp
  | mul g h _ _ ihg ihh => rw [mul_smul, ihg, ihh]
  | inv g _ ih =>
    have := ih (g⁻¹ • τ)
    rw [smul_inv_smul] at this
    exact this.symm

/-- The trace is `h_m + Σ_{k<7} x((τ+k)/7)^m`. -/
theorem traceFun_eq (m : ℕ) (τ : ℍ) :
    traceFun m τ = hfun m τ + ∑ k ∈ Finset.range 7, Xf (((τ : ℂ) + k) / 7) ^ m := by
  unfold traceFun
  have h0 : hfun m (cosetRep 0 • τ) = hfun m τ := by simp [cosetRep]
  have hs : ∀ k : Fin 7, hfun m (cosetRep k.succ • τ) =
      Xf (((τ : ℂ) + ((k : ℕ) : ℂ)) / 7) ^ m := by
    intro k
    have hk := k.isLt
    have hpos : 0 < ((τ : ℂ) + (k : ℕ)).im := by simp [τ.im_pos]
    have hw : 0 < (((τ : ℂ) + (k : ℕ)) / 7).im := by simp [τ.im_pos]
    have hsucc : (Fin.succ k : Fin 8) = ⟨(k : ℕ) + 1, by omega⟩ := rfl
    have hx : Xf (((τ : ℂ) + (k : ℕ)) / 7) ≠ 0 := Xf_ne_zero hw
    rw [hsucc, hfun, ← Xf_eq, cosetRep_smul (k : ℕ) hk τ, Xf_S hpos]
    rw [show (49 : ℂ) * (49 * Xf (((τ : ℂ) + (k : ℕ)) / 7))⁻¹ =
      (Xf (((τ : ℂ) + (k : ℕ)) / 7))⁻¹ by field_simp, inv_inv]
  rw [Fin.sum_univ_succ, h0, Finset.sum_congr rfl (fun k _ => hs k),
    Fin.sum_univ_eq_sum_range (fun k : ℕ => Xf (((τ : ℂ) + (k : ℂ)) / 7) ^ m)]

/-! ### The level-one `j`-function -/

/-- `j = 1728 E₄³ / (E₄³ - E₆²)`. -/
def Jfun (τ : ℍ) : ℂ := 1728 * classicalE4 τ ^ 3 / (classicalE4 τ ^ 3 - classicalE6 τ ^ 2)

theorem E4_smul (γ : SL(2, ℤ)) (τ : ℍ) :
    classicalE4 (γ • τ) = denom γ τ ^ 4 * classicalE4 τ := by
  have h := congrFun (classicalE4_slash γ) τ
  rw [SL_slash_apply] at h
  have hd := denom_ne_zero γ τ
  rw [← h, zpow_neg, zpow_ofNat]
  field_simp

theorem E6_smul (γ : SL(2, ℤ)) (τ : ℍ) :
    classicalE6 (γ • τ) = denom γ τ ^ 6 * classicalE6 τ := by
  have h := congrFun (classicalE6_slash γ) τ
  rw [SL_slash_apply] at h
  have hd := denom_ne_zero γ τ
  rw [← h, zpow_neg, zpow_ofNat]
  field_simp

theorem Jfun_smul (γ : SL(2, ℤ)) (τ : ℍ) : Jfun (γ • τ) = Jfun τ := by
  unfold Jfun
  rw [E4_smul, E6_smul]
  have hd := denom_ne_zero γ τ
  have hne := E4_cube_sub_E6_sq_ne τ
  have h12 : (denom γ τ ^ 4 * classicalE4 τ) ^ 3 - (denom γ τ ^ 6 * classicalE6 τ) ^ 2 =
      denom γ τ ^ 12 * (classicalE4 τ ^ 3 - classicalE6 τ ^ 2) := by ring
  rw [h12, mul_pow, show (denom γ τ ^ 4) ^ 3 = denom γ τ ^ 12 by ring, ← mul_assoc,
    mul_comm (1728 : ℂ), mul_assoc, mul_div_mul_left _ _ (pow_ne_zero 12 hd)]

/-- Near `i∞`, `j = P N³ / x`. -/
theorem Jfun_eq_of_P_ne (τ : ℍ) (hP : polyP (etaCoordinate τ) ≠ 0) :
    Jfun τ = polyP (etaCoordinate τ) * polyN (etaCoordinate τ) ^ 3 / etaCoordinate τ := by
  have hx : etaCoordinate τ ≠ 0 := by rw [← Xf_eq]; exact Xf_ne_zero τ.im_pos
  have h4 := E4_function τ
  have h6 := E6_function τ
  have hne := E4_cube_sub_E6_sq_ne τ
  set x := etaCoordinate τ
  set A := actualA τ
  set a := classicalE4 τ * polyP x
  set b := classicalE6 τ * polyP x ^ 2
  have key : 1728 * classicalE4 τ ^ 3 * x =
      polyP x * polyN x ^ 3 * (classicalE4 τ ^ 3 - classicalE6 τ ^ 2) := by
    apply mul_left_cancel₀ (pow_ne_zero 4 hP)
    have hid : polyP x * polyN x ^ 3 - polyT x ^ 2 = 1728 * x := by
      simp only [polyP, polyN, polyT]; ring
    linear_combination (polyP x * (1728 * x - polyP x * polyN x ^ 3) *
        (a ^ 2 + a * (A ^ 2 * polyN x) + (A ^ 2 * polyN x) ^ 2)) * h4 +
      (polyP x * polyN x ^ 3 * (b + A ^ 3 * polyT x)) * h6 -
      (polyP x * A ^ 6 * polyN x ^ 3) * hid
  rw [Jfun, div_eq_div_iff hne hx]
  linear_combination key

/-! ### The power-sum identities -/

theorem tendsto_Xf_shift (k : ℕ) :
    Tendsto (fun τ : ℍ => Xf (((τ : ℂ) + k) / 7)) atImInfty (𝓝 0) := by
  have h := etaCoordinate_tendsto'.comp (shiftSeven_tendsto k)
  have he : ((fun z : ℍ => Xf z) ∘ shiftSeven k) = fun τ : ℍ => Xf (((τ : ℂ) + k) / 7) := by
    funext τ; rfl
  rwa [he] at h

theorem eventually_P_ne : ∀ᶠ τ in atImInfty, polyP (etaCoordinate τ) ≠ 0 := by
  have h := etaCoordinate_tendsto.eventually (Metric.ball_mem_nhds (0 : ℂ) (by norm_num :
    (0 : ℝ) < 1 / 100))
  filter_upwards [h] with τ hτ
  rw [dist_zero_right] at hτ
  intro h0
  have hP : ‖13 * etaCoordinate τ + 49 * etaCoordinate τ ^ 2‖ < 1 := by
    calc ‖13 * etaCoordinate τ + 49 * etaCoordinate τ ^ 2‖
        ≤ 13 * ‖etaCoordinate τ‖ + 49 * ‖etaCoordinate τ‖ ^ 2 := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_mul, norm_pow]; norm_num
      _ < 1 := by nlinarith [norm_nonneg (etaCoordinate τ)]
  have : 13 * etaCoordinate τ + 49 * etaCoordinate τ ^ 2 = -1 := by
    simp only [polyP] at h0; linear_combination h0
  rw [this, norm_neg, norm_one] at hP
  exact lt_irrefl _ hP

theorem traceFun_holo (m : ℕ) : MDiff (traceFun m) := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  have heq : ∀ z ∈ Hset, (traceFun m ∘ ofComplex) z =
      ((49 : ℂ) * Xf z)⁻¹ ^ m + ∑ k ∈ Finset.range 7, Xf ((z + k) / 7) ^ m := by
    intro z hz
    simp only [Function.comp_apply]
    rw [traceFun_eq, hfun, ← Xf_eq, ofComplex_apply_of_im_pos hz]
  refine DifferentiableOn.congr ?_ heq
  intro z hz
  change 0 < z.im at hz
  apply DifferentiableAt.differentiableWithinAt
  apply DifferentiableAt.add
  · exact ((Xf_differentiableOn.differentiableAt (Hset_isOpen.mem_nhds hz)).const_mul 49).inv
      (mul_ne_zero (by norm_num) (Xf_ne_zero hz)) |>.pow m
  · apply DifferentiableAt.fun_sum
    intro k _
    have hw : 0 < ((z + k) / 7).im := by simp; linarith
    have hd : DifferentiableAt ℂ (fun y : ℂ => Xf ((y + k) / 7)) z :=
      DifferentiableAt.comp (g := Xf) (f := fun y : ℂ => (y + k) / 7) z
        (Xf_differentiableOn.differentiableAt (Hset_isOpen.mem_nhds hw))
        ((differentiableAt_id.add_const _).div_const _)
    exact hd.pow m

theorem Jfun_holo : MDiff Jfun := by
  have h4 : MDiff (classicalE4 : ℍ → ℂ) := ModularFormClass.holo classicalE4
  have h6 : MDiff (classicalE6 : ℍ → ℂ) := ModularFormClass.holo classicalE6
  rw [UpperHalfPlane.mdifferentiable_iff] at h4 h6 ⊢
  intro z hz
  have hd : (classicalE4 ∘ ofComplex) z ^ 3 - (classicalE6 ∘ ofComplex) z ^ 2 ≠ 0 := by
    simp only [Function.comp_apply]; exact E4_cube_sub_E6_sq_ne _
  exact (((h4 z hz).pow 3).const_mul 1728).div (((h4 z hz).pow 3).sub ((h6 z hz).pow 2)) hd

/-- A polynomial in `j`. -/
def qTrace (m : ℕ) (q : ℕ → ℂ) (τ : ℍ) : ℂ := ∑ i ∈ Finset.range (m + 1), q i * Jfun τ ^ i

/-- The level-one form `Tr h_m - Q_m(j)`. -/
def diffFun (m : ℕ) (q : ℕ → ℂ) (τ : ℍ) : ℂ := traceFun m τ - qTrace m q τ

theorem diffFun_smul (m : ℕ) (q : ℕ → ℂ) (γ : SL(2, ℤ)) (τ : ℍ) :
    diffFun m q (γ • τ) = diffFun m q τ := by
  simp only [diffFun, qTrace, traceFun_smul, Jfun_smul]

theorem diffFun_slash (m : ℕ) (q : ℕ → ℂ) (γ : SL(2, ℤ)) :
    diffFun m q ∣[(0 : ℤ)] γ = diffFun m q := by
  funext τ
  rw [SL_slash_apply, diffFun_smul]
  simp

theorem diffFun_holo (m : ℕ) (q : ℕ → ℂ) : MDiff (diffFun m q) := by
  unfold diffFun
  apply (traceFun_holo m).sub
  have he : qTrace m q = ∑ i ∈ Finset.range (m + 1), (fun τ : ℍ => q i * Jfun τ ^ i) := by
    funext τ; simp [qTrace, Finset.sum_apply]
  rw [he]
  apply MDifferentiable.sum
  intro i _
  exact mdifferentiable_const.mul (Jfun_holo.pow i)

/-- **The generic power-sum identity.** A trace certificate gives the power sum of the seven
`U₇` branches near `i∞`. -/
theorem powerSum_eventually (m : ℕ) (hm : 0 < m) (q : ℕ → ℂ) (p : ℂ → ℂ) (hpc : ContinuousAt p 0)
    (hp0 : p 0 = 0)
    (hcert : ∀ X : ℂ, X ≠ 0 → X ^ m * p X =
      ∑ i ∈ Finset.range (m + 1), q i * (polyP X * polyN X ^ 3) ^ i * X ^ (m - i) -
        (1 / 49 : ℂ) ^ m) :
    ∀ᶠ τ : ℍ in atImInfty,
      ∑ k ∈ Finset.range 7, Xf (((τ : ℂ) + k) / 7) ^ m = p (etaCoordinate τ) := by
  -- near `i∞`, `diffFun` is the power sum minus `p(x)`
  have hnear : ∀ᶠ τ : ℍ in atImInfty, diffFun m q τ =
      ∑ k ∈ Finset.range 7, Xf (((τ : ℂ) + k) / 7) ^ m - p (etaCoordinate τ) := by
    filter_upwards [eventually_P_ne] with τ hP
    have hx : etaCoordinate τ ≠ 0 := by rw [← Xf_eq]; exact Xf_ne_zero τ.im_pos
    have hc := hcert _ hx
    rw [diffFun, traceFun_eq, qTrace, Jfun_eq_of_P_ne τ hP]
    have hsum : ∑ i ∈ Finset.range (m + 1), q i *
        (polyP (etaCoordinate τ) * polyN (etaCoordinate τ) ^ 3 / etaCoordinate τ) ^ i =
        (etaCoordinate τ ^ m)⁻¹ * (∑ i ∈ Finset.range (m + 1), q i *
          (polyP (etaCoordinate τ) * polyN (etaCoordinate τ) ^ 3) ^ i *
            etaCoordinate τ ^ (m - i)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      have hi' : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      rw [div_pow]
      have hsplit : etaCoordinate τ ^ m = etaCoordinate τ ^ i * etaCoordinate τ ^ (m - i) := by
        rw [← pow_add, Nat.add_sub_cancel' hi']
      rw [hsplit]
      field_simp
    have hS : (∑ i ∈ Finset.range (m + 1), q i *
        (polyP (etaCoordinate τ) * polyN (etaCoordinate τ) ^ 3) ^ i * etaCoordinate τ ^ (m - i)) =
        etaCoordinate τ ^ m * p (etaCoordinate τ) + (1 / 49 : ℂ) ^ m := by
      rw [hc]; ring
    have hxm : etaCoordinate τ ^ m ≠ 0 := pow_ne_zero _ hx
    have hh : ((49 : ℂ) * etaCoordinate τ)⁻¹ ^ m = (1 / 49 : ℂ) ^ m * (etaCoordinate τ ^ m)⁻¹ := by
      rw [mul_inv, mul_pow, one_div, inv_pow, inv_pow]
    rw [hsum, hS, hfun, hh, mul_add, inv_mul_cancel_left₀ hxm]
    ring
  -- the level-one form
  let F : SlashInvariantForm GammaSeven 0 :=
    { toFun := diffFun m q
      slash_action_eq' := by
        intro γ hγ
        obtain ⟨δ, _, rfl⟩ := hγ
        simpa [SL_slash, mapGL] using diffFun_slash m q δ }
  have hlim : Tendsto (diffFun m q) atImInfty (𝓝 0) := by
    have hs : Tendsto (fun τ : ℍ => ∑ k ∈ Finset.range 7, Xf (((τ : ℂ) + k) / 7) ^ m -
        p (etaCoordinate τ)) atImInfty (𝓝 0) := by
      have h1 : Tendsto (fun τ : ℍ => ∑ k ∈ Finset.range 7, Xf (((τ : ℂ) + k) / 7) ^ m)
          atImInfty (𝓝 (∑ k ∈ Finset.range 7, (0 : ℂ) ^ m)) :=
        tendsto_finsetSum _ fun k _ => (tendsto_Xf_shift k).pow m
      have h2 : Tendsto (fun τ : ℍ => p (etaCoordinate τ)) atImInfty (𝓝 (p 0)) :=
        hpc.tendsto.comp etaCoordinate_tendsto
      have h1' := h1.sub h2
      simpa [hp0, zero_pow hm.ne'] using h1'
    exact hs.congr' (hnear.mono fun τ hτ => hτ.symm)
  have hbdd : IsBoundedAtImInfty (diffFun m q) := hlim.isBigO_one ℝ
  let G : ModularForm GammaSeven 0 :=
    levelSevenFormOfTwoCusps F (diffFun_holo m q) hbdd (by
      change IsBoundedAtImInfty (diffFun m q ∣[(0 : ℤ)] ModularGroup.S)
      rw [diffFun_slash]; exact hbdd)
  obtain ⟨c, hc⟩ := ModularForm.eq_const_of_weight_zero G
  have hG : (G : ℍ → ℂ) = diffFun m q := rfl
  rw [hG] at hc
  have hc0 : c = 0 := by
    have := hlim
    rw [hc] at this
    exact tendsto_nhds_unique tendsto_const_nhds this
  filter_upwards [hnear] with τ hτ
  have h0 : diffFun m q τ = 0 := by rw [hc, hc0]; rfl
  rw [h0] at hτ
  exact (sub_eq_zero.mp hτ.symm)

end Zeta7Radius49

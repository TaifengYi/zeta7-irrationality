import Zeta7Proof.AuxiliaryResonanceShifts

/-! Layer calculus for the actual source columns: total residue layers, congruence below `N`,
the cap submodules of the actual integral source and their reductions, and the kernel-lifting
rank bound used for the joint third and fourth layers. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
namespace Zeta7Auxiliary
open PowerSeries Zeta7Common

variable {p : ℕ} [Fact p.Prime]

/-! ### Total residues -/

open Classical in
/-- The residue of an integral element; `0` otherwise (the junk value is never used). -/
def resid (z : ℚ_[p]) : ZMod p := if h : Integral z then integralResidue z h else 0

theorem resid_eq {z : ℚ_[p]} (h : Integral z) : resid z = integralResidue z h := by
  rw [resid, dif_pos h]

theorem resid_coe (a : ℤ_[p]) : resid (a : ℚ_[p]) = PadicInt.toZMod a := by
  rw [resid_eq (integral_coe a)]
  rfl

theorem resid_add {x y : ℚ_[p]} (hx : Integral x) (hy : Integral y) :
    resid (x + y) = resid x + resid y := by
  rw [resid_eq hx, resid_eq hy, resid_eq (hx.add hy), integralResidue_add]

theorem resid_mul {x y : ℚ_[p]} (hx : Integral x) (hy : Integral y) :
    resid (x * y) = resid x * resid y := by
  rw [resid_eq hx, resid_eq hy, resid_eq (hx.mul hy), integralResidue_mul]

theorem resid_zero : resid (0 : ℚ_[p]) = 0 := by
  simpa using resid_coe (p := p) 0

theorem resid_neg {x : ℚ_[p]} (hx : Integral x) : resid (-x) = -resid x := by
  have h := resid_add hx hx.neg
  rw [add_neg_cancel, resid_zero] at h
  linear_combination h.symm

theorem resid_p_mul {x : ℚ_[p]} (hx : Integral x) : resid ((p : ℚ_[p]) * x) = 0 := by
  rw [resid_mul (integral_nat p) hx]
  have : resid ((p : ℚ_[p])) = 0 := by
    simpa using resid_coe (p := p) (p : ℤ_[p])
  rw [this, zero_mul]

theorem resid_sum {ι : Type*} (s : Finset ι) (f : ι → ℚ_[p]) (h : ∀ i ∈ s, Integral (f i)) :
    resid (∑ i ∈ s, f i) = ∑ i ∈ s, resid (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using resid_zero
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi,
      resid_add (h i (Finset.mem_insert_self _ _))
        (integral_sum s f fun j hj => h j (Finset.mem_insert_of_mem hj)),
      ih fun j hj => h j (Finset.mem_insert_of_mem hj)]

/-! ### Layer series and congruence below `N` -/

/-- The `e`-th layer of a series, as a total series over `ZMod p`. -/
def laySeries (e : ℕ) (F : PowerSeries ℚ_[p]) : PowerSeries (ZMod p) :=
  mk fun n => resid ((p : ℚ_[p]) ^ e * coeff n F)

theorem coeff_laySeries (e n : ℕ) (F : PowerSeries ℚ_[p]) :
    coeff n (laySeries e F) = resid ((p : ℚ_[p]) ^ e * coeff n F) := coeff_mk _ _

theorem laySeries_eq_layer {N e : ℕ} {F : PowerSeries ℚ_[p]} (h : Cap N e F) (n : Fin N) :
    coeff n.val (laySeries e F) = layerCoefficient h n := by
  rw [coeff_laySeries, resid_eq (h n.val n.isLt), layerCoefficient_eq_residue]

/-- Coefficientwise equality below `N`. -/
def EqBelow (N : ℕ) (f g : PowerSeries (ZMod p)) : Prop := ∀ n, n < N → coeff n f = coeff n g

theorem EqBelow.refl (N : ℕ) (f : PowerSeries (ZMod p)) : EqBelow N f f := fun _ _ => rfl

theorem EqBelow.symm {N : ℕ} {f g : PowerSeries (ZMod p)} (h : EqBelow N f g) : EqBelow N g f :=
  fun n hn => (h n hn).symm

theorem EqBelow.trans {N : ℕ} {f g k : PowerSeries (ZMod p)} (h : EqBelow N f g)
    (h' : EqBelow N g k) : EqBelow N f k := fun n hn => (h n hn).trans (h' n hn)

theorem EqBelow.add {N : ℕ} {f g f' g' : PowerSeries (ZMod p)} (h : EqBelow N f f')
    (h' : EqBelow N g g') : EqBelow N (f + g) (f' + g') := fun n hn => by
  rw [map_add, map_add, h n hn, h' n hn]

theorem EqBelow.neg {N : ℕ} {f f' : PowerSeries (ZMod p)} (h : EqBelow N f f') :
    EqBelow N (-f) (-f') := fun n hn => by rw [map_neg, map_neg, h n hn]

theorem EqBelow.sub {N : ℕ} {f g f' g' : PowerSeries (ZMod p)} (h : EqBelow N f f')
    (h' : EqBelow N g g') : EqBelow N (f - g) (f' - g') := fun n hn => by
  rw [map_sub, map_sub, h n hn, h' n hn]

theorem EqBelow.mul {N : ℕ} {f g f' g' : PowerSeries (ZMod p)} (h : EqBelow N f f')
    (h' : EqBelow N g g') : EqBelow N (f * g) (f' * g') := fun n hn => by
  rw [coeff_mul, coeff_mul]
  refine Finset.sum_congr rfl fun ij hij => ?_
  have hs : ij.1 + ij.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  rw [h ij.1 (by omega), h' ij.2 (by omega)]

theorem EqBelow.mul_left {N : ℕ} {g g' : PowerSeries (ZMod p)} (f : PowerSeries (ZMod p))
    (h : EqBelow N g g') : EqBelow N (f * g) (f * g') := (EqBelow.refl N f).mul h

theorem EqBelow.euler {N : ℕ} {f f' : PowerSeries (ZMod p)} (h : EqBelow N f f') :
    EqBelow N (euler f) (euler f') := fun n hn => by
  rw [euler_coeff, euler_coeff, h n hn]

theorem EqBelow.of_eq {N : ℕ} {f g : PowerSeries (ZMod p)} (h : f = g) : EqBelow N f g :=
  fun _ _ => by rw [h]

theorem eqBelow_sum {N : ℕ} {ι : Type*} (s : Finset ι) (f g : ι → PowerSeries (ZMod p))
    (h : ∀ i ∈ s, EqBelow N (f i) (g i)) : EqBelow N (∑ i ∈ s, f i) (∑ i ∈ s, g i) :=
  fun n hn => by
    rw [map_sum, map_sum]
    exact Finset.sum_congr rfl fun i hi => h i hi n hn

/-! ### Layers of combinations -/

theorem lay_add {N e : ℕ} {F G : PowerSeries ℚ_[p]} (hF : Cap N e F) (hG : Cap N e G) :
    EqBelow N (laySeries e (F + G)) (laySeries e F + laySeries e G) := fun n hn => by
  rw [map_add, coeff_laySeries, coeff_laySeries, coeff_laySeries, map_add, mul_add,
    resid_add (hF n hn) (hG n hn)]

theorem lay_neg {N e : ℕ} {F : PowerSeries ℚ_[p]} (hF : Cap N e F) :
    EqBelow N (laySeries e (-F)) (-laySeries e F) := fun n hn => by
  rw [map_neg, coeff_laySeries, coeff_laySeries, map_neg, mul_neg, resid_neg (hF n hn)]

theorem lay_sub {N e : ℕ} {F G : PowerSeries ℚ_[p]} (hF : Cap N e F) (hG : Cap N e G) :
    EqBelow N (laySeries e (F - G)) (laySeries e F - laySeries e G) := by
  rw [sub_eq_add_neg, sub_eq_add_neg]
  exact (lay_add hF hG.neg).trans ((EqBelow.refl N _).add (lay_neg hG))

/-- Multiplication by an integral series commutes with layers below `N`. -/
theorem lay_mul {N e : ℕ} {G F : PowerSeries ℚ_[p]} (hG : Cap N 0 G) (hF : Cap N e F) :
    EqBelow N (laySeries e (G * F)) (laySeries 0 G * laySeries e F) := fun n hn => by
  rw [coeff_laySeries, coeff_mul, coeff_mul, Finset.mul_sum]
  rw [resid_sum]
  · refine Finset.sum_congr rfl fun ij hij => ?_
    have hs : ij.1 + ij.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
    have hg := hG ij.1 (by omega)
    have hf := hF ij.2 (by omega)
    rw [pow_zero, one_mul] at hg
    rw [coeff_laySeries, coeff_laySeries, pow_zero, one_mul, ← resid_mul hg hf]
    congr 1
    ring
  · intro ij hij
    have hs : ij.1 + ij.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
    have hg := hG ij.1 (by omega)
    have hf := hF ij.2 (by omega)
    rw [pow_zero, one_mul] at hg
    have := hg.mul hf
    convert this using 1
    ring

theorem laySeries_zero_zpMap (a : PowerSeries ℤ_[p]) :
    laySeries 0 (zpMap (p := p) a) = PowerSeries.map PadicInt.toZMod a := by
  ext n
  rw [coeff_laySeries, pow_zero, one_mul, coeff_map, coeff_map]
  exact resid_coe _

theorem lay_C_mul {N e : ℕ} {F : PowerSeries ℚ_[p]} (hF : Cap N e F) (a : ℤ_[p]) :
    EqBelow N (laySeries e (C (a : ℚ_[p]) * F)) (C (PadicInt.toZMod a) * laySeries e F) :=
  fun n hn => by
    rw [coeff_laySeries, coeff_C_mul, coeff_C_mul, coeff_laySeries, mul_left_comm,
      resid_mul (integral_coe a) (hF n hn), resid_coe]

theorem lay_X_pow_mul (e t : ℕ) (F : PowerSeries ℚ_[p]) :
    laySeries e (X ^ t * F) = X ^ t * laySeries e F := by
  ext n
  rw [coeff_laySeries, coeff_X_pow_mul', coeff_X_pow_mul']
  split_ifs
  · rw [coeff_laySeries]
  · rw [mul_zero, resid_zero]

theorem lay_euler {N e : ℕ} {F : PowerSeries ℚ_[p]} (hF : Cap N e F) :
    EqBelow N (laySeries e (Zeta7Common.euler F)) (Zeta7Common.euler (laySeries e F)) :=
  fun n hn => by
    rw [coeff_laySeries, euler_coeff, euler_coeff, coeff_laySeries, mul_left_comm,
      resid_mul (integral_nat n) (hF n hn)]
    congr 1
    simpa using resid_coe (p := p) (n : ℤ_[p])

/-- A series with a lower cap has vanishing next layer. -/
theorem lay_succ_zero {N e : ℕ} {F : PowerSeries ℚ_[p]} (hF : Cap N e F) :
    EqBelow N (laySeries (e + 1) F) 0 := fun n hn => by
  rw [coeff_laySeries, map_zero, pow_succ, mul_comm ((p : ℚ_[p]) ^ e), mul_assoc,
    resid_p_mul (hF n hn)]

/-- Vanishing layer below `N` improves the cap. -/
theorem Cap.improve_of_lay {N e : ℕ} {F : PowerSeries ℚ_[p]} (hF : Cap N (e + 1) F)
    (hz : EqBelow N (laySeries (e + 1) F) 0) : Cap N e F := by
  apply hF.improve
  intro n
  rw [← laySeries_eq_layer hF n, hz n.val n.isLt, map_zero]

theorem Cap.zero' (N e : ℕ) : Cap N e (0 : PowerSeries ℚ_[p]) := by
  intro n _
  rw [map_zero, mul_zero]
  exact integral_zero

/-! ### Linearity of the actual source map -/

theorem actualSourceSeries_add (d : ℕ) (c : ℚ) (v w : TailIndex d → ℤ_[p]) :
    actualSourceSeries p d c (v + w) = actualSourceSeries p d c v + actualSourceSeries p d c w := by
  simp only [actualSourceSeries, Pi.add_apply, PadicInt.coe_add, map_add, add_mul,
    Finset.sum_add_distrib]

theorem actualSourceSeries_smul (d : ℕ) (c : ℚ) (a : ℤ_[p]) (v : TailIndex d → ℤ_[p]) :
    actualSourceSeries p d c (a • v) = C (a : ℚ_[p]) * actualSourceSeries p d c v := by
  simp only [actualSourceSeries, Pi.smul_apply, smul_eq_mul, PadicInt.coe_mul, map_mul,
    Finset.mul_sum, mul_assoc]

theorem actualSourceSeries_zero (d : ℕ) (c : ℚ) :
    actualSourceSeries p d c 0 = 0 := by
  simp [actualSourceSeries]

theorem actualSourceSeries_sum (d : ℕ) (c : ℚ) {κ : Type*} (s : Finset κ)
    (a : κ → ℤ_[p]) (G : κ → TailIndex d → ℤ_[p]) :
    actualSourceSeries p d c (∑ i ∈ s, a i • G i) =
      ∑ i ∈ s, C (a i : ℚ_[p]) * actualSourceSeries p d c (G i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [actualSourceSeries_zero]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, actualSourceSeries_add,
      actualSourceSeries_smul, ih]

theorem cap_sum_smul {N e : ℕ} {κ : Type*} (s : Finset κ) (a : κ → ℤ_[p])
    (F : κ → PowerSeries ℚ_[p]) (hF : ∀ i ∈ s, Cap N e (F i)) :
    Cap N e (∑ i ∈ s, C (a i : ℚ_[p]) * F i) :=
  Cap.sum s _ fun i hi => (hF i hi).const_mul (a i)

theorem lay_sum_smul {N e : ℕ} {κ : Type*} (s : Finset κ) (a : κ → ℤ_[p])
    (F : κ → PowerSeries ℚ_[p]) (hF : ∀ i ∈ s, Cap N e (F i)) :
    EqBelow N (laySeries e (∑ i ∈ s, C (a i : ℚ_[p]) * F i))
      (∑ i ∈ s, C (PadicInt.toZMod (a i)) * laySeries e (F i)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro n _
    simp [coeff_laySeries, resid_zero]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    have hi' := hF i (Finset.mem_insert_self _ _)
    have hs : ∀ j ∈ s, Cap N e (F j) := fun j hj => hF j (Finset.mem_insert_of_mem hj)
    exact (lay_add (hi'.const_mul (a i)) (cap_sum_smul s a F hs)).trans
      ((lay_C_mul hi' (a i)).add (ih hs))

/-! ### Cap submodules of the actual source and their reductions -/

/-- The reductions of actual integral source vectors whose column has cap `e` below `N`. -/
def capRed (d : ℕ) (c : ℚ) (N e : ℕ) : Submodule (ZMod p) (TailIndex d → ZMod p) where
  carrier := {w | ∃ v, Cap N e (actualSourceSeries p d c v) ∧ redV (p := p) (TailIndex d) v = w}
  add_mem' := by
    rintro _ _ ⟨v, hv, rfl⟩ ⟨w, hw, rfl⟩
    refine ⟨v + w, ?_, map_add _ _ _⟩
    rw [actualSourceSeries_add]
    exact hv.add hw
  zero_mem' := ⟨0, by rw [actualSourceSeries_zero]; exact Cap.zero' N e, map_zero _⟩
  smul_mem' := by
    rintro a _ ⟨v, hv, rfl⟩
    refine ⟨liftZ a • v, ?_, ?_⟩
    · rw [actualSourceSeries_smul]
      exact hv.const_mul _
    · rw [map_smulₛₗ, toZMod_liftZ]

theorem mem_capRed {d : ℕ} {c : ℚ} {N e : ℕ} (v : TailIndex d → ℤ_[p])
    (hv : Cap N e (actualSourceSeries p d c v)) :
    redV (p := p) (TailIndex d) v ∈ capRed (p := p) d c N e := ⟨v, hv, rfl⟩

theorem capRed_mono {d : ℕ} {c : ℚ} {N e f : ℕ} (hef : e ≤ f) :
    capRed (p := p) d c N e ≤ capRed (p := p) d c N f := by
  rintro _ ⟨v, hv, rfl⟩
  exact ⟨v, hv.mono hef, rfl⟩

/-- An independent family of reductions inside a submodule bounds its dimension. -/
theorem card_le_finrank_of_family {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    [FiniteDimensional (ZMod p) V] {κ : Type*} [Fintype κ]
    (S : Submodule (ZMod p) V) (f : κ → V) (hf : LinearIndependent (ZMod p) f)
    (hS : ∀ i, f i ∈ S) : Fintype.card κ ≤ Module.finrank (ZMod p) S := by
  rw [← finrank_span_eq_card hf]
  apply Submodule.finrank_mono
  rw [Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  exact hS i

/-- Truncation below `N` as a linear map. -/
def truncL (N : ℕ) : PowerSeries (ZMod p) →ₗ[ZMod p] (Fin N → ZMod p) where
  toFun f n := coeff n.val f
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

theorem truncL_congr {N : ℕ} {f g : PowerSeries (ZMod p)} (h : EqBelow N f g) :
    truncL N f = truncL N g := by
  ext n
  exact h n.val n.isLt

/-- **Kernel lifting.** Let `G` be actual source vectors of cap `e+1` with independent
reductions, whose `(e+1)`-layers truncated below `N` lie in a subspace `T`. Then the reductions of
cap-`e` vectors have dimension at least `card κ - dim T`. The lifted kernel vectors are genuine
integral combinations of the `G i`. -/
theorem capRed_kernel_bound (d : ℕ) (c : ℚ) (N e : ℕ) {κ : Type*} [Fintype κ] [DecidableEq κ]
    (G : κ → TailIndex d → ℤ_[p]) (hG : ∀ i, Cap N (e + 1) (actualSourceSeries p d c (G i)))
    (hind : LinearIndependent (ZMod p) (fun i => redV (p := p) (TailIndex d) (G i)))
    (T : Submodule (ZMod p) (Fin N → ZMod p))
    (hT : ∀ i, truncL N (laySeries (e + 1) (actualSourceSeries p d c (G i))) ∈ T) :
    Fintype.card κ ≤ Module.finrank (ZMod p) (capRed (p := p) d c N e) +
      Module.finrank (ZMod p) T := by
  classical
  let t : κ → Fin N → ZMod p := fun i => truncL N (laySeries (e + 1) (actualSourceSeries p d c (G i)))
  let Φ : (κ → ZMod p) →ₗ[ZMod p] (Fin N → ZMod p) :=
    ∑ i, (LinearMap.proj i).smulRight (t i)
  have hΦ : ∀ a, Φ a = ∑ i, a i • t i := fun a => by
    simp [Φ, LinearMap.sum_apply]
  let Ψ : (κ → ZMod p) →ₗ[ZMod p] (TailIndex d → ZMod p) :=
    ∑ i, (LinearMap.proj i).smulRight (redV (p := p) (TailIndex d) (G i))
  have hΨ : ∀ a, Ψ a = ∑ i, a i • redV (p := p) (TailIndex d) (G i) := fun a => by
    simp [Ψ, LinearMap.sum_apply]
  have hΨinj : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    rw [hΨ] at ha
    ext i
    exact (linearIndependent_iff'.mp hind) Finset.univ a ha i (Finset.mem_univ _)
  have hrange : LinearMap.range Φ ≤ T := by
    rintro _ ⟨a, rfl⟩
    rw [hΦ]
    exact T.sum_mem fun i _ => T.smul_mem _ (hT i)
  have hker : (LinearMap.ker Φ).map Ψ ≤ capRed (p := p) d c N e := by
    rintro _ ⟨a, ha, rfl⟩
    have ha0 : Φ a = 0 := ha
    rw [hΦ] at ha0
    let v : TailIndex d → ℤ_[p] := ∑ i, liftZ (a i) • G i
    have hser := actualSourceSeries_sum (p := p) d c Finset.univ (fun i => liftZ (a i)) G
    have hcap : Cap N (e + 1) (actualSourceSeries p d c v) := by
      rw [hser]
      exact cap_sum_smul _ _ _ fun i _ => hG i
    have hlay := lay_sum_smul (N := N) (e := e + 1) Finset.univ (fun i => liftZ (a i))
      (fun i => actualSourceSeries p d c (G i)) fun i _ => hG i
    have hz : EqBelow N (laySeries (e + 1) (actualSourceSeries p d c v)) 0 := by
      intro n hn
      rw [hser, hlay n hn, map_zero, map_sum]
      simp only [coeff_C_mul, toZMod_liftZ]
      have := congrFun ha0 ⟨n, hn⟩
      simpa [t, truncL] using this
    refine ⟨v, hcap.improve_of_lay hz, ?_⟩
    rw [hΨ, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smulₛₗ, toZMod_liftZ]
  have h1 := Submodule.finrank_mono hker
  rw [← (Submodule.equivMapOfInjective Ψ hΨinj (LinearMap.ker Φ)).finrank_eq] at h1
  have h2 := Submodule.finrank_mono hrange
  have h3 := LinearMap.finrank_range_add_finrank_ker Φ
  rw [Module.finrank_fintype_fun_eq_card] at h3
  omega

end Zeta7Auxiliary

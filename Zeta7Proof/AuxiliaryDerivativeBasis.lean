import Zeta7Proof.AuxiliaryDerivativeKernel
import Zeta7Proof.AuxiliaryLatticeAlgebra
import Zeta7Proof.AuxiliarySimultaneousCounts

/-! P4 completed for the actual derivative block: an integral source basis of the three
derivative germs with the exact kernel of `F₀` (cap two) and the lifted reduced kernel of
`F₁` inside it (cap one), with the counts `derivativeThree`, `derivativeTwo`,
`derivativeOne`. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
namespace Zeta7Auxiliary
open Zeta7Common

variable {p : ℕ} [Fact p.Prime]

abbrev DIdx (d : ℕ) := Fin 3 × Fin d

/-- The polynomial of degree `< d` attached to derivative germ `k`. -/
def dpoly {d : ℕ} (a : DIdx d → ℤ_[p]) (k : Fin 3) : Polynomial ℤ_[p] :=
  ∑ i : Fin d, Polynomial.C (a (k, i)) * Polynomial.X ^ (i : ℕ)

def dpolyL (d : ℕ) (k : Fin 3) : (DIdx d → ℤ_[p]) →ₗ[ℤ_[p]] Polynomial ℤ_[p] where
  toFun a := dpoly a k
  map_add' a b := by simp [dpoly, add_mul, Finset.sum_add_distrib]
  map_smul' c a := by
    simp [dpoly, Finset.smul_sum, Polynomial.smul_eq_C_mul, mul_assoc]

theorem dpoly_natDegree {d : ℕ} (a : DIdx d → ℤ_[p]) (k : Fin 3) :
    (dpoly a k).natDegree ≤ d - 1 := by
  unfold dpoly
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i _
  exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (by omega)

/-- The cleared exact map `(PQ)² F₀` on derivative source vectors. -/
def phi0 (hp : 11 ≤ p) (d : ℕ) : (DIdx d → ℤ_[p]) →ₗ[ℤ_[p]] Polynomial ℤ_[p] :=
  (LinearMap.mulLeft ℤ_[p] ((intPolyP p * integralQuotientPolynomial p (hp5 hp))^2)).comp
      (dpolyL d 0) +
    (LinearMap.mulLeft ℤ_[p] ((intPolyP p * integralQuotientPolynomial p (hp5 hp)) *
      rhoPoly p (hp5 hp))).comp (dpolyL d 1) +
    (LinearMap.mulLeft ℤ_[p] (Polynomial.C (halfZ p (hp2 hp)) *
      (integralQuotientPolynomial p (hp5 hp)^2 * intPolyW p + rhoPoly p (hp5 hp)^2))).comp
      (dpolyL d 2)

theorem phi0_apply (hp : 11 ≤ p) (d : ℕ) (a : DIdx d → ℤ_[p]) :
    phi0 hp d a = clearedF0 p hp (dpoly a 0) (dpoly a 1) (dpoly a 2) := rfl

theorem phi0_mem (hp : 11 ≤ p) (d : ℕ) (hd : 1 ≤ d) (a : DIdx d → ℤ_[p]) :
    phi0 hp d a ∈ Polynomial.degreeLT ℤ_[p] (derivativeBudget d p) := by
  rw [Polynomial.mem_degreeLT, phi0_apply]
  have h := clearedF0_natDegree hp _ _ _ (d-1) (dpoly_natDegree a 0) (dpoly_natDegree a 1)
    (dpoly_natDegree a 2)
  refine Polynomial.degree_le_natDegree.trans_lt ?_
  exact_mod_cast (show _ < derivativeBudget d p by unfold derivativeBudget; omega)

def phi0F (hp : 11 ≤ p) (d : ℕ) (hd : 1 ≤ d) :
    (DIdx d → ℤ_[p]) →ₗ[ℤ_[p]] (Fin (derivativeBudget d p) → ℤ_[p]) :=
  (Polynomial.degreeLTEquiv ℤ_[p] (derivativeBudget d p)).toLinearMap.comp
    ((phi0 hp d).codRestrict _ (phi0_mem hp d hd))

theorem phi0F_eq_zero (hp : 11 ≤ p) (d : ℕ) (hd : 1 ≤ d) (a : DIdx d → ℤ_[p])
    (h : phi0F hp d hd a = 0) : phi0 hp d a = 0 := by
  have h' := (LinearEquiv.map_eq_zero_iff (Polynomial.degreeLTEquiv ℤ_[p] (derivativeBudget d p))
    (x := (phi0 hp d).codRestrict _ (phi0_mem hp d hd) a)).mp h
  exact congrArg Subtype.val h'

/-! ### The reduced first-order map -/

def rdpoly {d : ℕ} (x : DIdx d → ZMod p) (k : Fin 3) : Polynomial (ZMod p) :=
  ∑ i : Fin d, Polynomial.C (x (k, i)) * Polynomial.X ^ (i : ℕ)

def rdpolyL (d : ℕ) (k : Fin 3) : (DIdx d → ZMod p) →ₗ[ZMod p] Polynomial (ZMod p) where
  toFun x := rdpoly x k
  map_add' a b := by simp [rdpoly, add_mul, Finset.sum_add_distrib]
  map_smul' c a := by
    simp [rdpoly, Finset.smul_sum, Polynomial.smul_eq_C_mul, mul_assoc]

theorem redZ_dpoly {d : ℕ} (a : DIdx d → ℤ_[p]) (k : Fin 3) :
    redZ p (dpoly a k) = rdpoly (redV (p := p) (DIdx d) a) k := by
  simp [dpoly, rdpoly, redV_apply]

def psiL (hp : 11 ≤ p) (d : ℕ) : (DIdx d → ZMod p) →ₗ[ZMod p] Polynomial (ZMod p) :=
  (LinearMap.mulLeft (ZMod p) (redZ p (intPolyP p * integralQuotientPolynomial p (hp5 hp)))).comp
      (rdpolyL d 1) +
    (LinearMap.mulLeft (ZMod p) (redZ p (rhoPoly p (hp5 hp)))).comp (rdpolyL d 2)

theorem psiL_red (hp : 11 ≤ p) (d : ℕ) (a : DIdx d → ℤ_[p]) :
    psiL hp d (redV (p := p) (DIdx d) a) = redZ p (clearedF1 p hp (dpoly a 1) (dpoly a 2)) := by
  simp only [psiL, clearedF1, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.mulLeft_apply, map_add, map_mul]
  rw [redZ_dpoly, redZ_dpoly]
  rfl

/-- The target of the reduced first-order map on the reduced exact kernel. -/
def psiTarget (hp : 11 ≤ p) (d : ℕ) : Submodule (ZMod p) (Polynomial (ZMod p)) :=
  (Polynomial.degreeLT (ZMod p) (d + 2)).map
    (LinearMap.mulLeft (ZMod p) (reducedQuotient p (hp5 hp)))

theorem psiTarget_finrank (hp : 11 ≤ p) (d : ℕ) :
    Module.finrank (ZMod p) (psiTarget hp d) ≤ d + 2 := by
  refine (Submodule.finrank_map_le _ _).trans ?_
  rw [(Polynomial.degreeLTEquiv (ZMod p) (d + 2)).finrank_eq, Module.finrank_fin_fun]

instance psiTarget_finite (hp : 11 ≤ p) (d : ℕ) :
    FiniteDimensional (ZMod p) (psiTarget hp d) := by
  unfold psiTarget
  infer_instance

theorem psiL_mem (hp : 11 ≤ p) (d : ℕ) (hd : 1 ≤ d) (x : DIdx d → ℤ_[p])
    (hx : phi0 hp d x = 0) : psiL hp d (redV (p := p) (DIdx d) x) ∈ psiTarget hp d := by
  rw [psiL_red]
  have h0 : redZ p (clearedF0 p hp (dpoly x 0) (dpoly x 1) (dpoly x 2)) = 0 := by
    rw [← phi0_apply, hx, map_zero]
  have hdiv := reducedQuotient_dvd_of_cleared hp _ _ _ h0
  obtain ⟨g, hg, hgd⟩ := reduced_clearedF1_factor hp (dpoly x 1) (dpoly x 2) (d-1)
    ((Polynomial.natDegree_map_le).trans (dpoly_natDegree x 1))
    ((Polynomial.natDegree_map_le).trans (dpoly_natDegree x 2)) hdiv
  rw [hg]
  refine ⟨g, ?_, rfl⟩
  show g ∈ Polynomial.degreeLT (ZMod p) (d + 2)
  rw [Polynomial.mem_degreeLT]
  refine Polynomial.degree_le_natDegree.trans_lt ?_
  exact_mod_cast (show g.natDegree < d + 2 by omega)

/-! ### Integral divisibility from a vanishing reduction -/

theorem polynomial_dvd_prime_of_redZ (f : Polynomial ℤ_[p]) (h : redZ p f = 0) :
    ∃ H : Polynomial ℤ_[p], f = Polynomial.C (p : ℤ_[p]) * H := by
  have hmem : f ∈ (Ideal.span {(p : ℤ_[p])}).map (Polynomial.C (R := ℤ_[p])) := by
    rw [Ideal.mem_map_C_iff]
    intro n
    rw [← PadicInt.maximalIdeal_eq_span_p, ← PadicInt.ker_toZMod, RingHom.mem_ker]
    have hc := congrArg (fun g => Polynomial.coeff g n) h
    simpa using hc
  rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton] at hmem
  obtain ⟨H, hH⟩ := hmem
  exact ⟨H, hH⟩

/-! ### Caps of actual derivative source vectors -/

attribute [local irreducible] hasseR hasseXi logDer Cap

/-- Extension of a derivative source vector by zero on the germs `K, J₁, J₂`. -/
def embedD {d : ℕ} (x : DIdx d → ℤ_[p]) : TailIndex d → ℤ_[p] :=
  fun j => if h : j.1.val < 3 then x (⟨j.1.val, h⟩, j.2) else 0

theorem embedD_supported {d : ℕ} (x : DIdx d → ℤ_[p]) : DerivativeSupported (embedD x) := by
  intro j hj
  simp only [embedD, dif_neg (not_lt.mpr hj)]

theorem sourcePoly_embedD {d : ℕ} (x : DIdx d → ℤ_[p]) (k : Fin 3) :
    sourcePoly (embedD x) ⟨k.val, by omega⟩ = ((dpoly x k : Polynomial ℤ_[p]) : PowerSeries ℤ_[p]) := by
  unfold sourcePoly dpoly
  rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [embedD, dif_pos k.isLt, map_mul, map_pow, Polynomial.coeToPowerSeries.ringHom_apply,
    Polynomial.coe_C, Polynomial.coe_X]

theorem actualSource_embedD (d : ℕ) (c : ℚ) (x : DIdx d → ℤ_[p]) :
    actualSourceSeries p d c (embedD x) =
      derivativeSource c (dpoly x 0 : PowerSeries ℤ_[p]) (dpoly x 1) (dpoly x 2) := by
  rw [actualSourceSeries_derivative d c _ (embedD_supported x)]
  rw [show (0 : Fin 6) = ⟨(0 : Fin 3).val, by omega⟩ from rfl,
    show (1 : Fin 6) = ⟨(1 : Fin 3).val, by omega⟩ from rfl,
    show (2 : Fin 6) = ⟨(2 : Fin 3).val, by omega⟩ from rfl,
    sourcePoly_embedD, sourcePoly_embedD, sourcePoly_embedD]

theorem embedD_cap_three (hp : 11 ≤ p) (c : ℚ) (hc : ¬p ∣ c.den) {d : ℕ}
    (x : DIdx d → ℤ_[p]) (N : ℕ) (hN : N ≤ p^2) :
    Cap N 3 (actualSourceSeries p d c (embedD x)) := by
  rw [actualSource_embedD]
  exact derivativeSource_cap_three hp c hc _ _ _ N hN

theorem embedD_cap_two (hp : 11 ≤ p) (c : ℚ) (hc : ¬p ∣ c.den) {d : ℕ}
    (x : DIdx d → ℤ_[p]) (hx : phi0 hp d x = 0) (N : ℕ) (hN : N ≤ p^2) :
    Cap N 2 (actualSourceSeries p d c (embedD x)) := by
  rw [actualSource_embedD]
  apply derivativeSource_cap_two hp c hc _ _ _ _ N hN
  exact (derivativeF0_eq_zero_iff hp _ _ _).mpr (by rw [← phi0_apply]; exact hx)

theorem cleared_factor_inv_cap (hp : 5 ≤ p) (N : ℕ) :
    Cap N 0 ((padicMap (p := p) shortP * hasseQp p hp)⁻¹) := by
  have h := inv_cap_zero (p := p) (integralP p * (integralQuotientPolynomial p hp : PowerSeries ℤ_[p]))
    1 (by rw [map_mul, integralP_constant, integralQuotient_series_constant, one_mul,
      Units.val_one]) N
  rwa [map_mul, zpMap_integralP] at h

theorem embedD_cap_one (hp : 11 ≤ p) (c : ℚ) (hc : ¬p ∣ c.den) {d : ℕ}
    (x : DIdx d → ℤ_[p]) (hx : phi0 hp d x = 0)
    (hψ : psiL hp d (redV (p := p) (DIdx d) x) = 0) (N : ℕ) (hN : N ≤ p^2) :
    Cap N 1 (actualSourceSeries p d c (embedD x)) := by
  rw [psiL_red] at hψ
  obtain ⟨H, hH⟩ := polynomial_dvd_prime_of_redZ _ hψ
  have hc1 := derivativeF1_cleared hp (dpoly x 1) (dpoly x 2)
  rw [hH, map_mul, zpPoly_C, PadicInt.coe_natCast, map_natCast] at hc1
  have hne : PowerSeries.constantCoeff (padicMap (p := p) shortP * hasseQp p (hp5 hp)) ≠ 0 := by
    rw [map_mul]; exact mul_ne_zero padicShortP_const (hasseQp_const _)
  have hinv := PowerSeries.inv_mul_cancel _ hne
  rw [actualSource_embedD]
  apply derivativeSource_cap_one hp c hc _ _ _ _
    ((padicMap (p := p) shortP * hasseQp p (hp5 hp))⁻¹ * zpPoly p H) _ N hN
  · have h1 := cleared_factor_inv_cap (p := p) (hp5 hp) N
    have h2 : Cap N 0 (zpPoly p H) := integral_series_cap (H : PowerSeries ℤ_[p]) N
    exact h1.mul h2
  · exact (derivativeF0_eq_zero_iff hp _ _ _).mpr (by rw [← phi0_apply]; exact hx)
  · calc derivativeF1 (hp5 hp) (dpoly x 1 : PowerSeries ℤ_[p]) (dpoly x 2)
        = ((padicMap (p := p) shortP * hasseQp p (hp5 hp))⁻¹ *
            (padicMap (p := p) shortP * hasseQp p (hp5 hp))) *
          derivativeF1 (hp5 hp) (dpoly x 1 : PowerSeries ℤ_[p]) (dpoly x 2) := by
            rw [hinv, one_mul]
      _ = _ := by
            rw [mul_assoc, hc1]
            ring

/-! ### The derivative block -/

theorem derivative_block (hp : 11 ≤ p) (d : ℕ) (hd : 1 ≤ d) :
    ∃ (k c₁ m : ℕ) (Y : Fin k ⊕ Fin c₁ → (DIdx d → ℤ_[p])) (Z : Fin m → (DIdx d → ℤ_[p])),
      k + c₁ + m = 3 * d ∧ 3 * d ≤ derivativeBudget d p + (k + c₁) ∧ k + c₁ ≤ d + 2 + k ∧
      (∀ j, phi0 hp d (Y j) = 0) ∧
      (∀ j, psiL hp d (redV (p := p) (DIdx d) (Y (Sum.inl j))) = 0) ∧
      LinearIndependent (ZMod p) (Sum.elim (fun j => redV (p := p) (DIdx d) (Y j))
        (fun j => redV (p := p) (DIdx d) (Z j))) := by
  classical
  obtain ⟨n, bM, f, hker, hcard⟩ := snf_kernel (p := p) (phi0F hp d hd)
  have hker' : ∀ i, phi0 hp d (bM (f i)) = 0 := fun i => phi0F_eq_zero hp d hd _ (hker i)
  have hcomb : ∀ a : Fin n → ℤ_[p], phi0 hp d (∑ i, a i • bM (f i)) = 0 := by
    intro a
    rw [map_sum]
    exact Finset.sum_eq_zero fun i _ => by rw [map_smul, hker' i, smul_zero]
  obtain ⟨k, c₁, Y, hkc, hnk, hY, hψ, hind⟩ := adapted_lift bM f (psiL hp d) (psiTarget hp d)
    (d + 2) (psiTarget_finrank hp d) (fun a => psiL_mem hp d hd _ (hcomb a))
  let e := Fintype.equivFin {j : DIdx d // j ∉ Set.range f}
  have hrange : Fintype.card (Set.range f) = n := by
    rw [Set.card_range_of_injective f.injective, Fintype.card_fin]
  have hm : Fintype.card {j : DIdx d // j ∉ Set.range f} = 3 * d - n := by
    rw [Fintype.card_subtype_compl, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
    rw [show Fintype.card {x : DIdx d // x ∈ Set.range f} = n from hrange]
  have hn3 : n ≤ 3 * d := by
    have := Fintype.card_subtype_le (fun x : DIdx d => x ∈ Set.range f)
    rw [show Fintype.card {x : DIdx d // x ∈ Set.range f} = n from hrange, Fintype.card_prod,
      Fintype.card_fin, Fintype.card_fin] at this
    omega
  have hc3 : Fintype.card (DIdx d) = 3 * d := by simp
  refine ⟨k, c₁, Fintype.card {j : DIdx d // j ∉ Set.range f}, Y, fun i => bM (e.symm i),
    by omega, by omega, by omega, fun j => ?_, hψ, ?_⟩
  · obtain ⟨a, ha⟩ := hY j
    rw [ha]
    exact hcomb a
  · have h := hind.comp (Sum.map id e.symm) (Sum.map_injective.mpr ⟨Function.injective_id, e.symm.injective⟩)
    convert h using 1
    ext t : 1
    rcases t with t | t <;> rfl

/-! ### Assembly of the full source basis -/

def embedR (d : ℕ) : (DIdx d → ZMod p) →ₗ[ZMod p] (TailIndex d → ZMod p) where
  toFun x j := if h : j.1.val < 3 then x (⟨j.1.val, h⟩, j.2) else 0
  map_add' x y := by ext j; simp only [Pi.add_apply]; split_ifs <;> simp
  map_smul' a x := by ext j; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> simp

theorem redV_embedD {d : ℕ} (x : DIdx d → ℤ_[p]) :
    redV (p := p) (TailIndex d) (embedD x) = embedR d (redV (p := p) (DIdx d) x) := by
  ext j
  simp only [redV_apply, embedD, embedR, LinearMap.coe_mk, AddHom.coe_mk]
  split_ifs <;> simp [redV_apply]

theorem embedR_ker (d : ℕ) : LinearMap.ker (embedR (p := p) d) = ⊥ := by
  apply LinearMap.ker_eq_bot.mpr
  intro x y h
  ext ⟨k, i⟩
  have := congrFun h (⟨k.val, by omega⟩, i)
  simpa [embedR] using this

def kIndex (d : ℕ) (t : Fin 3 × Fin d) : TailIndex d := (⟨t.1.val + 3, by omega⟩, t.2)

def kSingle (d : ℕ) (t : Fin 3 × Fin d) : TailIndex d → ℤ_[p] := Pi.single (kIndex d t) 1

theorem kIndex_injective (d : ℕ) : Function.Injective (kIndex d) := by
  rintro ⟨a, i⟩ ⟨b, j⟩ h
  simp only [kIndex, Prod.mk.injEq, Fin.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  subst h2
  congr 1
  ext
  omega

theorem redV_kSingle {d : ℕ} (t : Fin 3 × Fin d) :
    redV (p := p) (TailIndex d) (kSingle d t) = Pi.single (kIndex d t) 1 := by
  ext j
  simp only [redV_apply, kSingle, Pi.single_apply]
  split_ifs <;> simp

def projR (d : ℕ) : (TailIndex d → ZMod p) →ₗ[ZMod p] (DIdx d → ZMod p) where
  toFun v x := v (⟨x.1.val, by omega⟩, x.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem projR_embedR {d : ℕ} (y : DIdx d → ZMod p) : projR d (embedR d y) = y := by
  ext x
  simp [projR, embedR]

theorem projR_kSingle {d : ℕ} (t : Fin 3 × Fin d) :
    projR (p := p) d (Pi.single (kIndex d t) 1) = 0 := by
  ext x
  simp only [projR, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply, Pi.single_apply]
  rw [if_neg]
  intro h
  have := congrArg (fun j : TailIndex d => j.1.val) h
  simp [kIndex] at this
  omega

theorem actualPrimeMatrix_mul_col (d : ℕ) (c : ℚ) (U : Matrix (TailIndex d) (TailIndex d) ℤ_[p])
    (i j : TailIndex d) :
    (actualPrimeMatrix p d c * U.map (algebraMap ℤ_[p] ℚ_[p])) i j =
      PowerSeries.coeff (actualTailRow d c i) (actualSourceSeries p d c (fun t => U t j)) := by
  simp only [Matrix.mul_apply, actualSourceSeries, map_sum, PowerSeries.coeff_C_mul,
    actualPrimeMatrix, tailMatrix, Matrix.map_apply, PadicInt.algebraMap_apply]
  exact Finset.sum_congr rfl fun t _ => mul_comm _ _

theorem thresholdMass_equiv {κ τ : Type*} [Fintype κ] [Fintype τ] (e : κ ≃ τ) (h : ℕ)
    (w : κ → ℕ) : thresholdMass h (w ∘ e.symm) = thresholdMass h w := by
  classical
  unfold thresholdMass
  refine Finset.sum_congr rfl fun t _ => ?_
  congr 1
  rw [← Fintype.card_subtype, ← Fintype.card_subtype]
  exact Fintype.card_congr (e.symm.subtypeEquiv (fun _ => Iff.rfl))

/-- **P4 local estimate.** For the unchanged determinant, the actual derivative basis gives
`-v_p ≤ min r (6d) + min r (6d - c₂) + min r (3d + c₀) + min r (3d)`,
where `c₀ = derivativeThree`, `c₂ = derivativeOne`, and `r = min (6d) (7d + 176 - p)`. -/
theorem actualCommonDeterminant_derivative_bound (hp : 11 ≤ p) (c : ℚ) (hc : ¬p ∣ c.den)
    (d : ℕ) (hd : 1 ≤ d) (hN : 7 * d + 176 ≤ p^2) :
    -padicValRat p (actualCommonDeterminant d c) ≤
      ((min (min (6*d) (7*d+176-p)) (6*d) +
        min (min (6*d) (7*d+176-p)) (6*d - derivativeOne d p) +
        min (min (6*d) (7*d+176-p)) (3*d + derivativeThree d p) +
        min (min (6*d) (7*d+176-p)) (3*d) : ℕ) : ℤ) := by
  classical
  obtain ⟨k, c₁, m, Y, Z, hsum, hb, hnk, hY0, hY1, hind⟩ := derivative_block hp d hd
  let κ := ((Fin k ⊕ Fin c₁) ⊕ Fin m) ⊕ (Fin 3 × Fin d)
  let V : κ → TailIndex d → ℤ_[p] :=
    Sum.elim (Sum.elim (fun j => embedD (Y j)) (fun j => embedD (Z j))) (kSingle d)
  let w : κ → ℕ :=
    Sum.elim (Sum.elim (Sum.elim (fun _ => 1) (fun _ => 2)) (fun _ => 3)) (fun _ => 4)
  have hcapκ : ∀ t, Cap (7*d+176) (w t) (actualSourceSeries p d c (V t)) := by
    rintro (((j | j) | j) | j)
    · exact embedD_cap_one hp c hc _ (hY0 _) (hY1 j) _ hN
    · exact embedD_cap_two hp c hc _ (hY0 _) _ hN
    · exact embedD_cap_three hp c hc _ _ hN
    · exact actualSourceSeries_cap p c (fun g => actual_germs_cap_four (by omega) c hc _ hN g) _
  have hindκ : LinearIndependent (ZMod p) (fun t => redV (p := p) (TailIndex d) (V t)) := by
    have hv : LinearIndependent (ZMod p)
        (fun t => embedR d (Sum.elim (fun j => redV (p := p) (DIdx d) (Y j))
          (fun j => redV (p := p) (DIdx d) (Z j)) t)) :=
      hind.map' (embedR d) (embedR_ker d)
    have hw : LinearIndependent (ZMod p) (fun t : Fin 3 × Fin d =>
        (Pi.single (kIndex d t) 1 : TailIndex d → ZMod p)) :=
      (Pi.linearIndependent_single_one (TailIndex d) (ZMod p)).comp (kIndex d)
        (kIndex_injective d)
    have hS2 : Submodule.span (ZMod p) (Set.range fun t : Fin 3 × Fin d =>
        (Pi.single (kIndex d t) 1 : TailIndex d → ZMod p)) ≤
        LinearMap.ker (projR (p := p) d) := by
      rw [Submodule.span_le]
      rintro _ ⟨t, rfl⟩
      exact projR_kSingle t
    have hS1 : Submodule.span (ZMod p) (Set.range fun t => embedR d
        (Sum.elim (fun j => redV (p := p) (DIdx d) (Y j))
          (fun j => redV (p := p) (DIdx d) (Z j)) t)) ≤ LinearMap.range (embedR (p := p) d) := by
      rw [Submodule.span_le]
      rintro _ ⟨t, rfl⟩
      exact ⟨_, rfl⟩
    have hdisj : Disjoint (LinearMap.range (embedR (p := p) d))
        (LinearMap.ker (projR (p := p) d)) := by
      rw [Submodule.disjoint_def]
      rintro _ ⟨y, rfl⟩ hy
      rw [LinearMap.mem_ker, projR_embedR] at hy
      rw [hy, map_zero]
    have hsum' := hv.sum_type hw (hdisj.mono hS1 hS2)
    convert hsum' using 1 <;> first
      | rfl
      | (ext t : 1
         rcases t with ((j | j) | j) | j
         · exact redV_embedD _
         · exact redV_embedD _
         · exact redV_embedD _
         · exact redV_kSingle j)
  have hcardκ : Fintype.card κ = Fintype.card (TailIndex d) := by
    simp only [κ, Fintype.card_sum, Fintype.card_fin, Fintype.card_prod]
    omega
  let e : κ ≃ TailIndex d := Fintype.equivOfCardEq hcardκ
  let U : Matrix (TailIndex d) (TailIndex d) ℤ_[p] := fun i j => V (e.symm j) i
  have hU : IsUnit U.det := isUnit_det_of_reduced_cols U (hindκ.comp e.symm e.symm.injective)
  have hmain := actualCommonDeterminant_bound_of_compatible_caps d c hc U hU (w ∘ e.symm)
    (by
      intro j
      simp only [Function.comp]
      generalize e.symm j = t
      rcases t with ((t | t) | t) | t <;> simp [w])
    (by
      intro i j
      rw [actualPrimeMatrix_mul_col]
      have h := hcapκ (e.symm j)
      unfold Cap at h
      exact h _ (actualTailRow_lt d c i))
  rw [thresholdMass_equiv] at hmain
  have hcnt : ∀ t : Fin 4, (Finset.univ.filter (fun x : κ => t.val < w x)).card =
      (if t.val < 1 then k else 0) + (if t.val < 2 then c₁ else 0) +
        (if t.val < 3 then m else 0) + (if t.val < 4 then 3 * d else 0) := by
    intro t
    rw [Finset.card_filter]
    simp only [κ, Fintype.sum_sum_type, w, Sum.elim_inl, Sum.elim_inr, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, Fintype.card_prod, smul_eq_mul]
    fin_cases t <;> simp
  have hmass : thresholdMass (min (6 * d) (7 * d + 176 - p)) w =
      min (min (6*d) (7*d+176-p)) (k + c₁ + m + 3*d) +
      min (min (6*d) (7*d+176-p)) (c₁ + m + 3*d) +
      min (min (6*d) (7*d+176-p)) (m + 3*d) +
      min (min (6*d) (7*d+176-p)) (3*d) := by
    unfold thresholdMass
    rw [Fin.sum_univ_four]
    rw [hcnt 0, hcnt 1, hcnt 2, hcnt 3]
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two]
    norm_num
  rw [hmass] at hmain
  refine hmain.trans ?_
  have h1 : c₁ + m + 3*d ≤ 6*d - derivativeOne d p := by
    unfold derivativeOne derivativeTwo derivativeThree derivativeBudget at *
    omega
  have h2 : m + 3*d ≤ 3*d + derivativeThree d p := by
    unfold derivativeThree derivativeBudget at *
    omega
  have h0 : k + c₁ + m + 3*d = 6*d := by omega
  rw [h0]
  exact_mod_cast Nat.add_le_add (Nat.add_le_add (Nat.add_le_add le_rfl
    (min_le_min_left _ h1)) (min_le_min_left _ h2)) le_rfl

end Zeta7Auxiliary

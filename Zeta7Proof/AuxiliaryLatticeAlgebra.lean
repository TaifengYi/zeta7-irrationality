import Mathlib

/-! Finite lattice algebra over `ℤ_[p]` used to build compatible integral source bases:
Smith normal form for a kernel with an exact rank count, reduction of bases modulo `p`,
unit determinants from independent reductions, and lifting of residue-field bases
adapted to a subspace. No actual series occur here. -/
noncomputable section
set_option autoImplicit false
namespace Zeta7Auxiliary

variable {p : ℕ} [Fact p.Prime]

/-- Coordinatewise reduction modulo `p`, as a semilinear map. -/
def redV (ι : Type*) : (ι → ℤ_[p]) →ₛₗ[PadicInt.toZMod (p := p)] (ι → ZMod p) where
  toFun v i := PadicInt.toZMod (v i)
  map_add' v w := by ext i; simp
  map_smul' c v := by ext i; simp

theorem redV_apply {ι : Type*} (v : ι → ℤ_[p]) (i : ι) :
    redV (p := p) ι v i = PadicInt.toZMod (v i) := rfl

/-- The canonical lift `ZMod p → ℤ_[p]`. -/
def liftZ (x : ZMod p) : ℤ_[p] := (x.val : ℤ_[p])

theorem toZMod_liftZ (x : ZMod p) : PadicInt.toZMod (liftZ x) = x := by
  rw [liftZ, map_natCast, ZMod.natCast_zmod_val]

/-- A square integral matrix whose reduced columns are independent is unimodular. -/
theorem isUnit_det_of_reduced_cols {κ : Type*} [Fintype κ] [DecidableEq κ]
    (U : Matrix κ κ ℤ_[p])
    (h : LinearIndependent (ZMod p) (fun j => redV (p := p) κ (fun i => U i j))) :
    IsUnit U.det := by
  have hU : IsUnit (U.map PadicInt.toZMod) := by
    apply Matrix.linearIndependent_cols_iff_isUnit.mp
    convert h using 1
    ext j i
    rfl
  have hd : PadicInt.toZMod U.det ≠ 0 := by
    rw [RingHom.map_det]
    exact (Matrix.isUnit_iff_isUnit_det _).mp hU |>.ne_zero
  by_contra hnu
  apply hd
  have hm : U.det ∈ IsLocalRing.maximalIdeal ℤ_[p] := hnu
  rw [← PadicInt.ker_toZMod] at hm
  exact hm

/-- The reductions of an integral basis of `ι → ℤ_[p]` are independent. -/
theorem basis_reduced_independent {ι : Type*} [Fintype ι] [DecidableEq ι]
    (bM : Module.Basis ι ℤ_[p] (ι → ℤ_[p])) :
    LinearIndependent (ZMod p) (fun j => redV (p := p) ι (bM j)) := by
  let A : Matrix ι ι ℤ_[p] := (Pi.basisFun ℤ_[p] ι).toMatrix bM
  have hA : IsUnit A.det := by
    have := (Pi.basisFun ℤ_[p] ι).invertibleToMatrix bM
    exact Matrix.isUnit_det_of_invertible A
  have hA' : IsUnit (A.map PadicInt.toZMod) := by
    rw [Matrix.isUnit_iff_isUnit_det]
    have e := RingHom.map_det (PadicInt.toZMod (p := p)) A
    rw [RingHom.mapMatrix_apply] at e
    rw [← e]
    exact hA.map _
  have h := Matrix.linearIndependent_cols_iff_isUnit.mpr hA'
  convert h using 1
  ext j i
  simp [A, redV_apply, Module.Basis.toMatrix_apply, Matrix.col]

/-- Smith normal form of the kernel of a map into a free module of rank `b`:
an integral basis contains `n` kernel vectors, with `card ι ≤ b + n`. -/
theorem snf_kernel {ι : Type} [Fintype ι] {b : ℕ}
    (Φ : (ι → ℤ_[p]) →ₗ[ℤ_[p]] (Fin b → ℤ_[p])) :
    ∃ (n : ℕ) (bM : Module.Basis ι ℤ_[p] (ι → ℤ_[p])) (f : Fin n ↪ ι),
      (∀ i, Φ (bM (f i)) = 0) ∧ Fintype.card ι ≤ b + n := by
  obtain ⟨n, snf⟩ := (LinearMap.ker Φ).smithNormalForm (Pi.basisFun ℤ_[p] ι)
  refine ⟨n, snf.bM, snf.f, fun i => ?_, ?_⟩
  · have hmem : snf.a i • snf.bM (snf.f i) ∈ LinearMap.ker Φ := by
      rw [← snf.snf i]; exact (snf.bN i).2
    have ha : snf.a i ≠ 0 := by
      intro h0
      have h1 := snf.snf i
      rw [h0, zero_smul] at h1
      exact snf.bN.ne_zero i (Subtype.ext h1)
    rw [LinearMap.mem_ker, map_smul] at hmem
    exact (smul_eq_zero.mp hmem).resolve_left ha
  · have h := LinearMap.rank_range_add_rank_ker Φ
    rw [rank_eq_card_basis snf.bN, rank_fun', Fintype.card_fin] at h
    have hr : Module.rank ℤ_[p] (LinearMap.range Φ) ≤ b :=
      (Submodule.rank_le _).trans (by rw [rank_fin_fun])
    have hc : ((Fintype.card ι : ℕ) : Cardinal) ≤ ((b + n : ℕ) : Cardinal) := by
      rw [← h, Nat.cast_add]
      exact add_le_add_left hr _
    exact_mod_cast hc

theorem redV_sum_smul {ι κ : Type*} [Fintype κ] (a : κ → ℤ_[p]) (v : κ → ι → ℤ_[p]) :
    redV (p := p) ι (∑ i, a i • v i) = ∑ i, PadicInt.toZMod (a i) • redV (p := p) ι (v i) := by
  rw [map_sum]
  simp only [map_smulₛₗ]

/-- **Adapted lifting.** Let `bM` be an integral basis with `n` distinguished vectors, and let a
residue-field linear map `ψ` send every reduction of an integral combination of the distinguished
vectors into a subspace of dimension at most `D`. Then the distinguished span has an integral
family `Y` of `k + c = n` vectors, with `n ≤ D + k`, whose first `k` reductions are killed by `ψ`,
and whose reductions together with those of the remaining basis vectors are independent. -/
theorem adapted_lift {ι : Type} [Fintype ι] [DecidableEq ι]
    {W' : Type*} [AddCommGroup W'] [Module (ZMod p) W']
    (bM : Module.Basis ι ℤ_[p] (ι → ℤ_[p])) {n : ℕ} (f : Fin n ↪ ι)
    (ψ : (ι → ZMod p) →ₗ[ZMod p] W') (W : Submodule (ZMod p) W') (D : ℕ)
    [FiniteDimensional (ZMod p) W] (hD : Module.finrank (ZMod p) W ≤ D)
    (hψ : ∀ a : Fin n → ℤ_[p], ψ (redV (p := p) ι (∑ i, a i • bM (f i))) ∈ W) :
    ∃ (k c : ℕ) (Y : Fin k ⊕ Fin c → (ι → ℤ_[p])),
      k + c = n ∧ n ≤ D + k ∧
      (∀ j, ∃ a : Fin n → ℤ_[p], Y j = ∑ i, a i • bM (f i)) ∧
      (∀ j, ψ (redV (p := p) ι (Y (Sum.inl j))) = 0) ∧
      LinearIndependent (ZMod p) (Sum.elim (fun j => redV (p := p) ι (Y j))
        (fun j : {j // j ∉ Set.range f} => redV (p := p) ι (bM j))) := by
  classical
  let G : ι → ι → ZMod p := fun j => redV (p := p) ι (bM j)
  have hG : LinearIndependent (ZMod p) G := basis_reduced_independent bM
  let g : Fin n → ι → ZMod p := G ∘ f
  have hg : LinearIndependent (ZMod p) g := hG.comp f f.injective
  let S : Submodule (ZMod p) (ι → ZMod p) := Submodule.span (ZMod p) (Set.range g)
  let bS : Module.Basis (Fin n) (ZMod p) S := Module.Basis.span hg
  let a : S → Fin n → ℤ_[p] := fun y i => liftZ (bS.repr y i)
  let L : S → ι → ℤ_[p] := fun y => ∑ i, a y i • bM (f i)
  have hL : ∀ y : S, redV (p := p) ι (L y) = (y : ι → ZMod p) := by
    intro y
    rw [redV_sum_smul]
    simp only [a, toZMod_liftZ]
    have hy := congrArg Subtype.val (bS.sum_repr y)
    rw [Submodule.coe_sum] at hy
    rw [← hy]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Submodule.coe_smul, Module.Basis.span_apply]
    rfl
  let ψS : S →ₗ[ZMod p] W' := ψ.comp S.subtype
  have hrange : LinearMap.range ψS ≤ W := by
    rintro _ ⟨y, rfl⟩
    change ψ (y : ι → ZMod p) ∈ W
    rw [← hL y]
    exact hψ (a y)
  have hrk : Module.finrank (ZMod p) (LinearMap.range ψS) ≤ D :=
    (Submodule.finrank_mono hrange).trans hD
  have hS : Module.finrank (ZMod p) S = n := by
    rw [finrank_span_eq_card hg, Fintype.card_fin]
  have hrn := LinearMap.finrank_range_add_finrank_ker ψS
  rw [hS] at hrn
  let K := LinearMap.ker ψS
  obtain ⟨C, hKC⟩ := Submodule.exists_isCompl K
  have hkc := Submodule.finrank_add_eq_of_isCompl hKC
  rw [hS] at hkc
  let bK := Module.finBasis (ZMod p) K
  let bC := Module.finBasis (ZMod p) C
  let bKC : Module.Basis (Fin (Module.finrank (ZMod p) K) ⊕ Fin (Module.finrank (ZMod p) C))
      (ZMod p) S := (bK.prod bC).map (Submodule.prodEquivOfIsCompl K C hKC)
  have hKe : Module.finrank (ZMod p) K = Module.finrank (ZMod p) (LinearMap.ker ψS) := rfl
  refine ⟨Module.finrank (ZMod p) K, Module.finrank (ZMod p) C, fun j => L (bKC j),
    hkc, by omega, fun j => ⟨a (bKC j), rfl⟩, fun j => ?_, ?_⟩
  · rw [hL]
    have hK : bKC (Sum.inl j) ∈ K := by
      simp only [bKC, Module.Basis.map_apply, Module.Basis.prod_apply_inl_fst,
        Module.Basis.prod_apply, Submodule.coe_prodEquivOfIsCompl']
      simp
    exact hK
  · have hv : LinearIndependent (ZMod p) (fun j => redV (p := p) ι (L (bKC j))) := by
      simp only [hL]
      exact bKC.linearIndependent.map' S.subtype (Submodule.ker_subtype S)
    have hw : LinearIndependent (ZMod p)
        (fun j : {j // j ∉ Set.range f} => redV (p := p) ι (bM j)) :=
      hG.comp Subtype.val Subtype.val_injective
    apply hv.sum_type hw
    have hsub : Submodule.span (ZMod p) (Set.range fun j => redV (p := p) ι (L (bKC j))) ≤ S := by
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      show redV (p := p) ι (L (bKC j)) ∈ S
      rw [hL]
      exact (bKC j).2
    have hdisj := hG.disjoint_span_image (s := Set.range f) (t := (Set.range f)ᶜ)
      disjoint_compl_right
    have h1 : S ≤ Submodule.span (ZMod p) (G '' Set.range f) := by
      change Submodule.span (ZMod p) (Set.range (G ∘ f)) ≤ _
      rw [Set.range_comp]
    have h2 : Submodule.span (ZMod p) (Set.range (fun j : {j // j ∉ Set.range f} =>
        redV (p := p) ι (bM j))) ≤ Submodule.span (ZMod p) (G '' (Set.range f)ᶜ) := by
      apply le_of_eq
      congr 1
      ext x
      simp only [Set.mem_range, Set.mem_image, Set.mem_compl_iff, Subtype.exists]
      constructor
      · rintro ⟨j, hj, rfl⟩; exact ⟨j, hj, rfl⟩
      · rintro ⟨j, hj, rfl⟩; exact ⟨j, hj, rfl⟩
    exact Disjoint.mono (hsub.trans h1) h2 hdisj

end Zeta7Auxiliary

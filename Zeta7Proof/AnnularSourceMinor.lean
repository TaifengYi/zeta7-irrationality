import Mathlib

/-! The source minor in A5 / Appendix A4 of the 15 September manuscript.
This is the minor of shifts of the K-block polynomial, not the seven-germ
coefficient determinant. No analytic existence assertion is made here.
-/

set_option autoImplicit false
noncomputable section
namespace Zeta7AnnularSource
open Polynomial Matrix

/-- Polynomial coefficients extended by zero to negative indices. -/
def coeffInt {R : Type*} [Semiring R] (p : R[X]) (n : ℤ) : R :=
  if 0 ≤ n then p.coeff n.toNat else 0

/-- Rows ell,...,ell+k-1 of the k columns p, Xp,...,X^(k-1)p. -/
def shiftMinor {R : Type*} [CommRing R] (p : R[X]) (ell k : ℕ) :
    Matrix (Fin k) (Fin k) R :=
  fun i m => coeffInt p ((ell : ℤ) + i.val - m.val)

theorem shiftMinor_eq_coeff {R : Type*} [CommRing R]
    (p : R[X]) (ell k : ℕ) (i m : Fin k) :
    shiftMinor p ell k i m = (X ^ m.val * p).coeff (ell + i.val) := by
  simp only [shiftMinor, coeffInt, coeff_X_pow_mul']
  split_ifs <;> congr 1 <;> omega

theorem shiftMinor_diag {R : Type*} [CommRing R]
    (p : R[X]) (ell k : ℕ) (i : Fin k) :
    shiftMinor p ell k i i = p.coeff ell := by
  simp [shiftMinor, coeffInt]

theorem map_shiftMinor {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (p : R[X]) (ell k : ℕ) :
    (shiftMinor p ell k).map f = shiftMinor (p.map f) ell k := by
  ext i m
  simp only [shiftMinor, coeffInt, Matrix.map_apply, coeff_map]
  split_ifs <;> simp

theorem shiftMinor_lowerTriangular {R : Type*} [CommRing R]
    (p : R[X]) (ell k : ℕ) (h : ∀ n < ell, p.coeff n = 0) :
    (shiftMinor p ell k).IsLowerTriangular := by
  intro i m him
  change coeffInt p ((ell : ℤ) + i.val - m.val) = 0
  unfold coeffInt
  split_ifs with hn
  · apply h
    have : i.val < m.val := him
    omega
  · rfl

theorem det_shiftMinor {R : Type*} [CommRing R]
    (p : R[X]) (ell k : ℕ) (h : ∀ n < ell, p.coeff n = 0) :
    (shiftMinor p ell k).det = p.coeff ell ^ k := by
  rw [Matrix.det_of_isLowerTriangular _ (shiftMinor_lowerTriangular p ell k h)]
  simp [shiftMinor_diag]

theorem shiftMinor_C_mul {R : Type*} [CommRing R]
    (c : R) (f : R[X]) (ell k : ℕ) :
    shiftMinor (C c * f) ell k = c • shiftMinor f ell k := by
  ext i m
  simp only [shiftMinor, coeffInt, Matrix.smul_apply, smul_eq_mul]
  split_ifs <;> simp [coeff_C_mul]

section Padic
variable {p : ℕ} [Fact p.Prime]

theorem residue_ne_zero_iff (x : ℤ_[p]) :
    PadicInt.toZMod x ≠ 0 ↔ IsUnit x := by
  simp only [ne_eq, ← RingHom.mem_ker, PadicInt.ker_toZMod,
    IsLocalRing.mem_maximalIdeal]
  change (¬ ¬ IsUnit x) ↔ IsUnit x
  exact not_not

/-- A first unit coefficient gives a unit minor in every size, including zero. -/
theorem isUnit_det_shiftMinor (f : ℤ_[p][X]) (ell k : ℕ)
    (hu : IsUnit (f.coeff ell)) (hfirst : ∀ n < ell, ¬ IsUnit (f.coeff n)) :
    IsUnit (shiftMinor f ell k).det := by
  apply (residue_ne_zero_iff _).mp
  rw [RingHom.map_det]
  change ((shiftMinor f ell k).map PadicInt.toZMod).det ≠ 0
  rw [map_shiftMinor]
  rw [det_shiftMinor (f.map PadicInt.toZMod) ell k]
  · simpa only [coeff_map] using pow_ne_zero k ((residue_ne_zero_iff _).mpr hu)
  · intro n hn
    simp only [coeff_map]
    by_contra hne
    exact hfirst n hn ((residue_ne_zero_iff _).mp hne)

theorem valuation_eq_zero_of_isUnit (x : ℤ_[p]) (hx : IsUnit x) :
    x.valuation = 0 := by
  obtain ⟨u, rfl⟩ := hx
  have h := PadicInt.valuation_mul (Units.ne_zero u) (Units.ne_zero u⁻¹)
  simp only [Units.mul_inv, PadicInt.valuation_one] at h
  omega

theorem isUnit_of_valuation_eq_zero (x : ℤ_[p]) (hx : x ≠ 0)
    (hv : x.valuation = 0) : IsUnit x := by
  have h := PadicInt.unitCoeff_spec hx
  rw [hv, pow_zero, mul_one] at h
  rw [h]
  exact Units.isUnit _

/-- Extract the minimum coefficient valuation and choose the first unit index.
All choices concern a finite polynomial; a and ell are independent of k. -/
theorem exists_normalized_first (f : ℤ_[p][X]) (hf : f ≠ 0) :
    ∃ (a : ℕ) (g : ℤ_[p][X]) (ell : ℕ),
      f = C ((p : ℤ_[p]) ^ a) * g ∧ IsUnit (g.coeff ell) ∧
      (∀ n < ell, ¬ IsUnit (g.coeff n)) ∧ ell ≤ f.natDegree := by
  classical
  obtain ⟨j, hj, hmin⟩ := f.support.exists_min_image
    (fun n => (f.coeff n).valuation) (Polynomial.support_nonempty.mpr hf)
  let a := (f.coeff j).valuation
  have hj0 : f.coeff j ≠ 0 := Polynomial.mem_support_iff.mp hj
  have hdiv : C ((p : ℤ_[p]) ^ a) ∣ f := by
    apply (Polynomial.C_dvd_iff_dvd_coeff _ _).mpr
    intro n
    by_cases hn : f.coeff n = 0
    · rw [hn]; exact dvd_zero _
    · rw [← Ideal.mem_span_singleton]
      exact (PadicInt.mem_span_pow_iff_le_valuation _ hn a).mpr
        (hmin n (Polynomial.mem_support_iff.mpr hn))
  obtain ⟨g, hg⟩ := hdiv
  have hcoeff : f.coeff j = (p : ℤ_[p]) ^ a * g.coeff j := by
    rw [hg, coeff_C_mul]
  have hgj : g.coeff j ≠ 0 := by intro h; simp [h] at hcoeff; exact hj0 hcoeff
  have hval : (g.coeff j).valuation = 0 := by
    have hh := congrArg PadicInt.valuation hcoeff
    rw [PadicInt.valuation_p_pow_mul _ _ hgj] at hh
    change a = a + (g.coeff j).valuation at hh
    omega
  have hex : ∃ n, IsUnit (g.coeff n) := ⟨j, isUnit_of_valuation_eq_zero _ hgj hval⟩
  refine ⟨a, g, Nat.find hex, hg, Nat.find_spec hex, ?_, ?_⟩
  · intro n hn; exact Nat.find_min hex hn
  · exact (Nat.find_min' hex (isUnit_of_valuation_eq_zero _ hgj hval)).trans
      (Polynomial.le_natDegree_of_ne_zero hj0)

/-- Exact cost of the original, scaled columns; it is not silently discarded. -/
theorem scaled_minor_valuation (f : ℤ_[p][X]) (ell k a : ℕ)
    (hu : IsUnit (f.coeff ell)) (hfirst : ∀ n < ell, ¬ IsUnit (f.coeff n)) :
    (((p : ℤ_[p]) ^ a • shiftMinor f ell k).det).valuation = a * k := by
  have hunit := isUnit_det_shiftMinor f ell k hu hfirst
  rw [Matrix.det_smul, Fintype.card_fin, ← pow_mul,
    PadicInt.valuation_p_pow_mul _ _ hunit.ne_zero,
    valuation_eq_zero_of_isUnit _ hunit, add_zero]

/-- The all-size minor statement for an arbitrary nonzero integral K-block.
This constructs its source index without assuming a primitive normalization. -/
theorem exists_minor_cost (f : ℤ_[p][X]) (hf : f ≠ 0) :
    ∃ a ell : ℕ, ell ≤ f.natDegree ∧ ∀ k : ℕ,
      (shiftMinor f ell k).det ≠ 0 ∧
      (shiftMinor f ell k).det.valuation = a * k := by
  obtain ⟨a, g, ell, hg, hu, hfirst, hell⟩ := exists_normalized_first f hf
  refine ⟨a, ell, hell, fun k => ?_⟩
  rw [hg, shiftMinor_C_mul]
  refine ⟨?_, scaled_minor_valuation g ell k a hu hfirst⟩
  rw [Matrix.det_smul]
  exact mul_ne_zero (pow_ne_zero _ (pow_ne_zero _ (NeZero.ne _)))
    (isUnit_det_shiftMinor g ell k hu hfirst).ne_zero

end Padic

section Completion
variable {R ι κ ν : Type*} [CommRing R]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype ν] [DecidableEq ν]

/-- Retain all original columns, then append the unselected coordinate vectors.
The equivalence orders the selected coordinate rows first. -/
def completion (e : κ ⊕ ν ≃ ι) (u : Matrix ι κ R) :
    Matrix (κ ⊕ ν) (κ ⊕ ν) R :=
  Matrix.fromBlocks (u.submatrix (fun i => e (.inl i)) id)
    (0 : Matrix κ ν R) (u.submatrix (fun i => e (.inr i)) id) 1

theorem completion_original (e : κ ⊕ ν ≃ ι) (u : Matrix ι κ R)
    (i : κ ⊕ ν) (m : κ) : completion e u i (.inl m) = u (e i) m := by
  cases i <;> rfl

theorem completion_coordinate (e : κ ⊕ ν ≃ ι) (u : Matrix ι κ R)
    (i : κ ⊕ ν) (j : ν) :
    completion e u i (.inr j) = if i = .inr j then 1 else 0 := by
  cases i <;> simp [completion, Matrix.one_apply]

theorem det_completion (e : κ ⊕ ν ≃ ι) (u : Matrix ι κ R) :
    (completion e u).det = (u.submatrix (fun i => e (.inl i)) id).det := by
  rw [completion, Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, mul_one]

/-- Exact source-change identity for the very same target matrix. -/
theorem det_completedImage (e : κ ⊕ ν ≃ ι) (u : Matrix ι κ R)
    (M : Matrix ι ι R) :
    (M.submatrix e e * completion e u).det =
      M.det * (u.submatrix (fun i => e (.inl i)) id).det := by
  rw [Matrix.det_mul, Matrix.det_submatrix_equiv_self, det_completion]

theorem completedImage_original (e : κ ⊕ ν ≃ ι) (u : Matrix ι κ R)
    (M : Matrix ι ι R) (i : κ ⊕ ν) (m : κ) :
    (M.submatrix e e * completion e u) i (.inl m) =
      ∑ j : ι, M (e i) j * u j m := by
  simp only [Matrix.mul_apply, Matrix.submatrix_apply, completion_original]
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

end Completion

/-- The k=d-6 chosen K-block coordinates fit in the actual six-block source. -/
def selectedKRow (d ell : ℕ) (hell : ell ≤ 6) :
    Fin (d - 6) ↪ (Fin 6 × Fin d) where
  toFun i := (3, ⟨ell + i.val, by have := i.isLt; omega⟩)
  inj' := by intro i j h; apply Fin.ext; have := congrArg (fun x => x.2.val) h; dsimp at this; omega

theorem selectedKRow_degree (d ell : ℕ) (hell : ell ≤ 6) (i : Fin (d - 6)) :
    (selectedKRow d ell hell i).2.val = ell + i.val := rfl

end Zeta7AnnularSource

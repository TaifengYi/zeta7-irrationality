import Mathlib

/-! C3, step 1: Andréief's identity.

For a finite measure `ν` and functions `φ_a, ψ_b` (`a, b < n`) whose pairwise products are
`ν`-integrable,

`n! · det [∫ φ_a ψ_b dν]_{a,b} = ∫ det[φ_a(z_b)] · det[ψ_a(z_b)] dν^n(z)`.

Proof: expanding the determinant and using Fubini for products (`integral_fintype_prod_eq_prod`),
`det A = ∫ (∏_i ψ_i(z_i)) det Φ(z) dν^n`. For every permutation `τ` the substitution
`z ↦ z ∘ τ` preserves `ν^n` and multiplies `det Φ` by `sign τ`; summing the resulting identities
over all `τ` produces `n!` on the left and `∫ det Φ det Ψ` on the right. All integrability
obligations reduce to the pairwise products by `Integrable.fintype_prod`. -/
noncomputable section
set_option autoImplicit false
namespace Zeta7Arch
open MeasureTheory Matrix Equiv

variable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}

/-- `A a b = ∫ φ_a ψ_b dν`. -/
def pairMatrix (ν : Measure Ω) (φ ψ : Fin n → Ω → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun a b => ∫ z, φ a z * ψ b z ∂ν

/-- `Φ(z) a b = φ_a(z_b)`. -/
def evalMatrix (φ : Fin n → Ω → ℂ) (z : Fin n → Ω) : Matrix (Fin n) (Fin n) ℂ :=
  fun a b => φ a (z b)

/-- The coordinate permutation `z ↦ z ∘ τ`. -/
def permEquiv (τ : Perm (Fin n)) : (Fin n → Ω) ≃ᵐ (Fin n → Ω) :=
  MeasurableEquiv.piCongrLeft (fun _ => Ω) τ.symm

theorem permEquiv_apply (τ : Perm (Fin n)) (z : Fin n → Ω) (j : Fin n) :
    permEquiv τ z j = z (τ j) := by
  rw [permEquiv, MeasurableEquiv.coe_piCongrLeft]
  have h := Equiv.piCongrLeft_apply_apply (fun _ : Fin n => Ω) τ.symm z (τ j)
  rwa [Equiv.symm_apply_apply] at h

theorem permEquiv_measurePreserving (ν : Measure Ω) [SigmaFinite ν] (τ : Perm (Fin n)) :
    MeasurePreserving (permEquiv τ) (Measure.pi fun _ : Fin n => ν)
      (Measure.pi fun _ : Fin n => ν) :=
  measurePreserving_piCongrLeft (fun _ : Fin n => ν) τ.symm

theorem evalMatrix_perm (φ : Fin n → Ω → ℂ) (τ : Perm (Fin n)) (z : Fin n → Ω) :
    evalMatrix φ (permEquiv τ z) = (evalMatrix φ z).submatrix id τ := by
  ext a b
  simp [evalMatrix, permEquiv_apply]

theorem det_evalMatrix_perm (φ : Fin n → Ω → ℂ) (τ : Perm (Fin n)) (z : Fin n → Ω) :
    (evalMatrix φ (permEquiv τ z)).det = (Perm.sign τ : ℂ) * (evalMatrix φ z).det := by
  rw [evalMatrix_perm, det_permute']

omit [MeasurableSpace Ω] in
/-- `det Ψ(z) = Σ_τ sign τ ∏_i ψ_i(z_{τ i})`. -/
theorem det_evalMatrix_eq_sum (ψ : Fin n → Ω → ℂ) (z : Fin n → Ω) :
    (evalMatrix ψ z).det = ∑ τ : Perm (Fin n), (Perm.sign τ : ℂ) * ∏ i, ψ i (z (τ i)) := by
  rw [← det_transpose, det_apply']
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp [evalMatrix, transpose_apply]

omit [MeasurableSpace Ω] in
/-- The expansion `Σ_σ sign σ ∏_i φ_{σ i}(z_i) ψ_i(z_i) = (∏ ψ_i(z_i)) det Φ(z)`. -/
theorem sum_sign_prod_eq (φ ψ : Fin n → Ω → ℂ) (z : Fin n → Ω) :
    ∑ σ : Perm (Fin n), (Perm.sign σ : ℂ) * ∏ i, (φ (σ i) (z i) * ψ i (z i)) =
      (∏ i, ψ i (z i)) * (evalMatrix φ z).det := by
  rw [det_apply', Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.prod_mul_distrib]
  simp only [evalMatrix]
  ring

section Andreief

variable (ν : Measure Ω) [IsFiniteMeasure ν] (φ ψ : Fin n → Ω → ℂ)
  (hint : ∀ a b, Integrable (fun z => φ a z * ψ b z) ν)
include hint

theorem integrable_sign_term (σ : Perm (Fin n)) :
    Integrable (fun z : Fin n → Ω => ∏ i, (φ (σ i) (z i) * ψ i (z i)))
      (Measure.pi fun _ : Fin n => ν) :=
  Integrable.fintype_prod (f := fun i z => φ (σ i) z * ψ i z) fun i => hint (σ i) i

/-- The first expansion: `det A = ∫ (∏_i ψ_i(z_i)) det Φ(z) dν^n`. -/
theorem det_pairMatrix_eq_integral :
    (pairMatrix ν φ ψ).det =
      ∫ z, (∏ i, ψ i (z i)) * (evalMatrix φ z).det ∂(Measure.pi fun _ : Fin n => ν) := by
  have hterm : ∀ σ : Perm (Fin n), ∏ i, pairMatrix ν φ ψ (σ i) i =
      ∫ z, ∏ i, (φ (σ i) (z i) * ψ i (z i)) ∂(Measure.pi fun _ : Fin n => ν) := by
    intro σ
    rw [integral_fintype_prod_eq_prod (f := fun i z => φ (σ i) z * ψ i z)]
    rfl
  rw [det_apply']
  simp_rw [hterm]
  simp_rw [← integral_const_mul]
  rw [← integral_finsetSum _ fun σ _ => (integrable_sign_term ν φ ψ hint σ).const_mul _]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  exact sum_sign_prod_eq φ ψ z

theorem integrable_main :
    Integrable (fun z : Fin n → Ω => (∏ i, ψ i (z i)) * (evalMatrix φ z).det)
      (Measure.pi fun _ : Fin n => ν) := by
  have h := integrable_finsetSum (Finset.univ : Finset (Perm (Fin n)))
    fun σ _ => (integrable_sign_term ν φ ψ hint σ).const_mul (Perm.sign σ : ℂ)
  refine h.congr (Filter.Eventually.of_forall fun z => ?_)
  exact sum_sign_prod_eq φ ψ z

/-- **Andréief's identity.** -/
theorem andreief :
    (n.factorial : ℂ) * (pairMatrix ν φ ψ).det =
      ∫ z, (evalMatrix φ z).det * (evalMatrix ψ z).det ∂(Measure.pi fun _ : Fin n => ν) := by
  set μn := Measure.pi fun _ : Fin n => ν with hμn
  set I : (Fin n → Ω) → ℂ := fun z => (∏ i, ψ i (z i)) * (evalMatrix φ z).det with hI
  set J : Perm (Fin n) → (Fin n → Ω) → ℂ := fun τ z => (∏ i, ψ i (z (τ i))) * (evalMatrix φ z).det
    with hJ
  have hIint : Integrable I μn := integrable_main ν φ ψ hint
  have hsq : ∀ τ : Perm (Fin n), (Perm.sign τ : ℂ) * (Perm.sign τ : ℂ) = 1 := by
    intro τ
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  -- the substitution identity
  have hsub : ∀ τ : Perm (Fin n), ∀ z, I (permEquiv τ z) = (Perm.sign τ : ℂ) * J τ z := by
    intro τ z
    simp only [hI, hJ, det_evalMatrix_perm, permEquiv_apply]
    ring
  have hJint : ∀ τ : Perm (Fin n), Integrable (J τ) μn := by
    intro τ
    have h := ((permEquiv_measurePreserving ν τ).integrable_comp_emb
      (permEquiv τ).measurableEmbedding).mpr hIint
    refine (h.const_mul (Perm.sign τ : ℂ)).congr (Filter.Eventually.of_forall fun z => ?_)
    simp only [Function.comp_apply, hsub, ← mul_assoc, hsq, one_mul]
  have hstep : ∀ τ : Perm (Fin n), (Perm.sign τ : ℂ) * ∫ z, J τ z ∂μn = ∫ z, I z ∂μn := by
    intro τ
    rw [← (permEquiv_measurePreserving ν τ).integral_comp' I]
    simp_rw [hsub]
    rw [integral_const_mul]
  have hdetI := det_pairMatrix_eq_integral ν φ ψ hint
  calc (n.factorial : ℂ) * (pairMatrix ν φ ψ).det
      = ∑ _τ : Perm (Fin n), ∫ z, I z ∂μn := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
          nsmul_eq_mul, hdetI]
    _ = ∑ τ : Perm (Fin n), (Perm.sign τ : ℂ) * ∫ z, J τ z ∂μn :=
        Finset.sum_congr rfl fun τ _ => (hstep τ).symm
    _ = ∫ z, ∑ τ : Perm (Fin n), (Perm.sign τ : ℂ) * J τ z ∂μn := by
        rw [integral_finsetSum _ fun τ _ => (hJint τ).const_mul _]
        simp_rw [integral_const_mul]
    _ = ∫ z, (evalMatrix φ z).det * (evalMatrix ψ z).det ∂μn := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        simp only [hJ]
        rw [det_evalMatrix_eq_sum ψ z, Finset.mul_sum]
        refine Finset.sum_congr rfl fun τ _ => ?_
        ring

end Andreief

end Zeta7Arch

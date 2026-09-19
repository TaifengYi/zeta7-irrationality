import Mathlib.RingTheory.Trace.Defs
import Mathlib.RingTheory.PowerSeries.Restricted
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors

/-! Finite-free trace and descent of algebraic idempotents.
All finiteness data below is an actual basis. No analytic continuation data occurs. -/

set_option autoImplicit false
noncomputable section
namespace Zeta7Radius49
open scoped TensorProduct
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable {m : ℕ} (b : Module.Basis (Fin m) R S) (hm : IsUnit (m : R))

def normalizedTrace : S →ₗ[R] R :=
  (↑(hm.unit⁻¹) : R) • Algebra.trace R S

include b

theorem scalar_trace (a : R) :
    Algebra.trace R S (algebraMap R S a) = (m : R) * a := by
  simpa only [Fintype.card_fin, nsmul_eq_mul] using Algebra.trace_algebraMap_of_basis b a

theorem normalizedTrace_scalar (a : R) :
    normalizedTrace hm (algebraMap R S a) = a := by
  change (↑(hm.unit⁻¹) : R) * Algebra.trace R S (algebraMap R S a) = a
  rw [scalar_trace b a, ← mul_assoc, hm.val_inv_mul, one_mul]

theorem normalizedTrace_one : normalizedTrace hm (1 : S) = 1 := by
  simpa only [map_one] using normalizedTrace_scalar b hm (1 : R)

include hm

theorem scalar_inclusion_injective : Function.Injective (algebraMap R S) :=
  Function.LeftInverse.injective (normalizedTrace_scalar b hm)

/-- A tensor equalizer element descends by applying normalized trace to the second factor. -/
theorem normalizedTrace_descends (e : S)
    (he : e ⊗ₜ[R] (1 : S) = (1 : S) ⊗ₜ[R] e) :
    algebraMap R S (normalizedTrace hm e) = e := by
  let L : S ⊗[R] S →ₗ[R] S :=
    (TensorProduct.rid R S).toLinearMap.comp
      (TensorProduct.map (LinearMap.id : S →ₗ[R] S) (normalizedTrace hm))
  have h := congrArg L he
  simpa [L, normalizedTrace_one b hm, Algebra.smul_def] using h.symm

theorem normalizedTrace_idempotent (e : S) (he : e * e = e)
    (hdesc : e ⊗ₜ[R] (1 : S) = (1 : S) ⊗ₜ[R] e) :
    normalizedTrace hm e * normalizedTrace hm e = normalizedTrace hm e := by
  apply scalar_inclusion_injective b hm
  rw [map_mul, normalizedTrace_descends b hm e hdesc, he]

theorem descended_idempotent_zero_or_one [IsDomain R] (e : S) (he : e * e = e)
    (hdesc : e ⊗ₜ[R] (1 : S) = (1 : S) ⊗ₜ[R] e) :
    normalizedTrace hm e = 0 ∨ normalizedTrace hm e = 1 := by
  have h := normalizedTrace_idempotent b hm e he hdesc
  have hprod : normalizedTrace hm e * (normalizedTrace hm e - 1) = 0 := by
    rw [mul_sub, mul_one, h, sub_self]
  exact (mul_eq_zero.mp hprod).imp id sub_eq_zero.mp

theorem idempotent_eq_one_of_nonzero [IsDomain R] (e : S) (he : e * e = e)
    (hdesc : e ⊗ₜ[R] (1 : S) = (1 : S) ⊗ₜ[R] e) (hne : e ≠ 0) : e = 1 := by
  rcases descended_idempotent_zero_or_one b hm e he hdesc with h | h
  · have hd := normalizedTrace_descends b hm e hdesc
    rw [h, map_zero] at hd
    exact False.elim (hne hd.symm)
  · have hd := normalizedTrace_descends b hm e hdesc
    rwa [h, map_one, eq_comm] at hd

omit hm in
theorem trace_baseChange (f : S →ₗ[R] S) (A : Type*) [CommRing A] [Algebra R A] :
    LinearMap.trace A (A ⊗[R] S) (f.baseChange A) =
      algebraMap R A (LinearMap.trace R S f) := by
  letI : Module.Free R S := Module.Free.of_basis b
  letI : Module.Finite R S := Module.Finite.of_basis b
  exact LinearMap.trace_baseChange f A

omit hm in
theorem algebra_trace_baseChange (e : S) (A : Type*) [CommRing A] [Algebra R A] :
    Algebra.trace A (A ⊗[R] S) ((1 : A) ⊗ₜ[R] e) =
      algebraMap R A (Algebra.trace R S e) := by
  have he : Algebra.lmul A (A ⊗[R] S) ((1 : A) ⊗ₜ[R] e) =
      (Algebra.lmul R S e).baseChange A := by
    ext a s
    simp [Algebra.TensorProduct.tmul_mul_tmul]
  rw [Algebra.trace_apply, he]
  exact trace_baseChange b (Algebra.lmul R S e) A

theorem normalizedTrace_baseChange (e : S) (A : Type*) [CommRing A] [Algebra R A] :
    algebraMap R A (normalizedTrace hm e) =
      algebraMap R A (↑(hm.unit⁻¹) : R) *
        Algebra.trace A (A ⊗[R] S) ((1 : A) ⊗ₜ[R] e) := by
  rw [algebra_trace_baseChange b e A]
  change algebraMap R A ((↑(hm.unit⁻¹) : R) * Algebra.trace R S e) = _
  exact map_mul _ _ _

omit b hm in
theorem restricted_idempotent_zero_or_one (K : Type*) [NormedField K]
    [IsUltrametricDist K] (s : ℝ)
    (f : PowerSeries.IsRestricted.subring (R := K) s) (hf : f * f = f) :
    f = 0 ∨ f = 1 := by
  have h : f * (f - 1) = 0 := by rw [mul_sub, mul_one, hf, sub_self]
  exact (mul_eq_zero.mp h).imp id sub_eq_zero.mp

end Zeta7Radius49

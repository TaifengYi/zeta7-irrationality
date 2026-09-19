import Zeta7Proof.PolynomialBlockBridge
import Zeta7Proof.ActualLH
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.FieldTheory.Laurent

/-! Euler calculus on the canonical Laurent field used by the original germs. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open scoped LaurentSeries RatFunc
open HahnSeries PowerSeries
namespace Zeta7Germ

def laurentEuler (f : ℂ⸨X⸩) : ℂ⸨X⸩ where
  coeff n := (n : ℂ) * f.coeff n
  isPWO_support' := f.isPWO_support.mono (by
    intro n hn
    contrapose! hn
    simp only [HahnSeries.mem_support, not_not] at hn
    simp [hn])

@[simp] theorem laurentEuler_coeff (f : ℂ⸨X⸩) (n : ℤ) :
    (laurentEuler f).coeff n = (n : ℂ) * f.coeff n := rfl

theorem laurentEuler_support (f : ℂ⸨X⸩) : (laurentEuler f).support ⊆ f.support := by
  intro n hn
  simp only [mem_support, laurentEuler_coeff, ne_eq] at *
  exact fun h => hn (by rw [h, mul_zero])

@[simp] theorem laurentEuler_add (f g : ℂ⸨X⸩) :
    laurentEuler (f + g) = laurentEuler f + laurentEuler g := by
  ext n
  simp [mul_add]

@[simp] theorem laurentEuler_C (a : ℂ) : laurentEuler (HahnSeries.C a) = 0 := by
  ext n
  by_cases hn : n = 0 <;> simp [HahnSeries.C_apply, hn]

@[simp] theorem laurentEuler_one : laurentEuler 1 = 0 := by
  simpa using laurentEuler_C 1

@[simp] theorem laurentEuler_zero : laurentEuler 0 = 0 := by ext n; simp

theorem laurentEuler_mul (f g : ℂ⸨X⸩) :
    laurentEuler (f * g) = laurentEuler f * g + f * laurentEuler g := by
  classical
  ext n
  rw [laurentEuler_coeff, coeff_add,
    coeff_mul_left' f.isPWO_support (laurentEuler_support f),
    coeff_mul_right' g.isPWO_support (laurentEuler_support g), HahnSeries.coeff_mul,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ij hij
  have he : ij.1 + ij.2 = n := (Finset.mem_antidiagonal.mp hij).2.2
  rw [← he, Int.cast_add, laurentEuler_coeff, laurentEuler_coeff]
  ring

theorem laurentEuler_smul (a : ℂ) (f : ℂ⸨X⸩) :
    laurentEuler (a • f) = a • laurentEuler f := by
  ext n
  simp [mul_left_comm]

def laurentD : Derivation ℂ ℂ⸨X⸩ ℂ⸨X⸩ where
  toFun := laurentEuler
  map_add' := laurentEuler_add
  map_smul' a f := by
    simp only [Algebra.smul_def, RingHom.id_apply]
    have ha : (algebraMap ℂ ℂ⸨X⸩) a = HahnSeries.C a := by
      change HahnSeries.ofPowerSeries ℤ ℂ ((algebraMap ℂ ℂ⟦X⟧) a) = _
      exact HahnSeries.ofPowerSeries_C a
    rw [ha]
    ext n
    simp [HahnSeries.C_apply, coeff_single_zero_mul,
      mul_left_comm]
  map_one_eq_zero' := laurentEuler_one
  leibniz' f g := by simpa [smul_eq_mul, mul_comm, add_comm] using laurentEuler_mul f g

theorem laurentD_powerSeries (f : ℂ⟦X⟧) :
    laurentD (f : ℂ⸨X⸩) = (Zeta7Common.euler f : ℂ⟦X⟧) := by
  ext n
  change (n : ℂ) * (f : ℂ⸨X⸩).coeff n = _
  cases n with
  | ofNat n => simp [PowerSeries.coeff_coe, Zeta7Common.euler_coeff]
  | negSucc n => simp [PowerSeries.coeff_coe]

end Zeta7Germ

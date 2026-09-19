import Zeta7Proof.AnnularGaussBounds
import Mathlib.Algebra.Ring.MinimalAxioms
import Mathlib.Analysis.Normed.Unbundled.RingSeminorm

/-! The closed annulus as an actual normed ring of bilateral coefficients.
Multiplication is the summable convolution proved in the preceding modules. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
namespace Zeta7Annulus
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

@[ext] structure ClosedAnnulus (r R : ℝ) where
  coeffs : LaurentCoefficients
  inner : DecaysAt coeffs r
  outer : DecaysAt coeffs R

namespace ClosedAnnulus
variable {r R : ℝ} [Fact (0 < r)] [Fact (0 < R)]

instance : Zero (ClosedAnnulus r R) := ⟨⟨0, by simp [DecaysAt], by simp [DecaysAt]⟩⟩
instance : Add (ClosedAnnulus r R) := ⟨fun a b =>
  ⟨a.coeffs + b.coeffs, a.inner.add b.inner (Fact.out), a.outer.add b.outer (Fact.out)⟩⟩
instance : Neg (ClosedAnnulus r R) := ⟨fun a => ⟨-a.coeffs, a.inner.neg, a.outer.neg⟩⟩
instance : One (ClosedAnnulus r R) :=
  ⟨⟨bilateralMonomial 0 1, bilateralMonomial_decays _ _ _, bilateralMonomial_decays _ _ _⟩⟩
instance : Mul (ClosedAnnulus r R) := ⟨fun a b =>
  ⟨bilateralConvolution a.coeffs b.coeffs,
    a.inner.bilateralConvolution b.inner (Fact.out),
    a.outer.bilateralConvolution b.outer (Fact.out)⟩⟩

@[simp] theorem coeffs_zero : (0 : ClosedAnnulus r R).coeffs = 0 := rfl
@[simp] theorem coeffs_add (a b : ClosedAnnulus r R) : (a + b).coeffs = a.coeffs + b.coeffs := rfl
@[simp] theorem coeffs_neg (a : ClosedAnnulus r R) : (-a).coeffs = -a.coeffs := rfl
@[simp] theorem coeffs_one : (1 : ClosedAnnulus r R).coeffs = bilateralMonomial 0 1 := rfl
@[simp] theorem coeffs_mul (a b : ClosedAnnulus r R) :
    (a * b).coeffs = bilateralConvolution a.coeffs b.coeffs := rfl

instance : CommRing (ClosedAnnulus r R) := CommRing.ofMinimalAxioms
  (fun a b c => by ext k; exact add_assoc _ _ _)
  (fun a => by ext k; exact zero_add _)
  (fun a => by ext k; exact neg_add_cancel _)
  (fun a b c => ClosedAnnulus.ext (bilateralConvolution_assoc a.inner b.inner c.inner Fact.out))
  (fun a b => ClosedAnnulus.ext (bilateralConvolution_comm _ _))
  (fun a => by ext k; simp [bilateralMonomial_convolution])
  (fun a b c => ClosedAnnulus.ext
    (bilateralConvolution_add_right a.inner b.inner c.inner Fact.out))

@[simp] theorem coeffs_sub (a b : ClosedAnnulus r R) : (a - b).coeffs = a.coeffs - b.coeffs := by
  simp only [sub_eq_add_neg, coeffs_add, coeffs_neg]

theorem gauss_nonneg (a : ClosedAnnulus r R) : 0 ≤ closedAnnulusGauss a.coeffs r R :=
  (bilateralGauss_nonneg a.inner Fact.out).trans (le_max_left _ _)

theorem gauss_add (a b : ClosedAnnulus r R) :
    closedAnnulusGauss (a + b).coeffs r R ≤
      max (closedAnnulusGauss a.coeffs r R) (closedAnnulusGauss b.coeffs r R) := by
  apply max_le
  · exact (bilateralGauss_add a.inner b.inner Fact.out).trans
      (max_le_max (le_max_left _ _) (le_max_left _ _))
  · exact (bilateralGauss_add a.outer b.outer Fact.out).trans
      (max_le_max (le_max_right _ _) (le_max_right _ _))

theorem gauss_mul (a b : ClosedAnnulus r R) :
    closedAnnulusGauss (a * b).coeffs r R ≤
      closedAnnulusGauss a.coeffs r R * closedAnnulusGauss b.coeffs r R := by
  apply max_le
  · exact (bilateralGauss_convolution a.inner b.inner Fact.out).trans
      (mul_le_mul (le_max_left _ _) (le_max_left _ _)
        (bilateralGauss_nonneg b.inner Fact.out) a.gauss_nonneg)
  · exact (bilateralGauss_convolution a.outer b.outer Fact.out).trans
      (mul_le_mul (le_max_right _ _) (le_max_right _ _)
        (bilateralGauss_nonneg b.outer Fact.out) a.gauss_nonneg)

def ringNorm : RingNorm (ClosedAnnulus r R) where
  toFun a := closedAnnulusGauss a.coeffs r R
  map_zero' := by simp [closedAnnulusGauss, bilateralGauss, weightedCoefficient]
  add_le' a b := (gauss_add a b).trans (max_le (le_add_of_nonneg_right b.gauss_nonneg)
    (le_add_of_nonneg_left a.gauss_nonneg))
  neg' a := by simp only [coeffs_neg, closedAnnulusGauss, bilateralGauss_neg]
  mul_le' := gauss_mul
  eq_zero_of_map_eq_zero' a h := by
    apply ClosedAnnulus.ext
    apply (bilateralGauss_eq_zero_iff a.inner Fact.out).mp
    apply le_antisymm _ (bilateralGauss_nonneg a.inner Fact.out)
    exact (le_max_left _ _).trans h.le

instance : NormedRing (ClosedAnnulus r R) := ringNorm.toNormedRing

@[simp] theorem norm_eq (a : ClosedAnnulus r R) : ‖a‖ = closedAnnulusGauss a.coeffs r R := rfl

theorem norm_add_le_max (a b : ClosedAnnulus r R) : ‖a + b‖ ≤ max ‖a‖ ‖b‖ := gauss_add a b

theorem coeff_norm_le (a : ClosedAnnulus r R) (k : ℤ) : ‖a.coeffs k‖ ≤ ‖a‖ * r ^ (-k) :=
  (coefficient_norm_le_gauss a.inner Fact.out k).trans
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (zpow_pos (Fact.out : 0 < r) _).le)

def euler (a : ClosedAnnulus r R) : ClosedAnnulus r R :=
  ⟨bilateralEuler a.coeffs, a.inner.euler Fact.out, a.outer.euler Fact.out⟩

theorem euler_norm_le (a : ClosedAnnulus r R) : ‖euler a‖ ≤ ‖a‖ :=
  max_le_max (bilateralGauss_euler a.inner Fact.out) (bilateralGauss_euler a.outer Fact.out)

theorem euler_mul (a b : ClosedAnnulus r R) : euler (a * b) = euler a * b + a * euler b :=
  ClosedAnnulus.ext (bilateralEuler_leibniz a.inner b.inner Fact.out)

end ClosedAnnulus
end Zeta7Annulus

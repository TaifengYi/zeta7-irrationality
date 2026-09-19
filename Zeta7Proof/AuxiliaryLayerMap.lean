import Zeta7Proof.AuxiliaryCaps
import Mathlib.Algebra.Module.ZMod

/-! A well-defined linear residue map on every finite capped coefficient lattice. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
namespace Zeta7Auxiliary
variable (p : ℕ) [Fact p.Prime]

local instance residueAlgebra : Algebra ℤ_[p] (ZMod p) := PadicInt.toZMod.toAlgebra

def cappedVectors (N e : ℕ) : Submodule ℤ_[p] (Fin N → ℚ_[p]) where
  carrier := {v | ∀ i, Integral ((p : ℚ_[p]) ^ e * v i)}
  zero_mem' := by intro i; simpa using (integral_zero (p := p))
  add_mem' hx hy := by intro i; simpa only [Pi.add_apply, mul_add] using (hx i).add (hy i)
  smul_mem' a v hv := by
    intro i
    simpa only [Pi.smul_apply, Algebra.smul_def, PadicInt.algebraMap_apply, mul_left_comm]
      using (integral_coe a).mul (hv i)

def scaledIntegralVector (N e : ℕ) : cappedVectors p N e →ₗ[ℤ_[p]] (Fin N → ℤ_[p]) where
  toFun v i := ⟨(p : ℚ_[p]) ^ e * v.val i, v.property i⟩
  map_add' v w := by
    ext i
    change (p : ℚ_[p]) ^ e * (v.val i + w.val i) =
      (p : ℚ_[p]) ^ e * v.val i + (p : ℚ_[p]) ^ e * w.val i
    ring
  map_smul' a v := by
    ext i
    simp [Algebra.smul_def, mul_left_comm]

def residueLinear : ℤ_[p] →ₗ[ℤ_[p]] ZMod p where
  toFun := PadicInt.toZMod
  map_add' := map_add _
  map_smul' a b := by
    change PadicInt.toZMod (a * b) = PadicInt.toZMod a * PadicInt.toZMod b
    exact map_mul _ _ _

def layerMap (N e : ℕ) : cappedVectors p N e →ₗ[ℤ_[p]] (Fin N → ZMod p) :=
  LinearMap.pi (fun i => (residueLinear p).comp ((LinearMap.proj i).comp (scaledIntegralVector p N e)))

theorem layerMap_apply (N e : ℕ) (v : cappedVectors p N e) (i : Fin N) :
    layerMap p N e v i = PadicInt.toZMod
      (⟨(p : ℚ_[p]) ^ e * v.val i, v.property i⟩ : ℤ_[p]) := rfl

theorem layerMap_prime_smul (N e : ℕ) (v : cappedVectors p N e) :
    layerMap p N e ((p : ℤ_[p]) • v) = 0 := by
  rw [map_smul]
  ext i
  simp [Algebra.smul_def, residueAlgebra]

/-- Equality modulo p times the capped lattice gives the same residue layer. -/
theorem layerMap_congr_mod_prime (N e : ℕ) (v w z : cappedVectors p N e)
    (h : v - w = (p : ℤ_[p]) • z) : layerMap p N e v = layerMap p N e w := by
  apply sub_eq_zero.mp
  rw [← map_sub, h, layerMap_prime_smul]

def primeLattice (N e : ℕ) : Submodule ℤ_[p] (cappedVectors p N e) :=
  LinearMap.range ((p : ℤ_[p]) • LinearMap.id)

theorem primeLattice_le_kernel (N e : ℕ) : primeLattice p N e ≤ (layerMap p N e).ker := by
  rintro _ ⟨v, rfl⟩
  exact layerMap_prime_smul p N e v

/-- The layer map descends to the quotient by p times the capped source lattice. -/
def quotientLayerMap (N e : ℕ) :
    (cappedVectors p N e ⧸ primeLattice p N e) →ₗ[ℤ_[p]] (Fin N → ZMod p) :=
  (primeLattice p N e).liftQ (layerMap p N e) (primeLattice_le_kernel p N e)

theorem quotient_prime_nsmul (N e : ℕ)
    (v : cappedVectors p N e ⧸ primeLattice p N e) : p • v = 0 := by
  induction v using Submodule.Quotient.induction_on with
  | H v =>
    change p • (primeLattice p N e).mkQ v = 0
    rw [← map_nsmul]
    apply (Submodule.Quotient.mk_eq_zero (primeLattice p N e)).mpr
    refine ⟨v, ?_⟩
    simp [Nat.cast_smul_eq_nsmul]

instance quotientLayerModule (N e : ℕ) :
    Module (ZMod p) (cappedVectors p N e ⧸ primeLattice p N e) :=
  AddCommGroup.zmodModule (quotient_prime_nsmul p N e)

/-- The reduced layer is genuinely linear over the residue field. -/
def residueFieldLayerMap (N e : ℕ) :
    (cappedVectors p N e ⧸ primeLattice p N e) →ₗ[ZMod p] (Fin N → ZMod p) :=
  (quotientLayerMap p N e).toAddMonoidHom.toZModLinearMap p

theorem residueFieldLayerMap_mk (N e : ℕ) (v : cappedVectors p N e) :
    residueFieldLayerMap p N e ((primeLattice p N e).mkQ v) = layerMap p N e v := rfl

end Zeta7Auxiliary

import Zeta7Proof.Radius49FormalIdentification
import Stage2A

/-! Rational germs defined from the exact modular formal series.
These definitions do not depend on the separate Stage2B recurrence. -/

set_option autoImplicit false
noncomputable section
open PowerSeries
namespace Zeta7Common
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

def rationalH (c : ℚ) : ℚ⟦X⟧ :=
  Zeta7Main.BSeries * (Zeta7Main.GSeries.subst Zeta7Main.qSeries + C c)

theorem rationalH_map (c : ℚ) (hc : (c : ℚ_[7]) = Zeta7Main.eta) :
    (rationalH c).map (algebraMap ℚ ℚ_[7]) = Zeta7Main.HSeries := by
  unfold rationalH Zeta7Main.HSeries
  rw [map_mul, map_add, map_C]
  change _ * (_ + C (c : ℚ_[7])) = _
  rw [hc]
  rfl

def euler {K : Type*} [CommRing K] (f : K⟦X⟧) : K⟦X⟧ :=
  X * derivative K f

def primitive {K : Type*} [Field K] (f : K⟦X⟧) : K⟦X⟧ :=
  mk (fun n => if n = 0 then 0 else coeff (n - 1) f / (n : K))

def rationalPotential : ℚ⟦X⟧ :=
  8 * X * (1 + 16 * X + 49 * X ^ 2) * ((1 + 13 * X + 49 * X ^ 2) ^ 2)⁻¹

def quadratic {K : Type*} [Field K] (V f : K⟦X⟧) : K⟦X⟧ :=
  f * euler (euler f) - C (1 / 2 : K) * (euler f) ^ 2 - C (1 / 2 : K) * V * f ^ 2

def germs {K : Type*} [Field K] (V f : K⟦X⟧) : Fin 6 → K⟦X⟧ :=
  ![f, euler f, euler (euler f), quadratic V f,
    primitive (quadratic V f), primitive (primitive (quadratic V f))]

def rationalGerms (c : ℚ) : Fin 6 → ℚ⟦X⟧ := germs rationalPotential (rationalH c)

def targetGerms : Fin 6 → ℚ_[7]⟦X⟧ :=
  germs (rationalPotential.map (algebraMap ℚ ℚ_[7])) Zeta7Main.HSeries

theorem euler_coeff {K : Type*} [CommRing K] (f : K⟦X⟧) (n : ℕ) :
    coeff n (euler f) = (n : K) * coeff n f := by
  cases n with
  | zero => simp [euler]
  | succ n =>
    simp only [euler, coeff_succ_X_mul, coeff_derivative]
    push_cast
    ring

theorem map_euler {K L : Type*} [CommRing K] [CommRing L] (φ : K →+* L)
    (f : K⟦X⟧) : (euler f).map φ = euler (f.map φ) := by
  ext n
  simp [coeff_map, euler_coeff]

theorem map_primitive {K L : Type*} [Field K] [Field L] (φ : K →+* L)
    (f : K⟦X⟧) : (primitive f).map φ = primitive (f.map φ) := by
  ext n
  by_cases hn : n = 0 <;> simp [primitive, coeff_map, hn]

theorem map_quadratic {K L : Type*} [Field K] [Field L] (φ : K →+* L)
    (V f : K⟦X⟧) :
    (quadratic V f).map φ = quadratic (V.map φ) (f.map φ) := by
  simp [quadratic, map_euler, map_ofNat]

theorem map_germs {K L : Type*} [Field K] [Field L] (φ : K →+* L)
    (V f : K⟦X⟧) (j : Fin 6) :
    (germs V f j).map φ = germs (V.map φ) (f.map φ) j := by
  fin_cases j <;> simp [germs, map_euler, map_quadratic, map_primitive]

/-- All six complete target germs are the scalar extensions of these rational germs. -/
theorem rationalGerms_map (c : ℚ) (hc : (c : ℚ_[7]) = Zeta7Main.eta) (j : Fin 6) :
    (rationalGerms c j).map (algebraMap ℚ ℚ_[7]) = targetGerms j := by
  rw [rationalGerms, map_germs, rationalH_map c hc]
  rfl

abbrev TailIndex (d : ℕ) := Fin 6 × Fin d
abbrev BlockIndex (d : ℕ) := Fin d ⊕ TailIndex d

def blockSeries {K : Type*} [CommRing K] (d : ℕ) (g : Fin 6 → K⟦X⟧) :
    BlockIndex d → K⟦X⟧
  | .inl k => X ^ k.val
  | .inr jk => X ^ jk.2.val * g jk.1

def coefficientRow {K : Type*} [CommRing K] (d : ℕ) (g : Fin 6 → K⟦X⟧)
    (n : ℕ) : BlockIndex d → K := fun j => coeff n (blockSeries d g j)

def fullMatrix {K : Type*} [CommRing K] (d : ℕ) (g : Fin 6 → K⟦X⟧)
    (row : TailIndex d → ℕ) : Matrix (BlockIndex d) (BlockIndex d) K :=
  fun i => coefficientRow d g (Sum.elim Fin.val row i)

def tailMatrix {K : Type*} [CommRing K] (d : ℕ) (g : Fin 6 → K⟦X⟧)
    (row : TailIndex d → ℕ) : Matrix (TailIndex d) (TailIndex d) K :=
  fun i j => coeff (row i) (X ^ j.2.val * g j.1)

def topRight {K : Type*} [CommRing K] (d : ℕ) (g : Fin 6 → K⟦X⟧) :
    Matrix (Fin d) (TailIndex d) K :=
  fun i j => coeff i.val (X ^ j.2.val * g j.1)

theorem fullMatrix_blocks {K : Type*} [CommRing K] (d : ℕ) (g : Fin 6 → K⟦X⟧)
    (row : TailIndex d → ℕ) (hrow : ∀ i, d ≤ row i) :
    fullMatrix d g row = Matrix.fromBlocks (1 : Matrix (Fin d) (Fin d) K)
      (topRight d g) (0 : Matrix (TailIndex d) (Fin d) K) (tailMatrix d g row) := by
  classical
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · simp [fullMatrix, coefficientRow, blockSeries, coeff_X_pow, Matrix.one_apply, Fin.ext_iff]
  · rfl
  · have hne : row i ≠ j.val := by have := hrow i; have := j.isLt; omega
    simp [fullMatrix, coefficientRow, blockSeries, coeff_X_pow, hne]
  · rfl

theorem det_fullMatrix {K : Type*} [CommRing K] (d : ℕ) (g : Fin 6 → K⟦X⟧)
    (row : TailIndex d → ℕ) (hrow : ∀ i, d ≤ row i) :
    (fullMatrix d g row).det = (tailMatrix d g row).det := by
  rw [fullMatrix_blocks d g row hrow, Matrix.det_fromBlocks_zero₂₁]
  simp

theorem tailMatrix_eq_stage2 (d : ℕ) (c : ℚ) (row : TailIndex d → ℕ)
    (hrow : ∀ i, d ≤ row i) :
    tailMatrix d (rationalGerms c) row =
      Zeta7Stage2A.tailMatrix d (fun j n => coeff n (rationalGerms c j)) row := by
  ext i j
  simp only [tailMatrix, Zeta7Stage2A.tailMatrix, coeff_X_pow_mul']
  rw [ite_eq_left (by have := hrow i; have := j.2.isLt; omega)]

/-- Equality of the actual target tail determinant with one rational determinant. -/
theorem target_det_eq_ratCast (d : ℕ) (c : ℚ) (hc : (c : ℚ_[7]) = Zeta7Main.eta)
    (row : TailIndex d → ℕ) :
    (tailMatrix d targetGerms row).det =
      ((tailMatrix d (rationalGerms c) row).det : ℚ_[7]) := by
  have hm : tailMatrix d targetGerms row =
      (tailMatrix d (rationalGerms c) row).map (algebraMap ℚ ℚ_[7]) := by
    ext i j
    change coeff (row i) (X ^ j.2.val * targetGerms j.1) =
      (algebraMap ℚ ℚ_[7]) (coeff (row i) (X ^ j.2.val * rationalGerms c j.1))
    rw [← rationalGerms_map c hc j.1, ← coeff_map]
    simp only [map_mul (PowerSeries.map (algebraMap ℚ ℚ_[7])),
      map_pow (PowerSeries.map (algebraMap ℚ ℚ_[7])), map_X]
  rw [hm]
  exact ((algebraMap ℚ ℚ_[7]).map_det _).symm

/-- Base change applies entrywise to the same selected matrix, in every degree. -/
theorem tailMatrix_map {K L : Type*} [CommRing K] [CommRing L] (φ : K →+* L)
    (d : ℕ) (g : Fin 6 → K⟦X⟧) (row : TailIndex d → ℕ) :
    tailMatrix d (fun j => (g j).map φ) row = (tailMatrix d g row).map φ := by
  ext i j
  change coeff (row i) (X ^ j.2.val * (g j.1).map φ) =
    φ (coeff (row i) (X ^ j.2.val * g j.1))
  rw [← coeff_map]
  simp only [map_mul (PowerSeries.map φ), map_pow (PowerSeries.map φ), map_X]

theorem det_tailMatrix_map {K L : Type*} [CommRing K] [CommRing L] (φ : K →+* L)
    (d : ℕ) (g : Fin 6 → K⟦X⟧) (row : TailIndex d → ℕ) :
    (tailMatrix d (fun j => (g j).map φ) row).det = φ (tailMatrix d g row).det := by
  rw [tailMatrix_map]
  exact (φ.map_det _).symm

end Zeta7Common

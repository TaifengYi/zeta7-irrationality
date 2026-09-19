import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices
import Mathlib.GroupTheory.Schreier

/-! The explicit eight-representative calculation for Γ₀(7).
All matrix and residue calculations below are checked by the kernel. -/
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open Matrix Matrix.SpecialLinearGroup ModularGroup Subgroup
open scoped MatrixGroups
namespace Zeta7LevelSeven

def cosetRep (i : Fin 8) : SL(2, ℤ) :=
  if i = 0 then 1 else S * T ^ ((i.val : ℤ) - 1)

def nextS : Fin 8 → Fin 8 := ![1, 0, 7, 4, 3, 6, 5, 2]
def nextT : Fin 8 → Fin 8 := ![0, 2, 3, 4, 5, 6, 7, 1]
def prevT : Fin 8 → Fin 8 := ![0, 7, 1, 2, 3, 4, 5, 6]

theorem nextS_involutive (i : Fin 8) : nextS (nextS i) = i := by
  fin_cases i <;> decide
theorem nextT_prevT (i : Fin 8) : nextT (prevT i) = i := by
  fin_cases i <;> decide

def schreierS (i : Fin 8) : SL(2, ℤ) := cosetRep i * S * (cosetRep (nextS i))⁻¹
def schreierT (i : Fin 8) : SL(2, ℤ) := cosetRep i * T * (cosetRep (nextT i))⁻¹

theorem schreierS_mem (i : Fin 8) : schreierS i ∈ CongruenceSubgroup.Gamma0 7 := by
  change (schreierS i 1 0 : ZMod 7) = 0
  fin_cases i <;> decide

theorem schreierT_mem (i : Fin 8) : schreierT i ∈ CongruenceSubgroup.Gamma0 7 := by
  change (schreierT i 1 0 : ZMod 7) = 0
  fin_cases i <;> decide

theorem cosetRep_mem_iff (i : Fin 8) :
    cosetRep i ∈ CongruenceSubgroup.Gamma0 7 ↔ i = 0 := by
  change (cosetRep i 1 0 : ZMod 7) = 0 ↔ i = 0
  fin_cases i <;> decide

def schreierGroup : Subgroup SL(2, ℤ) :=
  closure (Set.range schreierS ∪ Set.range schreierT)

theorem schreierGroup_le : schreierGroup ≤ CongruenceSubgroup.Gamma0 7 := by
  apply (Subgroup.closure_le _).mpr
  rintro g (⟨i, rfl⟩ | ⟨i, rfl⟩)
  · exact schreierS_mem i
  · exact schreierT_mem i

theorem schreierS_mem_group (i : Fin 8) : schreierS i ∈ schreierGroup :=
  subset_closure (Or.inl ⟨i, rfl⟩)
theorem schreierT_mem_group (i : Fin 8) : schreierT i ∈ schreierGroup :=
  subset_closure (Or.inr ⟨i, rfl⟩)

/-- Rewriting works for every SL₂(ℤ) matrix, including inverse letters. -/
theorem schreier_decomposition (g : SL(2, ℤ)) :
    ∃ h ∈ schreierGroup, ∃ i : Fin 8, g = h * cosetRep i := by
  have hg : g ∈ Subgroup.closure ({S, T} : Set SL(2, ℤ)) := by
    rw [SpecialLinearGroup.SL2Z_generators]
    trivial
  induction hg using Subgroup.closure_induction_right with
  | one => exact ⟨1, schreierGroup.one_mem, 0, by simp [cosetRep]⟩
  | mul_right x hx s hs ih =>
    obtain ⟨h, hh, i, rfl⟩ := ih
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl
    · exact ⟨h * schreierS i, schreierGroup.mul_mem hh (schreierS_mem_group i),
        nextS i, by simp [schreierS, mul_assoc]⟩
    · exact ⟨h * schreierT i, schreierGroup.mul_mem hh (schreierT_mem_group i),
        nextT i, by simp [schreierT, mul_assoc]⟩
  | mul_inv_cancel x hx s hs ih =>
    obtain ⟨h, hh, i, rfl⟩ := ih
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl
    · refine ⟨h * (schreierS (nextS i))⁻¹,
        schreierGroup.mul_mem hh (schreierGroup.inv_mem (schreierS_mem_group _)), nextS i, ?_⟩
      simp [schreierS, nextS_involutive, mul_assoc]
    · refine ⟨h * (schreierT (prevT i))⁻¹,
        schreierGroup.mul_mem hh (schreierGroup.inv_mem (schreierT_mem_group _)), prevT i, ?_⟩
      simp [schreierT, nextT_prevT, mul_assoc]

/-- These sixteen explicit transitions generate the entire congruence subgroup. -/
theorem schreierGroup_eq_Gamma0 : schreierGroup = CongruenceSubgroup.Gamma0 7 := by
  apply le_antisymm schreierGroup_le
  intro g hg
  obtain ⟨h, hh, i, rfl⟩ := schreier_decomposition g
  have hi : cosetRep i ∈ CongruenceSubgroup.Gamma0 7 :=
    (CongruenceSubgroup.Gamma0 7).mul_mem_cancel_left (schreierGroup_le hh) |>.mp hg
  obtain rfl := (cosetRep_mem_iff i).mp hi
  simpa [cosetRep] using hh

theorem cosetRep_distinct (i j : Fin 8) :
    cosetRep j * (cosetRep i)⁻¹ ∈ CongruenceSubgroup.Gamma0 7 ↔ i = j := by
  change ((cosetRep j * (cosetRep i)⁻¹) 1 0 : ZMod 7) = 0 ↔ i = j
  fin_cases i <;> fin_cases j <;> decide

def rightCoset (i : Fin 8) :
    Quotient (QuotientGroup.rightRel (CongruenceSubgroup.Gamma0 7)) :=
  Quotient.mk (QuotientGroup.rightRel (CongruenceSubgroup.Gamma0 7)) (cosetRep i)

theorem rightCoset_bijective : Function.Bijective rightCoset := by
  constructor
  · intro i j hij
    exact (cosetRep_distinct i j).mp (QuotientGroup.rightRel_apply.mp (Quotient.exact hij))
  · intro q
    induction q using Quotient.inductionOn with
    | h g =>
      obtain ⟨h, hh, i, rfl⟩ := schreier_decomposition g
      refine ⟨i, Quotient.sound ?_⟩
      apply QuotientGroup.rightRel_apply.mpr
      simpa [mul_assoc] using schreierGroup_le hh

/-- Exact index eight, not just a finite-index instance. -/
theorem Gamma0_seven_index : (CongruenceSubgroup.Gamma0 7).index = 8 := by
  change Nat.card (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 7) = 8
  let e := (Equiv.ofBijective rightCoset rightCoset_bijective).trans
    (QuotientGroup.quotientRightRelEquivQuotientLeftRel (CongruenceSubgroup.Gamma0 7))
  simpa using (Nat.card_congr e).symm

end Zeta7LevelSeven

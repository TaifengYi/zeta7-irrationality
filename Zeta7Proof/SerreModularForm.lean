/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.NumberTheory.ModularForms.LevelOne.Basic
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Topology.UniformSpace.UniformConvergence

/-! Minimal adaptation of ANR-FALSE/PadicModForms, commit
f463dbbae6d24e08538ebe49b86718f094c5026a, Rational/Basic and PAdic/Defs.
Rational forms are q-expansions of actual LEVEL-ONE complex modular forms.
The rational q-expansion map is directly the subtype's linear inclusion,
which has exactly the upstream `rationalQExpansion_apply` behavior.
No theorem from PAdic/Basic is imported. -/

set_option autoImplicit false
noncomputable section
open PowerSeries Filter Topology UpperHalfPlane
open scoped MatrixGroups

namespace PowerSeries

def isModularForm (k : ℤ) (f : ℚ⟦X⟧) : Prop :=
  ∃ g : ModularForm 𝒮ℒ k, qExpansion 1 g = f.map (algebraMap ℚ ℂ)

theorem zero_isModularForm (k : ℤ) : isModularForm k 0 :=
  ⟨0, by simpa using qExpansion_zero 1⟩

theorem IsModularForm.smul {k : ℤ} {f : ℚ⟦X⟧}
    (hf : f.isModularForm k) (a : ℚ) : (a • f).isModularForm k := by
  obtain ⟨F, hF⟩ := hf
  exact ⟨(a : ℂ) • F, by
    simp [ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL,
      hF, smul_eq_C_mul]⟩

theorem IsModularForm.add {k : ℤ} {f g : ℚ⟦X⟧}
    (hf : f.isModularForm k) (hg : g.isModularForm k) : (f + g).isModularForm k := by
  obtain ⟨F, hF⟩ := hf
  obtain ⟨G, hG⟩ := hg
  exact ⟨F + G, by
    simp [ModularForm.qExpansion_add one_pos one_mem_strictPeriods_SL, hF, hG]⟩

def _root_.rationalModularForms (k : ℤ) : Submodule ℚ ℚ⟦X⟧ where
  carrier := {f | f.isModularForm k}
  zero_mem' := zero_isModularForm k
  add_mem' := IsModularForm.add
  smul_mem' a _ hf := IsModularForm.smul hf a

end PowerSeries

namespace ModularForm
def rationalQExpansion {k : ℤ} : rationalModularForms k →ₗ[ℚ] ℚ⟦X⟧ :=
  (rationalModularForms k).subtype

@[simp] theorem rationalQExpansion_apply {k : ℤ} (f : rationalModularForms k) :
    rationalQExpansion f = (f : ℚ⟦X⟧) := rfl
end ModularForm

variable {p : ℕ} [Fact p.Prime]

/-- A Serre presentation, with convergence of every coefficient UNIFORMLY. -/
structure pAdicModularFormStruct (f : ℚ_[p]⟦X⟧) where
  w : ℕ → ℤ
  F : (i : ℕ) → rationalModularForms (w i)
  tendsTo : TendstoUniformly
    (fun i n => ((coeff n (ModularForm.rationalQExpansion (F i)) : ℚ) : ℚ_[p]))
    (coeff · f) atTop

def PowerSeries.isPAdicModularForm (p : ℕ) [Fact p.Prime] (f : ℚ_[p]⟦X⟧) : Prop :=
  Nonempty (pAdicModularFormStruct f)

import Zeta7Proof
import Stage2Operator
import Zeta7Proof.KubotaLeopoldt
import Zeta7Proof.EisensteinLimit
import Zeta7Proof.SerreEisenstein

/-!
# Master entry point: `ζ₇(3)` is irrational

The project proves, with a fully internal and kernel-checked Lean proof,

  theorem zeta7Three_irrational : ¬ Zeta7Partial.IsRationalSeven zeta7Three
  theorem eta_irrational : ¬ Zeta7Partial.IsRationalSeven eta

(`Zeta7Proof/FinalTheorem.lean`). `#print axioms` for both reports exactly
`[propext, Classical.choice, Quot.sound]`; `Zeta7Proof/FinalInternalAudit.lean` checks this
mechanically, together with the absence of any project axiom in the import closure.

`Zeta7Main.zeta7Three` is a genuine measure-theoretic construction of the Kubota–Leopoldt value:
branch 4 at `s = 3`, whose weight character is `a ↦ a^(-2)`, i.e. `ζ₇(3) = L₇(3, ω^{-2})`.
`bernoulli_approximants_tendsto_zeta7Three` proves that it is the `7`-adic limit of
`-(1 - 7^(w_n - 1)) · B_(w_n) / w_n` with `w_n = 6 · 7^(n+1) - 2`, which is the classical
definition (see `INFORMAL_RESULT.md`).

`IrrationalityClaim` below is the exact target proposition. `irrationalityClaim_holds` proves it.
The historical `Zeta7Partial.conditional_exclusion` is printed for the record only; it is not
applied.
-/

set_option autoImplicit false

namespace Zeta7Main

open Zeta7Partial

/-- The exact target proposition: `ζ₇(3)` is not in the image of `ℚ`. -/
def IrrationalityClaim : Prop := ¬ IsRationalSeven zeta7Three

/-- **The target proposition holds** (`Zeta7Main.zeta7Three_irrational`). -/
theorem irrationalityClaim_holds : IrrationalityClaim := zeta7Three_irrational
/-- The rational cast is exactly the canonical field embedding. -/
theorem rational_cast_eq_algebraMap (q : ℚ) :
    (q : ℚ_[7]) = algebraMap ℚ ℚ_[7] q := by
  simp

/-- Thus distinct rational numbers remain distinct in the seven-adic field. -/
theorem rational_embedding_injective :
    Function.Injective (algebraMap ℚ ℚ_[7]) :=
  (algebraMap ℚ ℚ_[7]).injective

/-- This is image membership, not a statement about finite seven-adic digits. -/
theorem isRationalSeven_iff_mem_range (z : ℚ_[7]) :
    IsRationalSeven z ↔ z ∈ Set.range (algebraMap ℚ ℚ_[7]) := by
  simp [IsRationalSeven, Set.mem_range]

theorem isRationalSeven_ratCast (q : ℚ) :
    IsRationalSeven (q : ℚ_[7]) := ⟨q, rfl⟩

#print axioms rational_cast_eq_algebraMap
#print axioms rational_embedding_injective
#print axioms isRationalSeven_iff_mem_range
#print axioms isRationalSeven_ratCast
#print axioms IrrationalityClaim
#print axioms irrationalityClaim_holds
#print axioms zeta7Three_irrational
#print axioms eta_irrational
#print axioms zeta7Three
#print axioms bernoulli_approximants_tendsto_zeta7Three
#print Zeta7Partial.conditional_exclusion
#print axioms Zeta7Partial.conditional_exclusion

end Zeta7Main

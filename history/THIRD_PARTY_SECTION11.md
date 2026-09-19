> **HISTORICAL RECORD** (written before 19 September 2026). The ζ₇(3) irrationality theorem is now proved in Lean with a fully internal proof whose endpoints depend only on `propext`, `Classical.choice` and `Quot.sound`; see `README.md` and `FULLY_INTERNAL_COMPLETION.md` at the repository root. Status statements below are historical and have not been rewritten.

# Section 1.1 source attribution

`Zeta7Proof/ClassicalEulerTransport.lean` adapts Riccardo Brasca's 2026
`PadicModForms/ForMathlib/QExpansionDeriv.lean` from the already-present
ANR-FALSE archive (`f463dbb`). The archived source is
`reference/anr_false/source/ANR-FALSE-PadicModForms-f463dbb/PadicModForms/ForMathlib/QExpansionDeriv.lean.txt`.
Its Apache-2.0 copyright notice is preserved in the adapted file.
The license text is included at `licenses/Apache-2.0-Section11.txt`.

The adaptation replaces the archive's `PowerSeries.Θ` dependency with
`Zeta7Common.euler`, uses local names, and checks the proofs against this
project's unchanged Lean/Mathlib revisions. The local proof that the
normalized derivative tends to zero at the cusp is included explicitly.

`ActualEisensteinClassical.lean` also uses the archived `ForMathlib/E2.lean.txt`
as API guidance for applying q-expansion uniqueness through a continuous
map. The periodicity and formal-series identifications are proved locally.
The Ramanujan proofs are constructed from the pinned Mathlib's existing
slash-action theorems and level-one Sturm theorem; the absent
`Mathlib.NumberTheory.ModularForms.RamanujanFormula` is not imported.

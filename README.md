# ζ₇(3) is irrational: a Lean 4 formalization

## Result

**Theorem.** The 7-adic zeta value ζ₇(3) is irrational: ζ₇(3) ∉ ℚ.

Here ζ₇(3) = L₇(3, ω⁻²) is the Kubota–Leopoldt value, i.e.

  ζ₇(3) = lim_{n→∞} −(1 − 7^{w_n − 1}) · B_{w_n} / w_n  in ℚ₇,  with w_n = 6·7^{n+1} − 2.

The same holds for η = ζ₇(3)/2.

In Lean:

```lean
theorem Zeta7Main.zeta7Three_irrational : ¬ Zeta7Partial.IsRationalSeven Zeta7Main.zeta7Three
theorem Zeta7Main.eta_irrational        : ¬ Zeta7Partial.IsRationalSeven Zeta7Main.eta
```

`Challenge.lean` states the result using Mathlib alone (namespace `Zeta7Challenge`). `Solution.lean` proves it from the theorems above.

## Formal status

The Lean proof is complete and fully internal. The geometric continuation of the target series to radius 49 was originally an external input; it is now proved in Lean (`Zeta7Main.internal_radius49_geometric_continuation`).

The mathematical argument has not been refereed.

## Verification

```text
#print axioms Zeta7Main.zeta7Three_irrational
  [propext, Classical.choice, Quot.sound]
#print axioms Zeta7Main.eta_irrational
  [propext, Classical.choice, Quot.sound]
```

These are Lean's three standard axioms. The dependency graph contains no `sorry`, `admit`, `native_decide` or project axiom. This is checked mechanically by:
- `Zeta7Proof/FinalInternalAudit.lean` (final endpoints, no project axiom in the import closure);
- `Zeta7Proof/Radius49CompleteAudit.lean` (the radius layer, and that it does not depend on the final theorems).

## Build

- **Lean:** `leanprover/lean4:v4.34.0-rc2`.
- **Mathlib:** `v4.34.0-rc2`, commit `85e3a25e006c35636f0e53b0e9296caca2685bc0`, pinned in `lake-manifest.json`.

```sh
lake exe cache get   # optional: download prebuilt Mathlib
lake build           # builds the whole development, the audits, Challenge and Solution
```

## Contents

| Path | Contents |
|---|---|
| `Challenge.lean`, `Solution.lean`, `comparator.json`, `formalization.yaml` | Palomar-format statement, proof bridge, Comparator configuration and metadata |
| `Zeta7Proof/` | The development. The final theorem is in `Zeta7Proof/FinalTheorem.lean`, and the internal radius-49 proof is in the `Radius49*.lean` modules. |
| `PadicLFunctions/`, `LeanModularForms/` | Adapted third-party Lean code (Apache-2.0, original notices kept) |
| `palomar_local_check/` | Local check scripts: a Comparator-style declaration-closure comparison, and a metadata validator |
| `history/` | Historical records from earlier stages (see `history/README.md`) |

## Informal explanation

[INFORMAL_RESULT.md](INFORMAL_RESULT.md) covers:
- the precise statement and the normalization of ζ₇(3);
- the proof architecture;
- the internal radius-49 theorem;
- the axiom status;
- reproducibility;
- the literature context.

## Provenance

This is a human-directed research project with extensive AI assistance (GPT-6 Astra and Claude Code) in both the mathematics and the Lean engineering. It is neither an autonomous AI proof nor a purely manual formalization. See [PROVENANCE.md](PROVENANCE.md).

## Licence

Apache-2.0 (see `LICENSE`). Files adapted from other projects keep their original copyright notices.

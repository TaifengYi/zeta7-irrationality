# ζ₇(3) formalization: fully internal completion (19 September 2026)

The final irrationality endpoints use only Lean's three foundational axioms. The published radius-49 axiom has been removed from the final proof graph; its statement is now proved inside Lean.

## Environment

- **Lean:** `leanprover/lean4:v4.34.0-rc2`
- **Mathlib:** `v4.34.0-rc2`, commit `85e3a25e006c35636f0e53b0e9296caca2685bc0`
- **Lock file:** `lake-manifest.json`, SHA-256 `d04b8db1d7c5f071c137e61788a0753e0473b5c9a0e39d6dabd35159c1e48fc5`

## Build

- **Command:** `lake build`, with default targets `Zeta7Proof`, `Zeta7Main` and `Zeta7AxiomAudit`.
- **Result:** exit 0, "Build completed successfully (9150 jobs)", wall time 65 min.
- **Scope:** every new or modified module was recompiled.
- **Historical audits outside the default targets:** these were also compiled and pass: `Radius49PublishedGeometryAudit`, `ModularProgressAudit`, `N123IndependenceAudit`, `N123ProgressAudit`, `N4CompletionAudit`, `N4ProgressAudit`, `Section11LHAudit`, `Section11ProgressAudit`, `AnnularIntegralSourceAudit`, `SixGermRadiusAudit`.

## Endpoint axiom sets

Each endpoint below uses exactly `[propext, Classical.choice, Quot.sound]`. This is checked mechanically by `Zeta7Proof/FinalInternalAudit.lean`.

**Final irrationality endpoints**

| Theorem | Statement |
|---|---|
| `Zeta7Main.zeta7Three_irrational` | `¬ Zeta7Partial.IsRationalSeven zeta7Three` |
| `Zeta7Main.eta_irrational` | `¬ Zeta7Partial.IsRationalSeven eta` |

**Radius-49 layer**

| Theorem | Role |
|---|---|
| `Zeta7Radius49.twistMatrix_bound` | HM |
| `Zeta7Radius49.initial_HSeries_overconvergent` | HO |
| `Zeta7Main.internal_radius49_geometric_continuation` | `HasRadius49GeometricContinuation` |
| `Zeta7Main.HSeries_radius49` | coefficient decay below radius 49 |

**Earlier endpoints (not reopened)**

| Theorem | Role |
|---|---|
| `Zeta7Main.c_theorem_explicit` | C theorem with the explicit constants J and I |
| `Zeta7Cert.surplusS_gt` | kernel-checked surplus margin, S > 223/6250 |
| `Zeta7Valence.energyI_le_explicitI` | Archimedean energy bound |

## Audit results

These audits run in the full build:

| Audit | Result |
|---|---|
| `FinalInternalAudit` | PASSED: 9 endpoints; 10903 project declarations in the import closure, none an axiom; the archived axiom is absent from the environment. |
| `Radius49CompleteAudit` | PASSED: 1639 declarations of the radius modules use only the three axioms. The radius import closure excludes `FinalTheorem`, `FinalConditional`, `ArchCTheorem`, `ArchC30` and `PublishedRadius49GeometricInput`, so the proof is not circular. |
| `FinalAudit` | PASSED: 579 declarations. |

`FinalAudit` has been tightened: it no longer admits the radius axiom anywhere.

**Source hygiene.** The final closure contains 375 project modules. None contains `sorry`, `admit`, `native_decide`, `ofReduceBool`, `axiom`, `opaque`, `unsafe`, `implemented_by` or `extern` declarations.

## Radius assembly

`Zeta7Proof/Radius49Internal.lean` contains:

```lean
theorem internal_radius49_geometric_continuation : HasRadius49GeometricContinuation :=
  hasRadius49_of_matrix_bound_and_initial twistMatrix_bound initial_HSeries_overconvergent
```

`HSeries_radius49` and the endpoints that follow from it now use this internal theorem:
- `HSeries_isRestricted`
- `normalisedHSeries_radius1`
- `normalisedHSeries_isRestricted`
- `normalisedHSeries_summable_on_closedDisc`
- `HSeries_equation12`
- `normalisedHSeries_epsilon_norm_bound`
- `HSeries_epsilon_valuation_bound`
- `oppositeH_decaysOn_published`

These were previously in `Radius49FromPublishedGeometry` and were moved to `Radius49Internal`. Downstream modules, including `RetainedRadiusJets`, now import `Radius49Internal`.

## New internal-radius modules

All are under `Zeta7Proof/`:
- `Radius49Coordinate`
- `Radius49Bootstrap`
- `Radius49Twisted`
- `Radius49U7Data`
- `Radius49U7Analytic`
- `Radius49U7Formal`
- `Radius49U7PowerSums`
- `Radius49U7Psi`
- `Radius49U7Jacobian`
- `Radius49U7Norm`
- `Radius49HM`
- `Radius49HONear`
- `Radius49HOFricke`
- `Radius49HOGen`
- `Radius49HOAlg`
- `Radius49HOBnd`
- `Radius49HOChain`
- `Radius49GeometryCore`
- `Radius49Internal`

**Audits:** `Radius49InternalAudit`, `Radius49CompleteAudit`, `FinalInternalAudit`.

## Retained file excluded from the final graph

`Zeta7Proof/PublishedRadius49GeometricInput.lean` is now an archival module. It holds only the obsolete `axiom published_radius49_geometric_continuation`, stated over `Radius49GeometryCore`.

No module of the default build imports it. `FinalInternalAudit` checks this. The module still compiles on its own.

The axiom-free definitions it used to contain are now in `Radius49GeometryCore`: `DiscAlgebra`, `discSeries`, `discSeries_decay` and `HasRadius49GeometricContinuation`.

## Checkpoint

See the final section, which is appended after the checkpoint is created.

## Final checkpoint

| Field | Value |
|---|---|
| Path | `checkpoints/Zeta7_radius_FULLY_INTERNAL_20260919_161042.zip` |
| SHA-256 | `aad146be430a3509c55dc982885025d984c8b4e20eda2835eac30e4b111da5f4` |
| Entries | 1796 |

Each entry was verified against the working tree by `RADIUS_CHECKPOINT.ps1`. The ZIP contains every entry of the earlier frozen checkpoint. This section was appended after the ZIP was created, so the copy of this note inside the ZIP does not include it.

Earlier checkpoints are unchanged. They include `Zeta7_radius_HO_20260919_115803.zip` and `Zeta7_radius_rewired_20260919_144527.zip` (SHA-256 `d201c21b…715f466`).

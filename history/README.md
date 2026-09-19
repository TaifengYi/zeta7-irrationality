# Historical records

**Everything in this directory is historical.** These files document earlier stages of the project and are kept for transparency about how the result was obtained. They do not describe the current state.

The current state is:
- `Zeta7Main.zeta7Three_irrational` and `Zeta7Main.eta_irrational` are proved in Lean;
- they depend only on `propext`, `Classical.choice` and `Quot.sound`;
- the radius-49 continuation is proved internally.

See the repository root: `README.md`, `INFORMAL_RESULT.md`, `PROVENANCE.md` and `FULLY_INTERNAL_COMPLETION.md`.

Statements below such as "does not yet prove", "remains open" or "relative to the published radius input" were accurate on the dates the files were written. They have not been rewritten.

| File | What it records |
|---|---|
| `manuscript/Zeta7_Proposed_Unconditional_Proof.tex` | The project manuscript *A determinant argument for the irrationality of ζ₇(3)* (15 September 2026), unchanged. Its "Research status" paragraph predates the completed Lean proof. The manuscript cites published results for the radius-49 continuation; the Lean proof replaces those citations with an internal proof. |
| `PublishedRadius49GeometricInput.lean.txt` | The retired axiom `published_radius49_geometric_continuation`, used by earlier stages as an explicit external input. It is renamed to `.txt` so that it is not part of the Lean build. No module of the release declares or uses it. |
| `KL_CONSTRUCTION_PROVENANCE.md`, `EISENSTEIN_PROVENANCE.md`, `UNIFORM_PROVENANCE.md`, `THIRD_PARTY_SECTION11.md` | Source, version and licence records for the adapted third-party Lean code (Birkbeck, Brasca/ANR-FALSE) and for the Kubota–Leopoldt construction. The attribution content remains accurate. Their status remarks are historical. |
| `FINAL_RELATIVE_RADIUS_CHECKPOINT.md` | The state on 18 September 2026, when the irrationality theorem was proved relative to the radius axiom only. |
| `ZETA7_MASTER_LEDGER.md` | The master ledger kept during development. |

Paths of the form `reference/...` and `licenses/...` inside these records refer to the development workspace archive, not to this repository. The Apache-2.0 licence text covering the adapted code is the root `LICENSE`.

The full development workspace, with all stage ledgers, build logs and verified checkpoint archives, is preserved by the author. The final proof checkpoint is `Zeta7_radius_FULLY_INTERNAL_20260919_161042.zip`, SHA-256 `aad146be430a3509c55dc982885025d984c8b4e20eda2835eac30e4b111da5f4`.

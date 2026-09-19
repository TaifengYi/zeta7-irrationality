# Provenance: how this result was obtained

## Summary

This project was developed through substantial human–AI collaboration. GPT-6 Astra and Claude Code were used extensively for the following:
- mathematical exploration and proof development;
- Lean implementation, debugging and refactoring;
- computational experimentation and certificate generation;
- proof-audit work.

The human author:
- selected the research target;
- provided detailed mathematical direction;
- imposed the proof and verification standards;
- decomposed the project into intermediate goals;
- repeatedly redirected proposed approaches, and supplied guidance and source material;
- supervised the elimination of conditional assumptions;
- performed final validation

The result should therefore be described neither as an autonomous AI proof nor as a purely manually coded formalization. It is a human-directed research project with extensive AI assistance in both mathematical reasoning and formal proof engineering.

## Human contribution

The human author is Yi Taifeng, as named on the project manuscript.

- **Choice of problem.** The author chose the irrationality of the Kubota–Leopoldt value ζ₇(3) as the target. This is a case that the literature describes as open (see `INFORMAL_RESULT.md`, §7). 
- **Mathematical direction and architecture.** The author directed the decomposition into these components:
  - the target series and its differential equation;
  - seven-germ independence and the zero estimate (N);
  - the seven-adic annular saving (A);
  - the auxiliary-prime estimate (P);
  - the Archimedean energy estimate (C);
  - the explicit numerical margin;
  - the radius-49 continuation.

  
- **Rigor requirements.** The author set and enforced a strict verification standard:
  - no `sorry`, `admit`, `native_decide`, `Lean.ofReduceBool` or custom axiom;
  - no literature theorem smuggled in as a hypothesis;
  - finite numerical experiments are not accepted as proof unless a theorem converts them into equalities or inequalities;
  - final endpoints must depend only on `propext`, `Classical.choice` and `Quot.sound`.
- **Identifying unacceptable dependencies.** For much of the project the radius-49 continuation was an explicit external axiom (`published_radius49_geometric_continuation`) backed by published results of Calegari, Buzzard and Loeffler. The author identified it as an unacceptable conditional dependency and required its internal proof. The author then directed that proof's structure:
  - the matrix bound HM and initial overconvergence HO as the two remaining propositions;
  - the proof of HO by classical approximants in the weight-space component of −2, after an explicit check that U₇-fixedness alone cannot pin down the constant term.
- **Iterative steering.** Across many sessions the author:
  - issued phase plans and priority orders;
  - supplied source material: the Kubota–Leopoldt formalization, Eisenstein-family files, papers, and pointers to external Lean repositories to audit before building new infrastructure;
  - rejected approaches that were circular, conditional or unverifiable;
  - required frequent verified checkpoints;
  - required that solved components be frozen rather than reopened.
- **Validation and acceptance.** The author reviewed the audit outputs and accepted the final state: the fully internal proof, the axiom audits and the verified checkpoints.

## AI contribution

**Systems.** GPT-6 Astra and Claude Code (Anthropic).
- The Claude Code sessions that completed the proof ran on Claude Opus 5. These sessions covered the internal radius-49 proof (HM, HO), the removal of the radius axiom, and the final audits and packaging.
- The repository does not record the model versions of earlier sessions individually.
- The Kubota–Leopoldt construction and the Eisenstein-family files were adapted from human-written open-source formalizations (Birkbeck; Brasca's ANR-FALSE). See `KL_CONSTRUCTION_PROVENANCE.md`, `EISENSTEIN_PROVENANCE.md` and `UNIFORM_PROVENANCE.md` in the development workspace (retained under `history/` in the release).

AI systems contributed substantially, under the direction described above, to:
- **Literature exploration.** Locating and reading the relevant papers and existing Lean formalizations, and auditing external repositories for reusable infrastructure.
- **Mathematical derivations.** Working out proof steps, among them:
  - the level-one trace computation, the modular equation Ψ and the Newton recurrence for U₇ (HM);
  - the Jacobian formula and valuation bounds for the twisted operator;
  - the classical-approximant chain argument for initial overconvergence (HO);
  - details of the annular, auxiliary-prime and Archimedean estimates.
- **Lean proof development.** Writing essentially all of the project-specific Lean source, apart from the adapted third-party files listed below. This included proof search, tactic engineering, debugging and refactoring. The final import closure contains about 10,900 project declarations, including the adapted libraries.
- **Symbolic computation and certificates.** Computing explicit polynomials and coefficient data, and generating the certificates that Lean then checks (`ring`, `norm_num`, kernel `decide` and interval arithmetic), such as the surplus bound S > 223/6250.
- **Audits and automation.** Writing the axiom and non-circularity audits (`FinalInternalAudit`, `Radius49CompleteAudit`, and earlier stage audits), checkpoint scripts, and the local Comparator surrogate in `palomar_local_check/`.
- **Documentation.** Drafting the ledgers, this file, `INFORMAL_RESULT.md` and the Palomar metadata, all under the author's review.

## Verification boundary

Any piece of proof text was produced, the mathematical claims are established by the Lean kernel. At the final checkpoint:

```text
#print axioms Zeta7Main.zeta7Three_irrational  →  [propext, Classical.choice, Quot.sound]
#print axioms Zeta7Main.eta_irrational         →  [propext, Classical.choice, Quot.sound]
```

The final import closure contains no project axiom, no `sorry`, no `admit`, no `native_decide` and no `Lean.ofReduceBool`. The audit modules check this mechanically. Kernel checking does not by itself certify that the definitions mean what they are intended to mean. For that reason:
- `Challenge.lean` states the result with Mathlib-only definitions;
- it proves that the defining sequence converges;
- `INFORMAL_RESULT.md` explains the normalization.

The mathematical argument has not been independently refereed or published.

## No authorship inflation

- The human author did not write most of the Lean code or most of the detailed derivations line by line. Their contribution was direction, architecture, standards, supervision and acceptance, as described above.
- The AI systems did not select the problem or set the standards, and did not act autonomously. They worked within a plan set by the author and under sustained redirection.
- Credit for reused formal libraries (Mathlib; Birkbeck's p-adic L-functions and LeanModularForms; Brasca's ANR-FALSE p-adic modular forms) is recorded in the source files, which keep the original copyright notices, and in `formalization.yaml`.

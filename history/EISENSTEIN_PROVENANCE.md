> **HISTORICAL RECORD** (written before 19 September 2026). The ζ₇(3) irrationality theorem is now proved in Lean with a fully internal proof whose endpoints depend only on `propext`, `Classical.choice` and `Quot.sound`; see `README.md` and `FULLY_INTERNAL_COMPLETION.md` at the repository root. Status statements below are historical and have not been rewritten.

# Eisenstein sources and compatibility boundary

Uniform-milestone update: `rjw_normalisation` in the active complex file is now
public, with its statement and proof unchanged. This is the only further edit
to that file. The byte-for-byte descriptions below concern the preserved
specialization checkpoint. See [UNIFORM_PROVENANCE.md](UNIFORM_PROVENANCE.md).

User-supplied files received 2026-09-14, with no embedded version identifier:

| File | Exact supplied SHA-256 | Archived bytes |
|---|---|---|
| EisensteinFamily.lean | `644ed6a45bae405798782a75c6ee82cdaf1b203a860c230f9404ea9ad291056a` | reference/revision_20260914/EisensteinFamily.attached.lean.txt |
| EisensteinComplex.lean | `64b67f0b7abe4187b0c911bbfcedbb4f0a1172df15ceb4695030c76fc1e1a226` | reference/revision_20260914/EisensteinComplex.attached.lean.txt |

These differ from the earlier archived CBirkbeck commit
45307015169791f1316f23a459c8e92ed5961c54. The attached family simplifies proofs,
adds `unitsCmul_dirac`, and fixes the cast in the halving lemma. The attached
complex file generalizes the level parameter from prime to any positive natural
(`NeZero p`), as appropriate to classical stabilization. Neither supplies a
negative-weight overconvergent-form theorem.

Both complete supplied files were compiled directly from the Downloads paths.
The family passes unchanged. The complex file initially fails at its missing
LeanModularForms import; it passes after installing the audited dependency below.
The raw attempt and resolved compilation outputs are retained as
ATTACHED_FAMILY_RAW_COMPILE.txt, ATTACHED_COMPLEX_RAW_COMPILE.txt and
ATTACHED_COMPLEX_RESOLVED_COMPILE.txt.

The active family is the supplied file with exactly two private lemmas exposed:
`coe_inv_two` and `twistedZetaHalf_witness_eq`. Their proofs and statements are
unchanged. This permits using the actual canonical numerator in the target
specialization. The active complex file is byte-for-byte the supplied file.
Both retain Chris Birkbeck's copyright and Apache 2.0 license notices.

## Minimal level-raising dependency

Source: CBirkbeck/LeanModularForms, commit
`512911ce1a936ac9054415c5c72701fbd5cd5ae5`, the exact revision pinned by the
archived p-adic L-functions project. Downloaded source:
reference/lean_modular_forms/LevelRaise.lean.txt. We also inspected its
LevelEmbed and Gamma1Pair imports; no statement from those files is assumed.

Original LevelRaise SHA-256:
`c4e3324eda7bdfe1b49478390b481414e139a91c6417beab6879a08bce98b7d8`.
Adapted LevelRaise SHA-256:
`ca6b6bf20fe2737255e5262900c039dc00d92f8ae10e4f2e68f6994ae4859e81`.
Adapted family SHA-256:
`fb1f99072019429ddb8cb879001444746df2ce1b90a7b46f8609bc551667ba43`.

The active LeanModularForms/HeckeRIngs/GL2/LevelRaise.lean contains the complete
initial construction through `modularFormLevelRaise_apply`, followed by namespace
closure. The unrelated later cusp-form composition, matrix factorization and
q-expansion lemmas are not imported. No declaration in either supplied Eisenstein
file is removed. The level-raising import of LevelEmbed is replaced by mathlib's
Cusps module: this initial segment does not use any LevelEmbed theorem.

One proof is adapted to the pinned mathlib coercion API:
`levelRaiseMatrix_mul_mapGL` uses an explicit entrywise rational-to-real matrix
cast lemma (proved by reflexivity) before the same four-entry calculation.
All theorem statements in the retained segment are unchanged. No project pin or
mathlib source is changed. File hashes and exact adaptation diffs are recorded
in EISENSTEIN_PORT_HASHES.csv and EISENSTEIN_PORT_DIFF.txt.

## Mathematical scope and explicit hypotheses

`eisensteinFamily_interpolation`: arbitrary prime p, p != 2, natural k >= 4.
The constant clause quantifies over a numerator satisfying a localized witness
equation. That equation is a mathematical premise, not a kernel axiom. The
project target bridge supplies its canonical numerator and proves the equation;
it does not leave this premise open. The positive clauses evaluate finite
divisor measures. Oddness of k is allowed on this algebraic side; classical
modular-form identification uses even k.

`hasSum_stabilisedEisenstein`: positive level p, even natural k >= 4, z in the
upper half-plane. No unproved summability or q-expansion hypothesis. Its limit
is the actual classical difference E_k(z)-p^(k-1)E_k(pz), with E_k normalized to
constant zeta(1-k)/2. `stabilisedEisenstein` is a genuine classical modular form
on Gamma0(p); `stabilisedEisenstein_smul_apply` checks its scaling. These are
classical positive-weight theorems, not a construction of rigid analytic
negative-weight forms.

The twist is essential: A_0=(x*zeta_p)/2 has its pole at the inverse character,
not the trivial character. Its regularizing factor is g*[g]-1. At weight -2,
the family is tested against x^-3, so its constant pairs zeta_p against x^-2.
The project explicitly proves this character shift and that its denominator is
nonzero, reusing the preserved branch-4 value. No extra Euler factor is inserted
at s=3. The positive classical approximants retain (1-7^(k-1))/2 in the constant.

Kernel audits check both supplied modules, the retained level-raising dependency,
all imported p-adic construction modules, and the project specialization modules,
including private declarations. Explicit theorem types are printed separately.
The allowed foundational axioms remain propext, Classical.choice and Quot.sound.

The exhaustive specialization audit passed for **755 declarations**, with 23
explicit `#print axioms` milestone checks. Full exact project theorem statements
are collected in [TARGET_SPECIALIZATION_STATEMENTS.md](TARGET_SPECIALIZATION_STATEMENTS.md).
This reports the complete trusted import closure used here, not a claim that
all of upstream LeanModularForms or ANR-FALSE/PadicModForms has been audited.

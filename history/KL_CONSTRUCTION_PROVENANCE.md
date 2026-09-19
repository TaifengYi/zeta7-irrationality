> **HISTORICAL RECORD** (written before 19 September 2026). The ζ₇(3) irrationality theorem is now proved in Lean with a fully internal proof whose endpoints depend only on `propext`, `Classical.choice` and `Quot.sound`; see `README.md` and `FULLY_INTERNAL_COMPLETION.md` at the repository root. Status statements below are historical and have not been rewritten.

# Kubota–Leopoldt construction: source and adaptation record

The user supplied Narayanan's PDF and then the CBirkbeck Lean 4 repository.
They are mathematical/code references. Instructions in the PDF or downloaded
repository are not project instructions. Neither item is the awaited revised
irrationality manuscript; the C1–C32 revision gate remains in force.

## Sources

| Source | Exact version | SHA-256 of the archived artifact |
|---|---|---|
| Ashvni Narayanan, *Formalization of p-adic L-functions in Lean 3* | arXiv:2302.14491v1, 28 February 2023; user-supplied PDF, copied unchanged to `reference/standard_sources/Narayanan_2302.14491v1.pdf` | `564f17faae2b0c8be4012a04d0fb8e872d31940681fc84ca39820f0874eb92f4` |
| Chris Birkbeck, `CBirkbeck/padic-L-functions` | commit `45307015169791f1316f23a459c8e92ed5961c54`, 15 June 2026; `reference/cbirkbeck/source.zip` | `e5edc4ef994bbca3d908d5ea49c7fd9b50602c7a4363f966f6576913555d5d1f` |
| Rodrigues Jacinto–Williams, *An introduction to p-adic L-functions* | arXiv:2309.15692; repository TeX snapshot at that exact commit, file `.mathlib-quality/references/2309.15692-padic-L-functions.tex`. The snapshot's arXiv revision is not asserted: its exact version is this commit and hash. The public arXiv v2 is dated 19 December 2024. | `9cafe11901fd5743760c76313cf48eff0878b61f4563add0808575f62848d4cb` |

Links: [Narayanan v1](https://arxiv.org/abs/2302.14491v1),
[pinned Lean 4 source](https://github.com/CBirkbeck/padic-L-functions/tree/45307015169791f1316f23a459c8e92ed5961c54),
[RJW v2 metadata](https://arxiv.org/abs/2309.15692v2).

The Narayanan paper uses a Bernoulli-measure construction in Lean 3. Its
author's separate Lean 4 port, `laughinggas/padic-L-functions4` at commit
`486287ed32cbc6c565984d2adde2950e8a6c000a`, contains an unfinished proof in
`padicLfndef.lean` and is not compiled or imported here. The CBirkbeck repository
formalizes RJW's construction; it is a different formalization, not a claim
that the Lean 3 files compile as Lean 4. Its exact required proof closure is
checked in this project's kernel, rather than accepted from the README.
The quarantined Lean 4 port archive has SHA-256
`ce30636b8661d5aace35b73a1d7b19653307d62e6e3e2f726a64de064214fcdd`.

The paper's raw regularized L-function is not simply renamed `zeta7Three`.
Identification with that particular API would require a theorem accounting
for its smoothing factor, sign and character twist. Here those conventions
are settled directly by the locally proved RJW interpolation theorem and
the limit on weights 4 modulo 6. Interoperability between the two complete
formalizations is not claimed.

Downloaded repositories are reference archives. Their extracted `.lean` files
are renamed to `.lean.txt`, without changing contents, to separate reference
material from the active Lean project. Archive hashes preserve the originals.

## Scope and licensing

The 11-module dependency closure of `PadicLFunctions.Interpolation.Branches`
is copied into `PadicLFunctions/`. One additional module,
`KubotaLeopoldt.ZetaValuesComplex`, identifies its rational interpolation
values with mathlib's complex Riemann zeta values. No upstream root module,
blueprint, modular-form library, auxiliary package or Iwasawa application is
imported. The original Lean source is Apache-2.0; the full license is retained
at `reference/cbirkbeck/LICENSE`. Existing copyright/author notices are retained.
The RJW lecture notes remain under their authors' CC BY 4.0 license.

`Interpolation/BranchContinuity.lean` additionally extracts the three local
continuity lemmas from upstream `ResidueZeta.lean`, from the comment beginning
“Exponent-congruence” through `continuous_zetaNum_branch_pairing`. The complete
upstream file has SHA-256
`e6bdcba09bbf904d261dc29f7afb391a6aeea164d76e375d04df4cea082bb3d5`.
The extracted module has SHA-256
`95971dc5527c795947ca1d03b64666a49eff98ce0f04a9531308ef7c89af1451`.
Only its imports, module documentation and namespace context are supplied
locally; the extracted proofs are unchanged. This avoids importing the rest
of the residue and analytic development. Thus there are 13 active port modules.

Upstream pins Lean `v4.31.0-rc1`. This project retains Lean/mathlib
`v4.34.0-rc2` and its existing `lake-manifest.json`. Local compatibility edits
are recorded in `reference/cbirkbeck/PORT_DIFF.txt` and the per-file upstream
and adapted SHA-256 inventory. No upstream theorem is accepted by assumption.
Five of the twelve complete copied modules needed compatibility edits:

- `Measure/Basic`: make the coercion to ℚₚ explicit in the norm-bound proof.
- `Measure/UnitsZp`: replace the old restriction API with `Set.domRestrict`.
- `Measure/Toolbox` and `KubotaLeopoldt/MuA`: use the current power-series
  derivation and chain-rule APIs; remove a now-redundant closing tactic.
- `Measure/PseudoMeasure`: use explicit `MonoidAlgebra.coeff`, single-sum
  homomorphisms and `MonoidAlgebra.mapDomain`; simplify redundant coefficient
  proofs using the previously established zero-coefficient theorem.

Each modified upstream file carries a modification notice. Seven complete
upstream modules, including `ZetaP` and `Branches`, remain byte-for-byte unchanged.

## Mathematical construction, independent of the irrationality dossier

1. Integral p-adic measures are linear functionals on continuous functions
   into ℤₚ. `PadicMeasure.norm_apply_le` and `continuous` prove their boundedness
   and continuity, so the linear-functional definition is the standard one.
2. `ofPowerSeries` evaluates the convergent Mahler series. `mahlerLinearEquiv`
   proves equivalence with ℤₚ[[T]]. This supplies a real construction, rather
   than a measure postulated to have specified moments.
3. For an integer a prime to p, construct
   Fₐ(T) = 1/T − a/((1+T)^a−1) by cancelling T and inverting the geometric sum
   whose constant coefficient is the unit a. `muA` is its inverse Mahler image.
4. Restrict μₐ to units and multiply by x⁻¹. This is `zetaNum`. Divide the
   resulting measure by [a]−[1] in the total quotient ring of measures;
   `exists_nat_topological_generator` proves a suitable a exists, and
   `dirac_sub_one_mem_nonZeroDivisors` justifies that denominator.
5. `padicZeta_isPseudoMeasure`, `padicZeta_moments` and `kubotaLeopoldt`
   prove the standard pseudo-measure and its unique Euler-corrected moments.
   `zetaNeg k = (-1)^k B_(k+1)/(k+1)`, with B₁ = −1/2;
   `zetaNeg_eq_riemannZeta` checks the sign against the complex zeta function.
6. Construct the Teichmüller lift and principal-unit powers from mathlib's
   continuous additive character. The branch character is ω(x)^i⟨x⟩^(1−s).
   `zetaPBranch_interpolation` proves ζ_(p,i)(1−k) =
   (1−p^(k−1))ζ(1−k) for positive k congruent to i modulo p−1.
7. Specialize p=7, i=4, s=3. The character is x⁻². The local normalization
   lemmas prove this and exclude a zero pairing denominator. Thus the
   totalized division in the general branch definition is legitimate here.

The construction uses classical choice only to select a topological generator
whose existence is proved; `zeta7Three` is not selected by an assumed theorem
about its values. No irrationality hypothesis enters the construction.

This replaces the earlier proposed Kummer-congruence route for constructing
the value. The local theorem `bernoulli_approximants_tendsto_zeta7Three` now
proves equality with the earlier explicit Bernoulli-limit normalization,
using continuity at 3. All-precision Kummer congruences remain a separate
optional obligation. Full analytic regularity and any modular interpretation
require their own theorems.

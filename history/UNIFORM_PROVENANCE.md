> **HISTORICAL RECORD** (written before 19 September 2026). The ζ₇(3) irrationality theorem is now proved in Lean with a fully internal proof whose endpoints depend only on `propext`, `Classical.choice` and `Quot.sound`; see `README.md` and `FULLY_INTERNAL_COMPLETION.md` at the repository root. Status statements below are historical and have not been rewritten.

# Uniform coefficient limit: provenance and definition audit

The only ANR-FALSE revision used is
`f463dbbae6d24e08538ebe49b86718f094c5026a`. The supplied links were inspected
through their already archived exact source bytes, under
`reference/anr_false/source/ANR-FALSE-PadicModForms-f463dbb/`.
No package, Lean version, mathlib version, or dependency pin was upgraded.
Lean remains v4.34.0-rc2; mathlib remains
`85e3a25e006c35636f0e53b0e9296caca2685bc0`.

| Upstream source | SHA-256 of the exact archived bytes | Use |
|---|---|---|
| ForMathlib/PowerSeriesTopology.lean | `5aa9cc1094c5940e780f0c1a50b7285d7c4d07b0a599202daf035cd5c6e9d0c4` | Adapted only the uniform structure and convergence equivalence. |
| PAdic/Defs.lean | `e16789946e3783f53af99b8a3227afee95c7ceadf75d5cb5bb486871b616a0ed` | Adapted the Serre presentation structure and existence predicate. |
| PAdic/Basic.lean | `c25e31e0995d27b766d27dfbe7f93a7e256c2afa3a793709c26bb12b81a0aed3` | Read-only reference. No declaration is imported. Its two unfinished reduction proofs are excluded. |
| Rational/Basic.lean | `fffaa4afc77bb94982fc94272ad651670d912d6c028c3e7da1f804dfe68f08a4` | Minimal rational modular-form predicate, submodule, and inclusion. |
| ForMathlib/Padic.lean | `7aa286693669009c52e03e1c826a63e95c9721b905e983103f5713089fe7a0a0` | Adapted the norm/additive-valuation comparison directly into WithTop Z. |

The repository archive SHA-256 is
`46a8c160ed4040f14f76c61b7c8733a9ef08b34fa59f98f1370831d69ab95588`.
Riccardo Brasca's copyright and Apache 2.0 notices are preserved in adapted
modules; the complete license is at [reference/anr_false/LICENSE](reference/anr_false/LICENSE).
The new estimate module carries the notice because it adapts the valuation
comparison; the weight sequence, congruence, estimates and target-limit proofs
are project additions. [UNIFORM_SOURCE_HASHES.csv](UNIFORM_SOURCE_HASHES.csv)
records the active source hashes.

## Minimal adaptations and compatibility

[UniformPowerSeries.lean](Zeta7Proof/UniformPowerSeries.lean) pulls back the
uniform structure on `UniformFun Nat R` along the coefficient map. Its scope
is `Zeta7UniformTopology`. The equivalence is proved for any ring with a
uniform structure, any index type and any filter. No topological-ring claim
for arbitrary unbounded coefficient sequences is made. The existing formal
products and Lambert sums retain their original coefficientwise topology.

[SerreModularForm.lean](Zeta7Proof/SerreModularForm.lean) preserves the important
upstream definition: a rational modular form is the rational q-expansion of
an actual complex modular form of LEVEL ONE and the specified integral weight.
It is not an arbitrary power series or a level-seven form. The inclusion
`rationalQExpansion` is implemented directly as the submodule inclusion;
`rationalQExpansion_apply` proves the same underlying function as upstream.
The unused graded-ring machinery, weight-space notation, and unrelated
imports are omitted. The Serre structure's uniform-convergence field is
filled by the unconditional theorem in EisensteinUniform, not a premise.

The only change to the supplied active EisensteinComplex.lean is making
`PadicLFunctions.rjw_normalisation` public. Its statement and proof are
unchanged. Chris Birkbeck's copyright and license header are preserved.
This avoids reproving the already verified Bernoulli normalization.
`classicalEisensteinForm_apply` identifies the new modular-form packaging
with the pre-existing `rjwEisenstein` function by reflexivity.

## Exact normalization and weight sequence

`serreWeight r = 6 * 7^r - 2`, for every r >= 0. Weight zero of the sequence
is 4, not an invalid classical weight. Every term is even and at least 4.
The exact shift `serreWeight (r+1) = interpolationWeight r` is proved.
The coordinates in `(ZMod 6) × Z_7` tend to `(4,-2)`; for every seven-adic
unit, the classical characters tend to its inverse square. The coordinate
limit and character comparison have separate named Lean theorems.

The full level-one classical form is `zetaNeg(k-1)/2 • ModularForm.E hk`.
Its rational constant is `zetaNeg(k-1)/2 = zeta(1-k)/2`; every positive
coefficient is the FULL divisor sum `sum_{d|n} d^(k-1)`.
`classicalEisensteinForm_qExpansion` proves this all-degree comparison.
The previous project sequence was seven-stabilized: constant
`(1-7^(k-1))*zetaNeg(k-1)/2`, and sums restricted to 7∤d.

The target remains the independently evaluated `Zeta7Main.eisensteinMinusTwo`:
constant `eta = Zeta7Main.zeta7Three/2`, positive coefficient
`sum_{d|n,7∤d} d^(-3)`. The genuine KL definition, numerator witness,
denominator proof and Bernoulli-limit theorem are preserved unchanged.
The Euler correction tends to zero, its factor is nonzero at every index,
and division by that factor gives the full classical constant limit.
No extra Euler factor is inserted at the target.

## Uniform estimate and mathematical hypotheses

Fermat in the integers followed by the existing proved lifting lemma gives
`7^(r+1) | d^(6*7^r)-1` whenever 7∤d. Casting into Q_7 and cancelling the
nonzero unit cube gives error norm at most `7^(-(r+1))`. For 7|d the norm of
`d^(k-1)` is at most `7^(-(k-1))`, with k-1 >= r+1. The finite ultrametric
sum bound introduces no factor depending on the number of divisors.

The valuation used is `Padic.addValuation : Q_7 -> WithTop Z`; its value at
zero is infinity. `classical_nonconstant_all_precisions` has quantifiers
`forall M : Z, exists R : Nat, forall r >= R, forall n >= 1, ...`.
`classical_all_coefficients_norm` gives a single bound for every coefficient
including degree zero. The uniform convergence, topology-convergence,
constructed presentation and modularity endpoints have NO mathematical
hypotheses and no generic replacement for zeta7Three.

Ordinary helper hypotheses are explicit: r,n are natural indices; the
positive-degree bounds require n != 0; unit/nonunit helpers require 7∤d or
7|d; the character comparison quantifies a unit. These conditions are proved
or split in the closed endpoint. The generic topology lemma has ordinary
ring/uniform-space instances. The rational-form closure lemmas assume their
input forms are modular; the actual classical sequence supplies explicit
complex witnesses. None of these helper premises is an open analytic claim.

## Manuscripts and preservation

No new manuscript estimate is used in this milestone. The previous revised
candidate, received 14 September 2026 without an embedded version number,
has PDF hash `cd5a74d7ab96fff17e8b79bebee610a52772b581511b53f17dec34c28900fc6a`.
Its prior claim-by-claim review remains
[ZETA7_REVISION_DIFF_20260914.md](ZETA7_REVISION_DIFF_20260914.md).
No C1-C32 statement or analytic constant is changed in this run.
The KL construction sources and their mathematical-source versions remain
in [KL_CONSTRUCTION_PROVENANCE.md](KL_CONSTRUCTION_PROVENANCE.md).

The baseline is `Zeta7_specialization_20260914_154123.zip`, SHA-256
`cd754a6b57263abd305be72ebe26c266c30bc60ef85d5cd90ffa681e859f0ce1`.
Its project payload was extracted to `reference/uniform_baseline`, with
Lean files renamed `.lean.txt` for quarantine. Nested reference/checkpoint
archives were already present and retained in place. All 33 prior Lean
sources and all three pin files matched the extraction before the baseline
build. The original build and direct audits passed before any existing Lean
source was edited. New unimported drafts were prepared while those audits
ran; their extra source-scan entries do not represent additional baseline
compiled modules. The independently created ANNULAR_EXACT_CHECKS input bundle
is also reference material, not a registered Lean module.

The new checkpoint includes the prior checkpoint inputs and this milestone's
files, hashes and logs. Concurrent annular experiments and their unrelated
reports are outside this milestone and are excluded from its archive.
No artifact from those experiments is imported or used to prove these results.

Two further active-source modules, `UniformEndpoints.lean` and
`UniformEndpointsAudit.lean`, were added concurrently in the workspace during
verification. Both were read in full and included in the final compilation
and exhaustive dependency audit. They use only the already installed project
and mathlib constructions: Fermat/lifting for arbitrary seven-adic units,
uniform character convergence, simultaneous precision for all coefficients,
uniform convergence of the original stabilized sequence, and the exact
Lambert-expression modularity corollary. Their exact active bytes are in the
same source hash inventory. No external manuscript assertion enters them.
The initial complete build was retried because their master import appeared
after Lake had planned its dependencies; that failed attempt is retained as
`UNIFORM_FINAL_VERIFY_ATTEMPT_1.txt`.

Serre modularity proves neither overconvergence nor continuation. The first
independent remaining obligation is to construct the overconvergent
weight-minus-two Eisenstein form with this exact q-expansion on the required
annulus. The analytic U_7 and continuation bridges follow separately.

# The irrationality of ζ₇(3): informal account of the formalized result

## 1. Main result

**Theorem.** The 7-adic zeta value ζ₇(3) is irrational: ζ₇(3) ∉ ℚ ⊂ ℚ₇.

**Corollary.** η := ζ₇(3)/2 is irrational.

The proof is formalized in Lean 4 with Mathlib. The two endpoints are:

```lean
theorem Zeta7Main.zeta7Three_irrational : ¬ Zeta7Partial.IsRationalSeven Zeta7Main.zeta7Three
theorem Zeta7Main.eta_irrational        : ¬ Zeta7Partial.IsRationalSeven Zeta7Main.eta
```

Here `IsRationalSeven z` is `∃ q : ℚ, (q : ℚ_[7]) = z`, and `Zeta7Main.eta = Zeta7Main.zeta7Three / 2`. The rational value 0 is included: neither number is rational, including 0.

The Palomar statement file `Challenge.lean` restates the result using Mathlib only (`Zeta7Challenge.zeta7Three_irrational`, `Zeta7Challenge.eta_irrational`), together with the convergence theorem `Zeta7Challenge.approximant_tendsto` that pins down the definition. `Solution.lean` proves those declarations from the project's endpoints.

Nothing beyond these statements is claimed. In particular, no statement is made about ζ_p(3) for p ≠ 7, or about other 7-adic zeta values.

## 2. What ζ₇(3) means

For a prime p and an odd integer k ≥ 3, the p-adic zeta value is

  ζ_p(k) = L_p(k, ω^{1−k}),

the value at s = k of the Kubota–Leopoldt p-adic L-function twisted by the indicated power of the Teichmüller character ω. For p = 7 and k = 3 the character is ω^{−2}.

Its interpolation property, L_p(1−m, χ) = −(1 − χω^{−m}(p) p^{m−1}) B_{m,χω^{−m}}/m, becomes for m ≡ 4 (mod 6):

  L₇(1−m, ω^{−2}) = −(1 − 7^{m−1}) B_m / m = (1 − 7^{m−1}) ζ(1−m).

Take the weights w_n = 6·7^{n+1} − 2. They satisfy w_n ≡ 4 (mod 6) and w_n → −2 in ℤ₇, so 1 − w_n → 3. By continuity of L₇(·, ω^{−2}),

  ζ₇(3) = lim_{n→∞} −(1 − 7^{w_n−1}) B_{w_n} / w_n   (limit in ℚ₇).

This is the same number as in Lai–Lupu–Sprang [LLS]: ζ_p(s) = lim ζ(m) over negative integers m → s p-adically with m ≡ s (mod p−1). The Euler factor 1 − 7^{w_n−1} tends to 1 in ℚ₇.

**In Lean**, the project does not define `Zeta7Main.zeta7Three` as this limit:
- It is defined as `zetaSevenBranch 3`, the value at 3 of the fourth branch of a Kubota–Leopoldt function constructed from a 7-adic measure (the Mahler-transform construction of Rodrigues Jacinto–Williams, adapted from Birkbeck's formalization).
- The branch, sign, Euler-factor and B₁ conventions are fixed by a proved interpolation theorem.
- `Zeta7Main.bernoulli_approximants_tendsto_zeta7Three` proves that the Bernoulli sequence above converges to it.

`Challenge.lean` defines ζ₇(3) directly as the limit (`limUnder`) of that sequence. `Challenge.lean` also states `approximant_tendsto`, so the reader does not have to trust that the limit exists. `Solution.lean` proves the two definitions agree (`Zeta7Challenge.zeta7Three_eq`).

## 3. Proof architecture

The argument is a determinant (Siegel–Shidlovskii / Apéry–Beukers type) irrationality proof. It is carried out with modular forms on X₀(7) and a seven-adic analytic input.

### 3.1 The target function

Let:
- x(q) = q ∏_{7∤m} (1 − q^m)^{−4} = (η(7τ)/η(τ))⁴, a Hauptmodul for Γ₀(7);
- q(x) its compositional inverse;
- A = θ log x = E₂*-type weight-2 form, with θ = q d/dq;
- G(q) = Σ_{7∤a} q^a / (a³(1 − q^a)).

G + η is the q-expansion of the weight −2 specialization E₋₂* of the 7-adic Eisenstein family. It is constructed in Lean from the Kubota–Leopoldt measure. Its constant term is exactly η = ζ₇(3)/2.

Put B(x) = A(q(x)) and H(x) = B(x)·(G(q(x)) + η).

### 3.2 Differential and modular identities

The proof uses the following explicit identities. Each is proved in Lean.
- **Modular:** j = PN³/x, PN³ − T² = 1728x, and E₄/A² = N/P, E₆/A³ = T/P². Here P, N and T are explicit polynomials in x.
- **Fricke involution:** x ↦ 1/(49x).
- **Ramanujan-type:** H satisfies L H = R with L = D³ − VD − ½(DV), where D = x d/dx and V, R are explicit rational functions.
- **Primitives:** K = H D²H − ½(DH)² − ½VH² satisfies DK = RH. Its primitives J₁ and J₂ complete six "blocks" g = (H, DH, D²H, K, J₁, J₂) besides the constant 1.

### 3.3 N: seven-germ independence, zero estimate, determinant

- **Independence.** The seven germs 1, g₁, …, g₆ are linearly independent over ℂ(x), for every value of the parameter c in place of η. This rests on:
  - L v = hR has no rational solution;
  - the homogeneous module is irreducible;
  - a primitive-frame argument.
- **Zero estimate.** Any nonzero polynomial combination with degree < d has order of vanishing at 0 at most 7d + 175.
- **Determinant.** The jumps λ_j therefore satisfy j ≤ λ_j ≤ j + 176. A selected coefficient matrix gives a determinant D_d(c) ∈ ℚ that is nonzero for rational c (`actualCommonDeterminant_ne_zero`).

### 3.4 A: the seven-adic (annular) saving

Coefficient decay of H at every radius below 49 feeds a homogeneous solution on an open annulus. Splitting, a nonzero forcing polynomial, a Laurent relation, integral columns with explicit completion, and an exact count of the source-index cost then give

  v₇(D_d) ≥ (43 − δ) d² − K_δ d   for each fixed δ > 0.

The radius-49 decay is the only analytic input about the target (Section 4).

### 3.5 P: auxiliary-prime denominator estimate

For the primes p ≠ 7:

  Σ_{p≠7} v_p(D_d) log p ≥ −(12325/168 + ε) d²   for d ≫ 0  (`Zeta7Auxiliary.actualAuxiliaryEstimate`).

The proof uses:
- the Hasse polynomial and its simple roots;
- the rational homogeneous kernel in characteristic p;
- Cartier-type carries through the third and fourth layers;
- a derivative basis with compatible caps;
- two cap-one resonances;
- joint rank bounds;
- an exact profile summed over primes.

### 3.6 C: the Archimedean estimate

The germs pull back to holomorphic functions on |q| < 1. Pushing angular measures on six explicit circles forward by x(q) gives a measure μ with potential U. A Gram-determinant energy bound, and the return to the original determinant, give

  log|D_d| ≤ (J − (7/2) I + ε) d²   for d ≫ 0  (`Zeta7Arch.c_theorem`, `Zeta7Main.c_theorem_explicit`).

Here I is the energy of μ and J is an explicit constant. Lean proves the explicit upper bound I ≤ I_explicit (`Zeta7Valence.energyI_le_explicitI`).

### 3.7 The explicit margin and the conclusion

The surplus S := 43 log 7 + (7/2) I_explicit − J − 12325/168 satisfies S > 223/6250 (`Zeta7Cert.surplusS_gt`). This is a kernel-checked interval computation with no `native_decide`. Lean also proves log 7 < 2 (`Zeta7Cert.log_seven_lt_two`).

Suppose η ∈ ℚ. Then D_d(η) is a nonzero rational number, and the product formula gives log|D_d| = Σ_p v_p(D_d) log p. A, P and C then give lower and upper limits for d⁻² log|D_d| that differ by at least S − δ log 7 > 0 (with δ = 1/1000). This is impossible. Hence η ∉ ℚ, and ζ₇(3) = 2η ∉ ℚ.

## 4. The internal radius-49 theorem

Section 3.4 needs coefficient decay of H(x) at every radius ρ < 49 (`Zeta7Main.HSeries_radius49`). Earlier stages of this project took this as an explicit external input, `published_radius49_geometric_continuation`, justified from Calegari, Buzzard and Loeffler. The final version proves it in Lean:

1. **Twisted U₇ fixed point.**
   - The operator T(g) = A · U₇(g/A), transported to the coordinate x, fixes H.
   - This holds because U₇ E₋₂* = E₋₂*.
   - Hence the coefficients satisfy h_i = Σ_n t_{in} h_n with t_{in} = [x^i] T(x^n) (`HSeries_twisted_fixed`).
2. **HM, the matrix bound** (`Zeta7Radius49.twistMatrix_bound`).
   - The modular equation Ψ(Y, X) of degree 7 relating x(τ) and x(7τ) is proved from a level-one trace computation. A Newton recurrence for U₇(x^m) follows from it.
   - A Jacobian formula for the twisted operator gives explicit column recurrences.
   - Valuation bounds v₇(e_{k,j}) ≥ (7j − k)/4 then yield
     ‖t_{in}‖ · (7^{s′})^i ≤ K · (7^s)^n with s′ = min(7s, (12 + s)/7), for every 0 < s < 2.
3. **HO, initial overconvergence** (`Zeta7Radius49.initial_HSeries_overconvergent`). H has bounded coefficients at radius 7^{1/4} > 1.
   - The proof uses the classical approximants A·E*_{k_r}/E₆^{7^r} with k_r = 6·7^r − 2. These weights lie in the same component of weight space as −2.
   - It also uses:
     - the Katz ratio E₆/V(E₆) = T(x)/T̃(x);
     - generation of level-one forms by E₄ and E₆;
     - U₇-fixedness of the stabilized Eisenstein series;
     - a near-ordinary bound for T;
     - a chain argument uniform in r;
     - the limit r → ∞, using E₆^{7^r} ≡ 1 (mod 7^{r+1}) and uniform convergence of E_{k_r} to E₋₂*.
4. **Bootstrap.** Starting from HO, iterating HM with the map s ↦ min(7s, (12+s)/7) reaches every s < 2 (`hasRadius49_of_matrix_bound_and_initial`). This gives
   `Zeta7Main.internal_radius49_geometric_continuation : HasRadius49GeometricContinuation`.

The retired axiom survives only in the archival module `Zeta7Proof/PublishedRadius49GeometricInput.lean`, which no module imports. `FinalInternalAudit` checks that it is absent from the environment of the final theorems.

## 5. Kernel and axiom status

```text
#print axioms Zeta7Main.zeta7Three_irrational
'Zeta7Main.zeta7Three_irrational' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms Zeta7Main.eta_irrational
'Zeta7Main.eta_irrational' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are Lean's three standard foundational axioms. The same holds for `internal_radius49_geometric_continuation`, `twistMatrix_bound`, `initial_HSeries_overconvergent`, `c_theorem_explicit`, `surplusS_gt` and `energyI_le_explicitI`.

The final dependency graph contains:
- no project-specific axiom (`FinalInternalAudit` checks 10,903 project declarations in the import closure);
- no `sorry` or `admit`;
- no `native_decide` and no `Lean.ofReduceBool`;
- no `opaque`, `unsafe`, `implemented_by` or `extern` declaration.

Theorems with hypotheses are used only after the hypotheses have been discharged.

## 6. Reproducibility

- **Lean:** `leanprover/lean4:v4.34.0-rc2`.
- **Mathlib:** tag `v4.34.0-rc2`, commit `85e3a25e006c35636f0e53b0e9296caca2685bc0`, pinned in `lake-manifest.json`.
- **Build:** `lake build` builds the whole development, the audits, `Challenge` and `Solution`. The last complete build finished with "Build completed successfully"; see `FULLY_INTERNAL_COMPLETION.md` for job counts.
- **Proof checkpoint:** `Zeta7_radius_FULLY_INTERNAL_20260919_161042.zip`, SHA-256 `aad146be430a3509c55dc982885025d984c8b4e20eda2835eac30e4b111da5f4`.
- **Audit modules:** `Zeta7Proof/FinalInternalAudit.lean` (final endpoints, project axioms, archival module absent), `Zeta7Proof/Radius49CompleteAudit.lean` (the radius layer and its non-circularity), and `Zeta7Proof/FinalAudit.lean`.
- **Comparator surrogate:** `palomar_local_check/` contains a local reimplementation of Comparator's declaration-closure comparison, used because the official tool is Linux-only.

## 7. Literature context

- **Known cases.** Calegari [C] proved the irrationality of ζ_p(3) for p = 2 and 3 using overconvergent p-adic modular forms, adapting Beukers' treatment of Apéry's theorem. Beukers [B] gave an alternative proof by Padé approximation. As reported in [LLS], ζ₂(5) was proved irrational by Calegari, Dimitrov and Tang, and independently by Lai, Sprang and Zudilin.
- **Stated as open.** Lai, Lupu and Sprang [LLS] prove that for each prime p ≥ 5 some ζ_p(i), with i odd in [3, p + p/log p + 5], is irrational. They write: "for any prime p ⩾ 5, the irrationality of ζ_p(3) still remains an open question."
- **This formalization** establishes the case p = 7.

A literature search on 19 September 2026 (arXiv, Crossref and general web search) found no other proof of the irrationality of ζ₇(3) or ζ₅(3). The search was not exhaustive, and the mathematical argument has not been refereed or published.

The mathematical source for the formalization is the project manuscript *A determinant argument for the irrationality of ζ₇(3)* (Yi Taifeng, 15 September 2026, unrefereed; developed with the AI assistance described in `PROVENANCE.md`). It was written before the Lean proof was complete. The Lean development differs from it in one substantive respect: the radius-49 continuation is proved internally rather than taken from the literature.

## References

- [B] F. Beukers, *Irrationality of some p-adic L-values*, Acta Math. Sin. (Engl. Ser.) **24** (2008), 663–686. doi:10.1007/s10114-007-1029-2.
- [Bu] K. Buzzard, *Analytic continuation of overconvergent eigenforms*, J. Amer. Math. Soc. **16** (2003), 29–55. doi:10.1090/S0894-0347-02-00405-8.
- [C] F. Calegari, *Irrationality of certain p-adic periods for small p*, Int. Math. Res. Not. **2005**, no. 20, 1235–1249. doi:10.1155/IMRN.2005.1235. arXiv:math/0408214.
- [LLS] L. Lai, C. Lupu, J. Sprang, *On the irrationality of certain p-adic zeta values*, Res. Math. Sci. **12** (2025), article 77. doi:10.1007/s40687-025-00559-x. arXiv:2505.23088.
- [RJW] J. Rodrigues Jacinto, C. Williams, *An introduction to p-adic L-functions*, arXiv:2309.15692.

# Local pre-submission checks

The official Palomar verifier runs Comparator inside a Linux Landrun sandbox. It cannot run on the Windows machine used to prepare this package. The two scripts here reproduce its checks locally. They are advisory; Palomar's own run is authoritative.

## Declaration-closure comparison

**Files:** `DumpChallenge.lean`, `DumpSolution.lean`.

**What it does.** Starting from the three names in `comparator.json`, each script walks the used-constant graph in the same way as Comparator's `Compare.loop` (Comparator commit `575674928e239f5bc452aab72d1dd7b0f1326494`):
- the named theorems are recorded by kind and type only;
- every other declaration reached is recorded by kind, universe parameters, type and value.

**Run it:**

```sh
lake build Challenge Solution
lake env lean palomar_local_check/DumpChallenge.lean
lake env lean palomar_local_check/DumpSolution.lean
cmp palomar_local_check/challenge_closure.txt palomar_local_check/solution_closure.txt
```

**Result on 19 September 2026:**
- 12,576 constants were reached on each side, and the two outputs are identical.
- The three Solution theorems use exactly `[propext, Classical.choice, Quot.sound]`.
- The Challenge theorems additionally show `sorryAx`, from its intended holes.

**Negative control:** changing `weight` in a copy of the Challenge changed exactly one line of the output.

## Metadata validation

**File:** `validate_formalization.pl`.

**What it checks.** It mirrors the mechanical `formalization.yaml` contract in PalomarSubmission `scripts/submission_contract.py` (commit `3561d237dcc4b28482558ad28a64d767d7cc8615`):
- required fields and their lengths;
- human authors and maintainers;
- arXiv and MSC2020 codes against Palomar's taxonomy snapshots;
- source-origin consistency;
- the automation and review fields.

It parses with YAML-Tiny 1.77, which is pure Perl and rejects duplicate keys.

**Run it:**

```sh
YAML_TINY_LIB=<dir containing YAML/Tiny.pm> perl palomar_local_check/validate_formalization.pl \
  formalization.yaml <PalomarSubmission checkout>/taxonomies
```

**Result:** `FORMALIZATION.YAML VALID (mechanical contract mirror)`, with `result_origin: original`.

**Negative controls:** a duplicate key, an original-proof with a substantive relationship, and an unknown MSC code are each rejected.

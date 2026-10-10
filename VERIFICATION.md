# Verification

All eighteen statements of Challenge.lean have proofs. The local build, the axiom audit, the source guard, the
definition and statement checks, the standard-library replay of the finite facts behind the compared statements,
the metadata check, the module-resolution check, the elaboration check and Palomar's core-notation audit of the
statements pass; `python scripts/verify.py` runs them all and ends with `VERIFY: PASS`. The checks below were last
run on the tree of the final commit (the counts are printed by verify.py); a build log is evidence for that tree
only. Theorems are numbered as in `comparator.json`, which is also their order in Challenge.lean. `comparator.json`
lists no `definition_names`: a name there is a definition hole whose value the Solution supplies; the thirty-one
definitions here are fully specified in the Challenge (the game built from Kuhn's tree), so the comparator checks
the Solution's values against them.

## Formal scope

| # | Statement | Proved in |
| --- | --- | --- |
| 1 | `hasValue_one_one` — Kuhn's game has value −1/18 | KuhnPoker/Value.lean |
| 2 | `hasValue_unique` — a game has at most one value (every a, b) | KuhnPoker/Value.lean |
| 3 | `exists_isEquilibrium` — an equilibrium exists | KuhnPoker/Value.lean |
| 4 | `payoff_of_isEquilibrium` — every equilibrium pays I exactly −1/18 | KuhnPoker/Value.lean |
| 5 | `isEquilibrium_iff` — a pair is an equilibrium iff each strategy guarantees −1/18 | KuhnPoker/Value.lean |
| 6 | `guarantees₂_iff` — II's optimal strategy is unique: `kuhnII` | KuhnPoker/Value.lean |
| 7 | `guarantees₁_iff` — I's optimal strategies are exactly `kuhnI α k`, α ∈ [0, 1/3], k ∈ [0, 1], 3α = 1 ∨ k = 1 | KuhnPoker/Value.lean |
| 8 | `essentialMatrix_eq` — Kuhn's essential 8 × 4 matrix is six times the game matrix | KuhnPoker/NormalForm.lean |
| 9 | `basic₁_guarantees` — each of Kuhn's twelve basic strategies (A)–(L) guarantees −1/18 | KuhnPoker/NormalForm.lean |
| 10 | `basic₂_guarantees` — each of II's two basic strategies guarantees −1/18 | KuhnPoker/NormalForm.lean |
| 11 | `hasMixedValue` — the 27 × 64 normal form has value −1/18 | KuhnPoker/NormalForm.lean |
| 12 | `guaranteesMixed₁_iff` — a mixed strategy of I is optimal iff its realization plan lies on the segment | KuhnPoker/NormalForm.lean |
| 13 | `guaranteesMixed₂_iff` — a mixed strategy of II is optimal iff its marginals are `kuhnII` | KuhnPoker/NormalForm.lean |
| 14 | `hasValue_general` — the value `kuhnValue a b` at every ante a > 0 and bet b > 0 | KuhnPoker/General.lean |
| 15 | `kuhnValue_one_one` — `kuhnValue 1 1 = −1/18` | KuhnPoker/General.lean |
| 16 | `guarantees_case_one` — Case 1 (b ≤ a): Kuhn's strategies guarantee the value | KuhnPoker/General.lean |
| 17 | `guarantees_case_three` — Case 3 (a ≤ b ≤ 2a): Kuhn's strategies, η ∈ [(2a − b)/(2a + b), b/(2a + b)] | KuhnPoker/General.lean |
| 18 | `guarantees_case_four` — Case 4 (b ≥ 2a): the value 0 and its strategies | KuhnPoker/General.lean |

## What is checked

- **Build** — `lake build KuhnPoker`, `lake build Challenge`, `lake build Solution`, `lake build Test` on the pinned
  toolchain and Mathlib (`lean-toolchain`, `lake-manifest.json`; `lake update` is never run).
- **Axioms** — `Test/Axioms.lean` walks every constant in `KuhnPoker.*` (and the private auxiliaries the module
  system generates) and fails the build on any axiom beyond `propext`, `Classical.choice`, `Quot.sound`; it also
  fails if any compared theorem is missing from the environment.
- **Source guard** — `scripts/check-source.py` rejects `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`,
  `partial`, `implemented_by`, `extern`, `opaque`, `mutual`, `ofReduceBool` and the kernel-bypass options outside
  comments and strings in `KuhnPoker/`, `Solution.lean` and `Test/` (Challenge.lean's intentional `sorry`
  placeholders excepted).
- **Definitions and statements** — `scripts/check_definitions.py` compares every definition block of Challenge.lean
  with `KuhnPoker/Defs.lean` character for character; `scripts/check_statements.py` compares every theorem header
  of Challenge.lean with Solution.lean; `scripts/verify.py` prints every compared definition with `pp.all` from both
  modules and requires identical output, and runs Palomar's core-notation audit on every compared declaration.
- **Replay** — `scripts/check_kuhn.py` rebuilds the game from the five courses in the standard library, exactly,
  and checks the essential matrix, both optimal sets at a = b = 1 (II's six pins; the family on a grid, with the
  call-with-3 clause), the fourteen basic strategies and their plans, the general-stakes witnesses at sample stakes
  in every region and on both boundaries, and the refutation of the printed Case 3 interval.

## What is not checked here

The statements' faithfulness to Kuhn's paper is argued in `formalization.yaml` (fidelity) and PROOF.md, not
checked mechanically. The full optimal sets at general stakes (beyond the stated witnesses), Kuhn's convex-hull
form of the optimal polytopes and the n-card game are outside the formal scope.

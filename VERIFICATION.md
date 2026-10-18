# Verification

All thirty-seven statements of Challenge.lean have proofs. The local build, the axiom audit, the source guard and
its controls, the definition and statement checks, the standard-library replays of the finite facts behind the
compared statements, the metadata check, the module-resolution check, the elaboration check and Palomar's
core-notation audit of the statements pass; `python scripts/verify.py` runs them all and ends with `VERIFY: PASS`.
The checks below were last run on the tree of the final commit (the counts are printed by verify.py); a build log
is evidence for that tree only. Theorems are numbered as in `comparator.json`, which is also their order in
Challenge.lean. `comparator.json` lists no `definition_names`: a name there is a definition hole whose value the
Solution supplies; the thirty-one definitions here are fully specified in the Challenge (the game built from
Kuhn's tree), so the comparator checks the Solution's values against them.

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
| 19 | `upper_certificate` — the upper-bound identity, for every σ (valid or not): −1/18 − payoff σ kuhnII = three products, nonnegative when σ is valid | KuhnPoker/Value.lean |
| 20 | `lower_certificate` — the lower-bound identity, for every α, k, τ (valid or not): payoff (kuhnI α k) τ + 1/18 = four products − (1 − 3α)(1 − k)·(…); the four are nonnegative for α ∈ [0, 1/3] and valid τ | KuhnPoker/Value.lean |
| 21 | `isEquilibrium_iff_explicit` — the equilibria of Kuhn's game are exactly the pairs (kuhnI α k, kuhnII) with α ∈ [0, 1/3], k ∈ [0, 1], 3α = 1 ∨ k = 1 | KuhnPoker/Value.lean |
| 22 | `case_one_I_unique` — b < a: I's optimal strategy is unique up to the unreached call with the 3 | KuhnPoker/General.lean |
| 23 | `case_one_II_iff` — b ≤ a: II's optimal strategies are Kuhn's with the bet with the 2 after a pass free in [0, 2(a − b)/(2a + b)] | KuhnPoker/General.lean |
| 24 | `diagonal_II_unique` — a = b: II's optimal strategy is unique at every scale | KuhnPoker/General.lean |
| 25 | `diagonal_I_iff` — a = b: I's optimal strategies are Kuhn's family at every scale | KuhnPoker/General.lean |
| 26 | `case_three_I_unique` — a < b ≤ 2a: I's optimal strategy is unique | KuhnPoker/General.lean |
| 27 | `case_three_II_iff` — a ≤ b ≤ 2a: with the other coordinates pinned, η guarantees the value iff (2a − b)/(2a + b) ≤ η ≤ b/(2a + b) | KuhnPoker/General.lean |
| 28 | `case_three_II_set` — a ≤ b < 2a: II's optimal strategies exactly (bets forced; calls a polytope of three inequalities) | KuhnPoker/General.lean |
| 29 | `case_three_printed_interval` — a ≤ b ≤ 2a, η on Kuhn's printed interval [b/(2a + b), (a + b)/(2a + b)]: II's (b/(2a + b), 0, 1; 0, η, 1) guarantees the value iff η = b/(2a + b) | KuhnPoker/General.lean |
| 30 | `case_three_printed_upper_end_fails` — at a = 2, b = 3, the printed upper end η = 5/7 fails | KuhnPoker/General.lean |
| 31 | `case_four_I_iff` — 2a ≤ b: I's optimal strategies exactly | KuhnPoker/General.lean |
| 32 | `case_four_II_iff` — 2a < b: II's optimal strategies exactly | KuhnPoker/General.lean |
| 33 | `boundary_II_certificate` — b = 2a, the bet with the 2 zero: −3·payoff is a times six products, for every a and every pair | KuhnPoker/Boundary.lean |
| 34 | `boundary_II_iff` — b = 2a: II's optimal strategies exactly (the bet with the 2 after a pass zero, and four inequalities) | KuhnPoker/Boundary.lean |
| 35 | `payoff_of_isEquilibrium_general` — every a, b > 0: every equilibrium pays `kuhnValue a b` | KuhnPoker/Equilibrium.lean |
| 36 | `isEquilibrium_general_iff` — every a, b > 0: a pair is an equilibrium iff each strategy guarantees `kuhnValue a b` | KuhnPoker/Equilibrium.lean |
| 37 | `boundary_isEquilibrium_iff` — b = 2a: the equilibria are exactly I's single strategy with any strategy of II's polytope | KuhnPoker/Equilibrium.lean |

## What is checked

- **Build** — `lake build KuhnPoker`, `lake build Challenge`, `lake build Solution`, `lake build Test` on the pinned
  toolchain and Mathlib (`lean-toolchain`, `lake-manifest.json`; `lake update` is never run).
- **Axioms** — `Test/Axioms.lean` walks every public constant in `KuhnPoker.*` (private auxiliaries are not
  enumerated under the module system, but `collectAxioms` reaches every private constant a public proof uses) and
  fails the build on any axiom beyond `propext`, `Classical.choice`, `Quot.sound`; it also fails if fewer than 190
  constants are matched or any compared theorem is missing from the environment.
- **Source guard** — `scripts/check-source.py` rejects `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`,
  `partial`, `implemented_by`, `extern`, `opaque`, `mutual`, `ofReduceBool`, `set_option` and every `debug.` option
  outside comments and strings in `KuhnPoker/`, `Solution.lean` and `Test/` (Challenge.lean's intentional `sorry`
  placeholders excepted), any `leanOptions`, `moreLeanArgs`, `weakLeanArgs` or `-D` in `lakefile.toml`, and any
  control character in the Python scripts; `scripts/check_source_guard.py` runs the guard on one clean fixture, six
  prohibited-option fixtures and one with a control byte in a script, so a regex that silently drops an alternative
  fails the run.
- **Definitions and statements** — `scripts/check_definitions.py` compares every definition block of Challenge.lean
  with `KuhnPoker/Defs.lean` character for character; `scripts/check_statements.py` compares every theorem header
  of Challenge.lean with Solution.lean; `scripts/verify.py` prints every compared definition, and the type of every compared theorem, with
  `pp.all` from both modules and requires identical output, and runs Palomar's core-notation audit on every
  compared declaration.
- **Replay** — `scripts/check_kuhn.py` rebuilds the game from the five courses in the standard library, exactly,
  and checks the essential matrix; II's strategy at a = b = 1 (its guarantee against all 27 pure strategies of I,
  tight exactly on the 8 essential rows, and the failure of every single-coordinate move by ±1/10); I's family on a
  grid with the call-with-3 clause; the fourteen basic strategies and their plans; the vertices of both optimal
  polytopes of the normal form (an exact enumeration over the essential rows and columns, to which the
  realization-plan and marginal forms confine the support: exactly Kuhn's twelve and two); the general-stakes
  witnesses at sample stakes in every region and on both boundaries; and the refutation of the printed Case 3
  interval. `scripts/check_boundary.py` rebuilds the payoff a second way (branching on I's pure action) and checks
  the b = 2a identity at a = 1 on all 2,048 Boolean points of its eleven free coordinates (both sides are
  multi-affine in them and linear in a, so the points decide it; the theorem states it for every a), the five pure deviations behind the polytope, its nine vertices by exact
  elimination over every five of the fourteen constraints, all 27 pure responses at each vertex, a strict interior
  point, and the agreement of the four inequalities with all 27 pure-response inequalities on 3,125 grid points.

## What is not checked here

The statements' faithfulness to Kuhn's paper is argued in `formalization.yaml` (fidelity) and PROOF.md, not
checked mechanically. The vertex count and the dimension of II's set on b = 2a (replayed by
`scripts/check_boundary.py`), Kuhn's convex-hull form of the optimal polytopes (its vertices replayed by
`scripts/check_kuhn.py`, not stated as a theorem; on paper equivalent to the realization-plan form proved) and the
n-card game are outside the formal scope.

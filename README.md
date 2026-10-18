# Kuhn poker: the value −1/18, all optimal strategies, and the solution at every ante and bet

Kuhn's simplified two-person poker (H. W. Kuhn, *A simplified two-person poker*, Contributions to the Theory of
Games I, Ann. of Math. Studies 24 (1950) 97–103): three cards `1 < 2 < 3`, one dealt to each player, an ante of
`a` from each and a single bet of `b` (Kuhn's game has `a = b = 1`); player I bets or passes; after a pass II
bets or passes, and after II's bet I calls or folds; after I's bet II calls or folds; the five courses of play
of p. 98 pay `a` to the higher card (pass–pass), `a` to II (pass–bet–pass), `a + b` to the higher card
(pass–bet–bet), `a` to I (bet–pass) and `a + b` to the higher card (bet–bet). A behaviour strategy gives, per
card, I's probability of betting first and of calling after passing, and II's probability of betting after a
pass and of calling a bet.

[Challenge.lean](Challenge.lean) builds the game from this tree (thirty-one definitions, namespace `KuhnPoker`)
and states thirty-seven theorems; [Solution.lean](Solution.lean) proves them, kernel-only; the table in
[VERIFICATION.md](VERIFICATION.md) names each one. For Kuhn's game:

- the value is `−1/18`: each player has a strategy guaranteeing it, a game has at most one value, an
  equilibrium exists, every equilibrium pays I exactly `−1/18`, and a pair is an equilibrium iff each strategy
  guarantees the value (`hasValue_one_one`, `hasValue_unique`, `exists_isEquilibrium`,
  `payoff_of_isEquilibrium`, `isEquilibrium_iff`);
- II's optimal strategy is unique at all six information sets — bet after a pass with the `1, 2, 3` with
  probabilities `1/3, 0, 1`, call with probabilities `0, 1/3, 1` (`guarantees₂_iff`; Kuhn's `(ξ, η) = (1/3, 1/3)`
  with the four coordinates he removed as superfluous proved forced);
- I's optimal strategies are exactly Kuhn's family: bet the `1` with probability `α` and fold it, never bet the
  `2` first and call with it with probability `α + 1/3`, bet the `3` with probability `3α` and call with it, for
  `α ∈ [0, 1/3]`, the call with the `3` unconstrained exactly when `3α = 1` (`guarantees₁_iff`); so the
  equilibria are exactly the pairs of such a strategy with II's (`isEquilibrium_iff_explicit`);
- the two certificates are stated as identities (`upper_certificate`, `lower_certificate`): `−1/18` minus the
  payoff against II's strategy is three products, nonnegative on valid strategies, and the payoff of the family plus
  `1/18` is four such products minus a tail carrying the factor `(1 − 3α)(1 − k)`;
- the normal form, with Kuhn's coding of the `27` and `64` pure strategies: his essential `8 × 4` matrix is six
  times the game matrix (`essentialMatrix_eq`), his twelve basic optimal mixed strategies (A)–(L) and II's two
  guarantee `−1/18` (`basic₁_guarantees`, `basic₂_guarantees`, `hasMixedValue`), and a mixed strategy is
  optimal iff its realization plan lies on the family (I) or its marginals are II's strategy (II)
  (`guaranteesMixed₁_iff`, `guaranteesMixed₂_iff`).

For every ante `a > 0` and bet `b > 0` (Kuhn's pp. 102–103, stated there without proof, and the region `b > 2a`
he does not state): the value is `−b²/(6(2a + b))` for `b ≤ a`, `−b(2a − b)/(6(2a + b))` for `a ≤ b ≤ 2a` and
`0` for `b ≥ 2a` (`hasValue_general`, `kuhnValue_one_one`), with explicit guaranteeing strategies in each case —
Kuhn's for `b ≤ 2a`, II's Case 3 call taken from the corrected interval, and his `b = 2a` strategies for every
`b ≥ 2a` (`guarantees_case_one`, `guarantees_case_three`, `guarantees_case_four`); every equilibrium pays
`kuhnValue a b`, and a pair is an equilibrium iff each strategy guarantees it (`payoff_of_isEquilibrium_general`,
`isEquilibrium_general_iff`), so the equilibria at every ante and bet are exactly the pairs of optimal strategies
below. The full optimal sets (Kuhn states strategies for `b ≤ 2a` only, in his reduced parameters): I's strategy is
unique for `b < a` up
to the unreached call with the `3` (`case_one_I_unique`) and for `a < b ≤ 2a` outright (`case_three_I_unique`); on
the diagonal `b = a` it is Kuhn's family at every scale (`diagonal_I_iff`); for `b ≥ 2a` it never bets the `1` or
the `2` first, folds them, and with the `3` is cut out by one inequality (`case_four_I_iff`), a single strategy at
`b = 2a` and beyond it a two-dimensional set in which I may also bet the `3` first, with probability at most
`(b − 2a)/b` (a triangle in realization-plan coordinates); so Kuhn's bluffing family belongs to `b = a` alone. II's
strategy is unique on the diagonal at every scale (`diagonal_II_unique`) and a segment for `b ≤ a`
(`case_one_II_iff`); for `a ≤ b < 2a` its bets after a pass are forced, `(b/(2a + b), 0, 1)`, and its calls form a
polytope of three inequalities (`case_three_II_set`); for `b > 2a` it never bets the `1` or the `2` after a pass,
never calls with them, and calls with the `3` with probability at least `4a/(2a + b)`, its bet with the `3` free
(`case_four_II_iff`); and on the line `b = 2a` its optimal set is a five-dimensional polytope (`boundary_II_iff`):
the bet with the `2` after a pass is `0` and, writing the bets after a pass `(p, 0, r)` and the calls `(s, t, w)`,
`2p ≤ r`, `s + t ≤ p`, `1 ≤ t + w` and `1 + p + s ≤ 2w` — nine vertices (replayed), one of them calling a bet with
the `1` half the time at an information set no equilibrium reaches; the neighbouring descriptions reach only a face
and an edge of it (PROOF.md §5). The identity behind it is a theorem (`boundary_II_certificate`): with the bet with
the `2` zero, `−3` times the payoff at `b = 2a` is `a` times six products, each nonnegative for a valid strategy of
I against a strategy of the polytope; and the equilibria on the line are exactly I's single strategy with any
strategy of the polytope (`boundary_isEquilibrium_iff`).

Two corrections to the printed text and one scope note. In Case 3 the calling probability `η` with the `2`
ranges exactly over `[(2a − b)/(2a + b), b/(2a + b)]` (`case_three_II_iff`), and the interval printed on p. 102,
`b/(2a + b) ≤ η ≤ (a + b)/(2a + b)`, holds only at its lower end (`case_three_printed_interval`; at
`a = 2, b = 3`, `η = 5/7` lets I gain, `case_three_printed_upper_end_fails`). p. 101's table gives `β = 5/12` for
the basic strategies (I) and (J), where p. 100's mixtures and p. 101's own formula give `7/12` (not a theorem
here; the replay checks that the twelve plans lie on the segment, which gives `β = α + 1/3 = 7/12`). And Case 1's
"both players have a unique optimal mode of behavior" is true in his behaviour parameters, the terms in which he
states the solutions; in the full game II may also bet the `2` after a pass with any probability in
`[0, 2(a − b)/(2a + b)]` (`case_one_II_iff`).

Every guarantee is a finite nonnegative-product identity: the gap between the payoff and the value is a sum of
products of the opponent's probabilities and their complements with nonnegative coefficients (polynomials in `a`,
`b` and the free parameter, at general stakes built from `a`, `b`, `2a + b`, `a − b`, `2a − b`, `4a − b`, `b − 2a`
and the interval factors `(2a + b)η − (2a − b)`, `b − (2a + b)η`, `2(a − b) − (2a + b)ξ`, and, in the optimal-set theorems, the
slacks of their stated inequalities), and every "only if" is a
linear certificate from finitely many pure strategies. `scripts/check_kuhn.py` replays the finite facts in the
standard library, Kuhn's twelve and two vertices included; `scripts/check_boundary.py` replays the line `b = 2a`
(the vertex count and the dimension are replayed, not stated as theorems); `python scripts/verify.py`
runs every local check and ends with `VERIFY: PASS`. No formal library found by the dated search (2026-10-10)
holds the game; nothing is derived from another project.
Lean v4.35.0-rc2, Mathlib v4.35.0-rc2; MIT ([LICENSE](LICENSE)); AI assistance in [DISCLOSURE.md](DISCLOSURE.md).

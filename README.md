# Kuhn poker: the value −1/18, the optimal sets, and the value at every ante and bet

Kuhn's simplified two-person poker (H. W. Kuhn, *A simplified two-person poker*, Contributions to the Theory of
Games I, Ann. of Math. Studies 24 (1950) 97–103): three cards `1 < 2 < 3`, one dealt to each player, an ante of
`a` from each and a single bet of `b` (Kuhn's game has `a = b = 1`); player I bets or passes; after a pass II
bets or passes, and after II's bet I calls or folds; after I's bet II calls or folds; the five courses of play
of p. 98 pay `a` to the higher card (pass–pass), `a` to II (pass–bet–pass), `a + b` to the higher card
(pass–bet–bet), `a` to I (bet–pass) and `a + b` to the higher card (bet–bet). A behaviour strategy gives, per
card, I's probability of betting first and of calling after passing, and II's probability of betting after a
pass and of calling a bet.

[Challenge.lean](Challenge.lean) builds the game from this tree (thirty-one definitions, namespace `KuhnPoker`)
and states eighteen theorems; [Solution.lean](Solution.lean) proves them, kernel-only; the table in
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
  `α ∈ [0, 1/3]`, the call with the `3` unconstrained exactly when `3α = 1` (`guarantees₁_iff`);
- the normal form, with Kuhn's coding of the `27` and `64` pure strategies: his essential `8 × 4` matrix is six
  times the game matrix (`essentialMatrix_eq`), his twelve basic optimal mixed strategies (A)–(L) and II's two
  guarantee `−1/18` (`basic₁_guarantees`, `basic₂_guarantees`, `hasMixedValue`), and a mixed strategy is
  optimal iff its realization plan lies on the family (I) or its marginals are II's strategy (II)
  (`guaranteesMixed₁_iff`, `guaranteesMixed₂_iff`).

For every ante `a > 0` and bet `b > 0` (Kuhn's pp. 102–103, stated there without proof, and the region `b > 2a`
he does not state): the value is `−b²/(6(2a + b))` for `b ≤ a`, `−b(2a − b)/(6(2a + b))` for `a ≤ b ≤ 2a` and
`0` for `b ≥ 2a` (`hasValue_general`, `kuhnValue_one_one`), with explicit guaranteeing strategies in each case
(`guarantees_case_one`, `guarantees_case_three`, `guarantees_case_four`). Two corrections to the printed text:
in Case 3 the calling probability `η` with the `2` ranges over `[(2a − b)/(2a + b), b/(2a + b)]`, and the
interval printed on p. 102, `b/(2a + b) ≤ η ≤ (a + b)/(2a + b)`, fails at its upper end (at `a = 2, b = 3`,
`η = 5/7` lets I gain); and Case 1's "unique optimal mode of behavior" holds for the reduced parameters only
(II may bet the `2` after a pass with any probability in `[0, 2(a − b)/(2a + b)]`).

Every inequality is a finite nonnegative-product identity — the target minus the payoff is a sum of nonnegative
rational multiples of products of probabilities and their complements, with the case factors `a − b`, `2a − b`,
`b − 2a` at general stakes — and every "only if" is a linear certificate from finitely many pure strategies.
`scripts/check_kuhn.py` replays the finite facts in the standard library; `python scripts/verify.py` runs every
local check and ends with `VERIFY: PASS`. No library holds the game; nothing is derived from another project.
Lean v4.35.0-rc2, Mathlib v4.35.0-rc2; MIT ([LICENSE](LICENSE)); AI assistance in [DISCLOSURE.md](DISCLOSURE.md).

#!/usr/bin/env python3
"""Standard-library replay of the finite facts behind the compared statements (exact rational arithmetic).

    python -I scripts/check_kuhn.py

Rebuilds Kuhn poker from the five courses of play (Kuhn 1950, p. 98) with ante a and bet b, independently of
the Lean text, and checks: (1) Kuhn's essential 8 x 4 matrix (p. 99) is six times the game matrix on his rows
and columns; (2) II's strategy (bet after a pass 1/3, 0, 1; call 0, 1/3, 1) holds all 27 pure strategies of I to
at most -1/18, with equality exactly on the 8 essential rows; (3) I's family (bet alpha, 0, 3 alpha; call
0, alpha + 1/3, k) guarantees at least -1/18 against all 64 pure strategies of II for every alpha in a rational
grid of [0, 1/3] with k = 1, and for every k in a grid at 3 alpha = 1; (4) Kuhn's twelve basic mixed strategies
(A)-(L) and II's two (p. 100) guarantee -1/18 in the normal form, and their realization plans lie on the family;
(5) the general-stakes witnesses of the Challenge (Cases 1, 3, 4) guarantee kuhnValue(a, b) at rational sample
stakes in each region and on both boundaries, with eta at both ends and the middle of the corrected Case 3
interval; (6) Kuhn's printed Case 3 interval fails at its upper end (a = 2, b = 3, eta = 5/7: some pure strategy
of I earns more than the value). Every check prints its outcome; the last line is VERDICT: PASS or VERDICT: FAIL
and the exit status is 0 only on PASS. No asserts (python -O strips them)."""

from fractions import Fraction as F
from itertools import product
import sys

CARDS = (0, 1, 2)
DEALS = [(c, d) for c in CARDS for d in CARDS if c != d]
failures = []


def check(name, ok, detail=""):
    print(f"[{'ok' if ok else 'FAIL'}] {name}" + (f": {detail}" if detail else ""))
    if not ok:
        failures.append(name)


def to_higher(c1, c2, k):
    return k if c2 < c1 else -k


def deal_payoff(a, b, bet1, call1, bet2, call2, c1, c2):
    """The five courses (p. 98): pass-pass, pass-bet-pass, pass-bet-bet, bet-pass, bet-bet; payoff to I."""
    return ((1 - bet1[c1]) * (1 - bet2[c2]) * to_higher(c1, c2, a)
            + (1 - bet1[c1]) * bet2[c2] * (1 - call1[c1]) * (-a)
            + (1 - bet1[c1]) * bet2[c2] * call1[c1] * to_higher(c1, c2, a + b)
            + bet1[c1] * (1 - call2[c2]) * a
            + bet1[c1] * call2[c2] * to_higher(c1, c2, a + b))


def payoff(a, b, s1, s2):
    bet1, call1 = s1
    bet2, call2 = s2
    return sum(deal_payoff(a, b, bet1, call1, bet2, call2, c1, c2) for c1, c2 in DEALS) / 6


def pure1(x):
    """Kuhn's coding: 0 = pass then fold, 1 = pass then call, 2 = bet."""
    return ([F(1) if x[c] == 2 else F(0) for c in CARDS], [F(1) if x[c] == 1 else F(0) for c in CARDS])


def pure2(y):
    """Kuhn's coding: binary, first figure = bet after a pass, second = call a bet."""
    return ([F(1) if y[c] >= 2 else F(0) for c in CARDS], [F(1) if y[c] in (1, 3) else F(0) for c in CARDS])


PURE1 = list(product((0, 1, 2), repeat=3))
PURE2 = list(product((0, 1, 2, 3), repeat=3))
V = F(-1, 18)
KUHN_II = ([F(1, 3), F(0), F(1)], [F(0), F(1, 3), F(1)])


def kuhn_I(alpha, k):
    return ([alpha, F(0), 3 * alpha], [F(0), alpha + F(1, 3), k])


def guarantees1(a, b, s1, v):
    return all(payoff(a, b, s1, pure2(y)) >= v for y in PURE2)


def guarantees2(a, b, s2, v):
    return all(payoff(a, b, pure1(x), s2) <= v for x in PURE1)


def kuhn_value(a, b):
    if b <= a:
        return -b * b / (6 * (2 * a + b))
    if b <= 2 * a:
        return -b * (2 * a - b) / (6 * (2 * a + b))
    return F(0)


def main():
    one = F(1)
    # (1) the essential matrix
    rows = [(0, 0, 1), (0, 0, 2), (0, 1, 1), (0, 1, 2), (2, 0, 1), (2, 0, 2), (2, 1, 1), (2, 1, 2)]
    cols = [(0, 0, 3), (0, 1, 3), (2, 0, 3), (2, 1, 3)]
    table = [[0, 0, -1, -1], [0, 1, -2, -1], [-1, -1, 1, 1], [-1, 0, 0, 1],
             [1, -2, 0, -3], [1, -1, -1, -3], [0, -3, 2, -1], [0, -2, 1, -1]]
    bad = [(x, y) for i, x in enumerate(rows) for j, y in enumerate(cols)
           if 6 * payoff(one, one, pure1(x), pure2(y)) != table[i][j]]
    check("essential matrix: 6 x payoff equals Kuhn's p. 99 table on his 8 rows and 4 columns", not bad,
          f"{32 - len(bad)} of 32 entries agree")
    # (2) II's strategy
    vals = {x: payoff(one, one, pure1(x), KUHN_II) for x in PURE1}
    check("II's strategy holds all 27 pure strategies of I to at most -1/18", all(v <= V for v in vals.values()))
    tight = sorted(x for x, v in vals.items() if v == V)
    check("equality exactly on Kuhn's 8 essential rows", tight == sorted(rows), f"tight rows {tight}")
    # (3) I's family
    grid = [F(i, 30) for i in range(0, 11)]  # 0, 1/30, ..., 1/3
    check("the family guarantees -1/18 against all 64 pure strategies of II (alpha in a grid of [0, 1/3], k = 1)",
          all(guarantees1(one, one, kuhn_I(al, F(1)), V) for al in grid))
    check("at 3 alpha = 1 the call with the 3 is free (k in {0, 1/4, 1/2, 3/4, 1})",
          all(guarantees1(one, one, kuhn_I(F(1, 3), k), V) for k in [F(0), F(1, 4), F(1, 2), F(3, 4), F(1)]))
    check("below 3 alpha = 1 the call with the 3 is forced (alpha = 1/6, k = 0 fails)",
          not guarantees1(one, one, kuhn_I(F(1, 6), F(0)), V))
    check("II's strategy is pinned: moving any coordinate by 1/10 lets some pure strategy of I earn more",
          all(not guarantees2(one, one, ([KUHN_II[0][c] + (d if (i, c) == (0, cc) else 0) for c in CARDS],
                                        [KUHN_II[1][c] + (d if (i, c) == (1, cc) else 0) for c in CARDS]), V)
              for i in (0, 1) for cc in CARDS for d in (F(1, 10), F(-1, 10))
              if 0 <= KUHN_II[i][cc] + d <= 1))
    # (4) the basic strategies
    basic1 = [
        {(0, 0, 1): F(2, 3), (0, 1, 1): F(1, 3)},
        {(0, 0, 1): F(1, 3), (0, 1, 2): F(1, 2), (2, 0, 1): F(1, 6)},
        {(0, 0, 1): F(5, 9), (0, 1, 2): F(1, 3), (2, 1, 1): F(1, 9)},
        {(0, 0, 1): F(1, 2), (0, 1, 2): F(1, 3), (2, 1, 2): F(1, 6)},
        {(0, 0, 2): F(2, 5), (0, 1, 1): F(7, 15), (2, 0, 1): F(2, 15)},
        {(0, 0, 2): F(1, 3), (0, 1, 1): F(1, 2), (2, 0, 2): F(1, 6)},
        {(0, 0, 2): F(1, 2), (0, 1, 1): F(1, 3), (2, 1, 1): F(1, 6)},
        {(0, 0, 2): F(4, 9), (0, 1, 1): F(1, 3), (2, 1, 2): F(2, 9)},
        {(0, 0, 2): F(1, 6), (0, 1, 2): F(7, 12), (2, 0, 1): F(1, 4)},
        {(0, 0, 2): F(5, 12), (0, 1, 2): F(1, 3), (2, 1, 1): F(1, 4)},
        {(0, 0, 2): F(1, 3), (0, 1, 2): F(1, 3), (2, 1, 2): F(1, 3)},
        {(0, 1, 2): F(2, 3), (2, 0, 2): F(1, 3)},
    ]
    basic2 = [{(0, 0, 3): F(1, 3), (0, 1, 3): F(1, 3), (2, 0, 3): F(1, 3)}, {(0, 0, 3): F(2, 3), (2, 1, 3): F(1, 3)}]
    ok_sum = all(sum(p.values()) == 1 for p in basic1 + basic2)
    check("the fourteen basic strategies are probability vectors", ok_sum)
    ok1 = all(all(sum(w * payoff(one, one, pure1(x), pure2(y)) for x, w in p.items()) >= V for y in PURE2) for p in basic1)
    check("each of Kuhn's twelve basic strategies (A)-(L) guarantees -1/18 against all 64 columns", ok1)
    ok2 = all(all(sum(w * payoff(one, one, pure1(x), pure2(y)) for y, w in q.items()) <= V for x in PURE1) for q in basic2)
    check("each of II's two basic strategies holds all 27 rows to -1/18", ok2)
    plans_ok = True
    for p in basic1:
        rb = [sum(w for x, w in p.items() if x[c] == 2) for c in CARDS]
        rc = [sum(w for x, w in p.items() if x[c] == 1) for c in CARDS]
        al = rb[0]
        plans_ok &= (rb == [al, 0, 3 * al] and rc == [0, al + F(1, 3), 1 - 3 * al] and 0 <= al <= F(1, 3))
    check("the twelve realization plans lie on the segment (alpha, 0, 3 alpha), (0, alpha + 1/3, 1 - 3 alpha)", plans_ok)
    margs_ok = all([sum(w for y, w in q.items() if y[c] >= 2) for c in CARDS] == KUHN_II[0]
                   and [sum(w for y, w in q.items() if y[c] in (1, 3)) for c in CARDS] == KUHN_II[1] for q in basic2)
    check("II's two basic strategies have Kuhn's marginals", margs_ok)
    # (5) the general stakes
    samples = {"b < a": [(F(2), F(1)), (F(3), F(1)), (F(7), F(3)), (F(10), F(9))],
               "b = a": [(F(1), F(1)), (F(5), F(5))],
               "a < b < 2a": [(F(2), F(3)), (F(4), F(5)), (F(3), F(5)), (F(10), F(19))],
               "b = 2a": [(F(1), F(2)), (F(3), F(6))],
               "b > 2a": [(F(1), F(3)), (F(2), F(7)), (F(1), F(10)), (F(5), F(11))]}
    for region, pts in samples.items():
        for a, b in pts:
            d = 2 * a + b
            v = kuhn_value(a, b)
            if b <= a:
                s1 = ([b / d, F(0), F(1)], [F(0), 2 * a / d, F(1)])
                s2 = ([b / d, F(0), F(1)], [F(0), (2 * a - b) / d, F(1)])
                check(f"Case 1 witnesses at a = {a}, b = {b} guarantee {v}",
                      guarantees1(a, b, s1, v) and guarantees2(a, b, s2, v))
            if a <= b <= 2 * a:
                s1 = ([F(0)] * 3, [F(0), (2 * a - b) / d, F(1)])
                lo, hi = (2 * a - b) / d, b / d
                ok3 = guarantees1(a, b, s1, v) and all(
                    guarantees2(a, b, ([b / d, F(0), F(1)], [F(0), eta, F(1)]), v) for eta in (lo, hi, (lo + hi) / 2))
                check(f"Case 3 witnesses at a = {a}, b = {b} guarantee {v} (eta at both ends and the middle)", ok3)
            if 2 * a <= b:
                check(f"Case 4 witnesses at a = {a}, b = {b} guarantee 0",
                      guarantees1(a, b, ([F(0)] * 3, [F(0), F(0), F(1)]), F(0))
                      and guarantees2(a, b, ([F(0), F(0), F(1)], [F(0), F(0), F(1)]), F(0)))
    # (6) the printed interval
    a, b = F(2), F(3)
    d = 2 * a + b
    printed_hi = (a + b) / d
    check("Kuhn's printed Case 3 upper end (a + b)/(2a + b) fails at a = 2, b = 3",
          not guarantees2(a, b, ([b / d, F(0), F(1)], [F(0), printed_hi, F(1)]), kuhn_value(a, b)),
          f"eta = {printed_hi}")
    check("the corrected upper end b/(2a + b) holds there",
          guarantees2(a, b, ([b / d, F(0), F(1)], [F(0), b / d, F(1)]), kuhn_value(a, b)))
    check("just above the corrected upper end fails (eta = b/(2a + b) + 1/100)",
          not guarantees2(a, b, ([b / d, F(0), F(1)], [F(0), b / d + F(1, 100), F(1)]), kuhn_value(a, b)))
    check("just below the corrected lower end fails (eta = (2a - b)/(2a + b) - 1/100)",
          not guarantees2(a, b, ([b / d, F(0), F(1)], [F(0), (2 * a - b) / d - F(1, 100), F(1)]), kuhn_value(a, b)))
    print(f"{len(failures)} failures")
    print("VERDICT: " + ("PASS" if not failures else "FAIL"))
    sys.exit(0 if not failures else 1)


if __name__ == "__main__":
    main()

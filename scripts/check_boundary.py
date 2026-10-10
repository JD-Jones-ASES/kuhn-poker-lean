#!/usr/bin/env python3
"""Exact independent replay of the b = 2a boundary, using only the standard library.

The evaluator branches on a reduced pure strategy of I instead of copying the
five-term Lean payoff polynomial. It checks the six-product identity on every
Boolean assignment (the identity is multi-affine), replays the five separating
pure deviations, and enumerates every vertex of the bounded five-dimensional
polytope using exact Gaussian elimination. The vertex/dimension calculation is
computational evidence; the optimality iff and certificate are Lean theorems.
"""

from fractions import Fraction as F
from itertools import combinations, product


PURE_I = tuple(product(range(3), repeat=3))  # Kuhn's coding: 0 = pass then fold, 1 = pass then call, 2 = bet


def payoff(a, b, strategy, u, v):
    total = F(0)
    for i, j in product(range(3), repeat=2):
        if i == j:
            continue
        sign = 1 if i > j else -1
        if strategy[i] == 2:
            total += (1 - v[j]) * a + v[j] * sign * (a + b)
        elif strategy[i] == 1:
            total += (1 - u[j]) * sign * a + u[j] * sign * (a + b)
        else:
            total += (1 - u[j]) * sign * a - u[j] * a
    return total / 6


def unpack(point):
    p, r, s, t, w = point
    return (p, F(0), r), (s, t, w)


def certificate(x, y, point):
    p, r, s, t, w = point
    return (2 * x[0] * (t + w - 1) + (1 - x[0]) * y[0] * r
            + x[1] * (2 * w - 1 - p - s) + (1 - x[1]) * y[1] * (r - 2 * p)
            + x[2] * (p - s - t) + 2 * (1 - x[2]) * (1 - y[2]) * p)


def constraints():
    rows = []  # dot(row, point) <= rhs, point = (p, r, s, t, w)
    for i in range(5):
        for sign, rhs in ((-1, 0), (1, 1)):
            row = [0] * 5
            row[i] = sign
            rows.append((tuple(row), rhs))
    rows.extend([((2, -1, 0, 0, 0), 0), ((-1, 0, 1, 1, 0), 0),
                 ((0, 0, 0, -1, -1), -1), ((1, 0, 1, 0, -2), -1)])
    return rows


def dot(left, right):
    return sum(a * b for a, b in zip(left, right))


def solve(rows):
    matrix = [[F(x) for x in row] + [F(rhs)] for row, rhs in rows]
    for col in range(5):
        pivot = next((i for i in range(col, 5) if matrix[i][col]), None)
        if pivot is None:
            return None
        matrix[col], matrix[pivot] = matrix[pivot], matrix[col]
        scale = matrix[col][col]
        matrix[col] = [x / scale for x in matrix[col]]
        for i in range(5):
            if i != col:
                scale = matrix[i][col]
                matrix[i] = [x - scale * y for x, y in zip(matrix[i], matrix[col])]
    return tuple(matrix[i][-1] for i in range(5))


def main():
    checks = []

    def check(label, condition):
        checks.append(bool(condition))
        print(f"[{'ok' if condition else 'FAIL'}] {label}")

    boolean_points = tuple(product((F(0), F(1)), repeat=5))
    identities = True
    for bits in product((0, 1), repeat=6):
        x, y = bits[:3], bits[3:]
        strategy = tuple(2 if x[i] else y[i] for i in range(3))
        for point in boolean_points:
            u, v = unpack(point)
            identities &= -3 * payoff(F(1), F(2), strategy, u, v) == certificate(x, y, point)
    check("six-product identity on all 2048 Boolean assignments", identities)

    separating = True
    for point in boolean_points:
        p, r, s, t, w = point
        u, v = unpack(point)
        for a in (F(1), F(7, 3)):
            tests = [((0, 0, 1), F(0)), ((0, 1, 1), a * (2 * p - r)),
                     ((0, 0, 2), a * (s + t - p)), ((2, 0, 1), 2 * a * (1 - t - w)),
                     ((0, 2, 1), a * (1 + p + s - 2 * w))]
            separating &= all(3 * payoff(a, 2 * a, pure, u, v) == rhs for pure, rhs in tests)
            for middle in (F(1, 5), F(1)):
                separating &= 3 * payoff(a, 2 * a, (0, 0, 1), (p, middle, r), v) == a * middle
    check("five separating pure strategies, including the forced middle bet", separating)

    rows = constraints()
    vertices = set()
    for active in combinations(rows, 5):
        point = solve(active)
        if point is not None and all(dot(row, point) <= rhs for row, rhs in rows):
            vertices.add(point)
    expected = {
        (F(0), F(0), F(0), F(0), F(1)),
        (F(0), F(1), F(0), F(0), F(1)),
        (F(1, 3), F(2, 3), F(0), F(1, 3), F(2, 3)),
        (F(1, 3), F(1), F(0), F(1, 3), F(2, 3)),
        (F(1, 2), F(1), F(0), F(0), F(1)),
        (F(1, 2), F(1), F(0), F(1, 4), F(3, 4)),
        (F(1, 2), F(1), F(0), F(1, 2), F(3, 4)),
        (F(1, 2), F(1), F(0), F(1, 2), F(1)),
        (F(1, 2), F(1), F(1, 2), F(0), F(1)),
    }
    check("exact vertex enumeration: nine vertices", vertices == expected)
    check("each vertex holds all 27 pure strategies of I to value zero",
          all(max(payoff(F(1), F(2), pure, *unpack(point)) for pure in PURE_I) == 0
              for point in vertices))
    interior = (F(3, 10), F(4, 5), F(3, 100), F(3, 20), F(9, 10))
    check("strict rational interior point certifies dimension five",
          all(dot(row, interior) < rhs for row, rhs in rows))

    # A direct check throughout a rational grid, including points outside the polytope.
    grid = (F(0), F(1, 3), F(1, 2), F(2, 3), F(1))
    equivalent = True
    for point in product(grid, repeat=5):
        feasible = all(dot(row, point) <= rhs for row, rhs in rows)
        optimal = all(payoff(F(1), F(2), pure, *unpack(point)) <= 0 for pure in PURE_I)
        equivalent &= feasible == optimal
    check("polytope iff all 27 best-response inequalities on 3125 rational points", equivalent)

    print("BOUNDARY: " + ("PASS" if all(checks) else "FAIL"))
    return 0 if all(checks) else 1


if __name__ == "__main__":
    raise SystemExit(main())

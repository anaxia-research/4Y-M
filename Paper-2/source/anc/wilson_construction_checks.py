"""Exact finite checks of the analytical constructions, not a Wilson gap proof."""
from collections import Counter
from fractions import Fraction as F
from itertools import product
import json


def replica_cycles(T, d, first, second):
    nodes = set(product(range(2), range(T)))
    def successor(node):
        sheet, time = node
        if time == T - 1:
            sheet ^= first
        if time == d - 1:
            sheet ^= second
        return sheet, (time + 1) % T
    lengths = []
    while nodes:
        start = next(iter(nodes))
        node, count = start, 0
        while node in nodes:
            nodes.remove(node)
            count += 1
            node = successor(node)
        assert node == start
        lengths.append(count)
    return sorted(lengths)


def check_replica():
    count = 0
    for T in (3, 4, 7, 10):
        for d in sorted({1, T // 2, T - 1}):
            for a, b in product(range(2), repeat=2):
                expected = [T, T] if a == b else [2 * T]
                assert replica_cycles(T, d, a, b) == expected
                count += 1
        V = 8 * T**3
        assert F(V, 2) * F(1, 16388 * T**3) == F(1, 4097)
    return count


def check_frustration(L):
    vertices = list(product(range(L), repeat=3))
    def step(x, i):
        return tuple((value + (j == i)) % L for j, value in enumerate(x))
    def sign(x, i):
        return 1 if i == 0 else (-1)**(x[0] if i == 1 else x[0] + x[1])
    incidence = Counter()
    for x in vertices:
        for i in range(3):
            for j in range(i + 1, 3):
                edges = [(x, i), (step(x, i), j), (step(x, j), i), (x, j)]
                value = 1
                for edge in edges:
                    value *= sign(*edge)
                    incidence[edge] += 1
                assert value == -1
    V = L**3
    assert len(incidence) == 3 * V
    assert set(incidence.values()) == {4}
    assert sum(incidence.values()) == 12 * V
    assert F(3) - F(21, 8) == F(3, 8)
    assert 54 * 8 == 432
    return 3 * V


def check_tilted_chain(theta):
    """A correlated four-state reversible kernel with exact positive spectrum."""
    states = list(product(range(2), repeat=2))
    pi = F(1, 4)
    transition = {(x, y): theta * (x == y) + (1 - theta) * pi
                  for x in states for y in states}
    S1, S2, numerator, untilted = F(0), F(0), F(0), F(0)
    for x in states:
        for y1 in range(2):
            p1 = sum(transition[x, (y1, y2)] for y2 in range(2))
            ell1 = 2 * p1
            chi2 = sum(F(1, 2) * (2 * transition[x, (y1, y2)] / p1 - 1)**2
                       for y2 in range(2))
            weight = pi * F(1, 2)
            S1 += weight * ell1**2
            numerator += weight * ell1**2 * chi2
            untilted += weight * chi2
            for y2 in range(2):
                ell2 = 2 * transition[x, (y1, y2)] / p1
                S2 += pi**2 * (ell1 * ell2)**2
    trace_P2 = sum(transition[x, y] * transition[y, x]
                   for x in states for y in states)
    assert S1 == 1 + theta**2
    assert S2 == trace_P2 == 1 + 3 * theta**2
    assert S2 / S1 == 1 + numerator / S1
    assert numerator / S1 != untilted
    return {"theta": str(theta), "tilted_chi_square": str(numerator / S1),
            "untilted_chi_square": str(untilted)}


def main():
    for B in (F(1), F(2), F(3), F(10), F(100)):
        for numerator in range(101):
            p = F(numerator, 100)
            difference = B*p/(B*p+1-p)-p/(p+B*(1-p))
            assert difference == (B*B-1)*p*(1-p)/(B+(B-1)**2*p*(1-p))
            assert difference <= (B-1)/(B+1)
    result = {
        "scope": "finite exact identities; no uniform Wilson estimate or Clay proof",
        "replica_corner_graphs": check_replica(),
        "frustrated_plaquettes": {str(L): check_frustration(L) for L in (6, 8, 10)},
        "conditional_trace_examples": [check_tilted_chain(t) for t in (F(1, 3), F(2, 5))],
        "status": "passed",
        "row_variation_examples": 505,
    }
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()

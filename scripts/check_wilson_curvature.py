"""Check the Wilson curvature proof's lattice counts and coordinate changes.

The coordinate check uses the quaternion group Q8, a noncommutative subgroup
of SU(2), with exact multiplication. It exercises each pivot of the Haar
change of variables on a sample field. The analytical argument applies to the
whole group. Run with Python 3 and the standard library.
"""
from itertools import product
import math
import random


# Magnitudes 1, 2, 3, 4 represent 1, i, j, k, respectively.
TABLE = ((1, 2, 3, 4), (2, -1, 4, -3), (3, -4, -1, 2), (4, 3, -2, -1))


def mul(*values):
    ans = 1
    for value in values:
        sign = 1 if ans * value > 0 else -1
        ans = sign * TABLE[abs(ans) - 1][abs(value) - 1]
    return ans


def inv(value):
    return value if abs(value) == 1 else -value


def build_grid(shape, periodic):
    """Return tree edges, unpaired handle edges, and ordered face pivots."""
    if not shape:
        return [], [], []
    n = shape[0]
    points = list(product(*(range(size) for size in shape[1:])))
    base_tree, handles, base_pivots = build_grid(shape[1:], periodic)

    def lift(edge):
        x, axis = edge
        return (0, *x), axis + 1

    tree = [((j, *y), 0) for y in points for j in range(n - 1)]
    tree.extend(map(lift, base_tree))
    roots = list(map(lift, handles))
    pivots = [((0, *y), i + 1, k + 1, lift(edge))
              for y, i, k, edge in base_pivots]
    for j in range(n - 1):
        for y in points:
            for k, size in enumerate(shape[1:], 1):
                if periodic or y[k - 1] < size - 1:
                    pivots.append(((j, *y), 0, k, ((j + 1, *y), k)))
    if periodic:
        roots.append(((n - 1,) + (0,) * (len(shape) - 1), 0))
        # Traverse the transverse tree away from its root. Its edges all
        # increase one coordinate, so coordinate sum orders parent first.
        for y, axis in sorted(base_tree, key=lambda entry: sum(entry[0])):
            child = list(y)
            child[axis] += 1
            pivots.append(((n - 1, *y), 0, axis + 1, ((n - 1, *child), 0)))
    return tree, roots, pivots


def check_grid(shape, periodic):
    vertices = list(product(*(range(n) for n in shape)))
    edges = {(v, i) for v in vertices for i in range(len(shape))
             if periodic or v[i] + 1 < shape[i]}
    tree, handles, pivots = build_grid(shape, periodic)
    found = {edge: 1 for edge in tree}
    rng = random.Random(35)
    actual = {e: rng.choice((-4, -3, -2, -1, 1, 2, 3, 4)) for e in sorted(edges)}
    actual.update(found)
    found.update({e: actual[e] for e in handles})
    assert len(tree) == len(vertices) - 1
    assert len(handles) == (len(shape) if periodic else 0)
    assert len(set((p, i, j) for p, i, j, e in pivots)) == len(pivots)

    def step(v, i):
        w = list(v)
        w[i] = (w[i] + 1) % shape[i]
        return tuple(w)

    for v, i, j, target in pivots:
        face = [(v, i), (step(v, i), j), (step(v, j), i), (v, j)]
        assert set(face) - found.keys() == {target}
        def face_value(links):
            a, b, c, d = (links[e] for e in face)
            return mul(a, b, inv(c), inv(d))
        desired = face_value(actual)
        solutions = []
        for q in TABLE[0] + tuple(-q for q in TABLE[0]):
            found[target] = q
            if face_value(found) == desired:
                solutions.append(q)
        assert solutions == [actual[target]]
        found[target] = solutions[0]
    assert found == actual
    print(shape, "periodic" if periodic else "free", "pivots:", len(pivots))


def main():
    c = 25 / (54 * math.pi)
    cap = math.pi**2.5 / 2
    assert 6 + 4*math.log(8**1.5/c) + 3*math.log(cap) < 33
    assert math.log(cap * 8**1.5/c) < 7.21
    assert 33 + 6 - 352/8 < -math.log(128)
    for shape in [(4,), (4, 5), (3, 4, 5), (4, 4, 4, 4), (4, 6, 4, 8)]:
        for periodic in (False, True):
            check_grid(shape, periodic)
    print("All coordinate checks and numerical constant comparisons passed.")


if __name__ == "__main__":
    main()

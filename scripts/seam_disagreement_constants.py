"""Exact constants for the conditional one-cube seam-disagreement theorem."""

from fractions import Fraction
from collections import Counter
from itertools import combinations, product
from math import prod


def check_constants():
    cutoff = Fraction(2, 5)
    defect_ratio = (1 - cutoff) / cutoff
    assert defect_ratio == Fraction(3, 2)
    # D <= 1/2 and D^2 - 4D + 1 >= 0. The polynomial decreases there.
    d = Fraction(2, 7)
    assert d < Fraction(1, 2) and d * d - 4 * d + 1 < 0

    time_factor = 8
    spatial_side = 24
    comparison = Fraction(time_factor * spatial_side, spatial_side - time_factor) ** 3
    assert comparison == 1728
    assert comparison * d**time_factor < Fraction(1, 8)
    majorant = Fraction(2048)
    assert comparison / (1 - comparison * d**time_factor) < majorant
    assert majorant * d ** (time_factor - 1) == Fraction(262144, 823543)
    assert majorant * d ** (time_factor - 1) < Fraction(1, 3)
    assert d**7 < Fraction(1, 3)


def check_rough_cell_incidence(sides):
    """Count actual square faces, including wraps of the sample torus."""
    incidences = Counter()
    for cell in product(*(range(length) for length in sides)):
        for plane in combinations(range(4), 2):
            normal_axes = [axis for axis in range(4) if axis not in plane]
            for offsets in product((0, 1), repeat=2):
                base = list(cell)
                for axis, offset in zip(normal_axes, offsets):
                    base[axis] = (base[axis] + offset) % sides[axis]
                incidences[tuple(base), plane] += 1
    assert len(incidences) == 6 * prod(sides)
    assert set(incidences.values()) == {4}


def check_cluster_and_trace_constants():
    assert Fraction(2 * 24**3, 64) == 432
    assert Fraction(432 * 4**4, 2**2) == 27648
    assert Fraction(3, 2)**4 / 6 < 1
    relaxed_probability = Fraction(53, 134)
    assert Fraction(2, 5) - relaxed_probability == Fraction(3, 670)
    d = Fraction(2, 7)
    assert (1 - relaxed_probability) / relaxed_probability == (1 + d)**2 / (1 + d*d)
    assert 28 * d**2 - 106 * d + 28 == 0
    # log(4) = 4 * (1/3 + (1/3)^3/3 + ...), so 4 log(4) > 5.
    assert 4 * Fraction(4, 3) > 5


def check_aspect_threshold():
    aspect, time_factor = 24, 18
    d = Fraction(4, 9)
    comparison = Fraction(aspect * time_factor, aspect - time_factor) ** 3
    threshold = (1 + d**2) / ((1 + d)**2 + 1 + d**2)
    assert comparison == 72**3
    assert comparison * d**time_factor < Fraction(1, 5)
    assert Fraction(5, 4) * comparison * d ** (time_factor - 1) < Fraction(1, 2)
    assert threshold == Fraction(97, 266)
    assert Fraction(1, 3) < threshold < Fraction(53, 134)
    assert Fraction(24**3, 32) == 432


def check_winding_geometry(n, period, swapped):
    """Enumerate the active two-sheet Wilson plaquettes, including seam crossings."""
    def step(site, axis):
        sheet, x, y, z, t = site
        coord = [x, y, z, t]
        if axis == 3 and t in swapped:
            sheet ^= 1
        coord[axis] = (coord[axis] + 1) % (period if axis == 3 else n)
        return (sheet, *coord)

    sites = list(product(range(2), range(n), range(n), range(n), range(period)))
    incidences = Counter()
    for site in sites:
        for i, j in combinations(range(4), 2):
            assert step(step(site, i), j) == step(step(site, j), i)
            square = [(site, i), (step(site, i), j), (step(site, j), i), (site, j)]
            parallel = [s for s, direction in square if direction == 0]
            if parallel:
                tails = {(s[0], *s[2:]) for s in parallel}
                assert len(parallel) == len(tails) == 2
            incidences.update(square)
    assert set(incidences.values()) == {6}
    assert len({(s[0], *s[2:]) for s in sites}) == 2 * n**2 * period


def check_winding_constants():
    u = Fraction(1, 16)
    assert (1 + u) / (1 - u)**3 == Fraction(4352, 3375) < Fraction(3, 2)
    assert sum([1, 3, Fraction(9, 2), Fraction(27, 6), Fraction(81, 24)]) > 16
    for b in [Fraction(1, 4), Fraction(3), Fraction(1000)]:
        assert 12*b / (12*b + 3) == 4*b / (1 + 4*b)
        assert 6*b / (4*(1+6*b)) < Fraction(1, 4)
    for cuts in [set(), {1}, {3}, {1, 3}]:
        check_winding_geometry(4, 4, cuts)


if __name__ == "__main__":
    check_constants()
    for box in [(4, 4, 4, 4), (4, 6, 4, 8)]:
        check_rough_cell_incidence(box)
    check_cluster_and_trace_constants()
    check_aspect_threshold()
    check_winding_constants()
    print("Seam, winding, aspect ratio, cluster and trace checks passed. The physical Wilson seam bound remains open.")

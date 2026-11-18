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


if __name__ == "__main__":
    check_constants()
    for box in [(4, 4, 4, 4), (4, 6, 4, 8)]:
        check_rough_cell_incidence(box)
    check_cluster_and_trace_constants()
    check_aspect_threshold()
    print("Seam, aspect ratio, cluster and trace constants passed. The Wilson seam probability remains open.")

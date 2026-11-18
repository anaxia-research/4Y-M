"""Exact arithmetic and geometry checks for the seam and unequal-coupling estimates."""

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


def check_anisotropic_constants():
    """Check the scalar bounds used in the unequal-coupling and time limits."""
    neighborhood_size = 80
    small_weight = Fraction(1, 10**6)
    # e^3 > sum_{j=0}^4 3^j/j! > 16, so e^18 > 16^6.
    exp_three_lower = 1 + 3 + Fraction(9, 2) + Fraction(27, 6) + Fraction(81, 24)
    assert exp_three_lower > 16
    assert Fraction(1, 16**6) < Fraction(1, 8)
    assert 4 / Fraction(7, 8)**3 < 6
    assert Fraction(6, 16**6) < small_weight
    # The geometric tail bound gives exp(x)-1 <= x/(1-x), 0 <= x < 1.
    assert (1 + small_weight)**4 / (1 - small_weight) < 4
    # e < 3 by using j! >= 2^(j-1) in its series (strict for j >= 3).
    assert 4 * small_weight < Fraction(1, 2 * 9 * neighborhood_size**2)
    # At A = a_0, A e^2 = 1/(2*80^2). Check the weighted rooted sum.
    weighted_activity = Fraction(1, 2 * neighborhood_size**2)
    rooted_sum = weighted_activity / (1 - neighborhood_size**2 * weighted_activity)
    assert rooted_sum == Fraction(1, neighborhood_size**2)
    assert neighborhood_size * rooted_sum <= 1
    # At a common cluster-size cutoff, the two periods contribute 2*6 and 12.
    assert 2 * (3 + 3) + 2 * (3 + 3) == 24
    assert 2 * 24 == 48
    assert Fraction(97, 169) / (1 + Fraction(97, 169)) == Fraction(97, 266)
    # In continuous time, t*h -> 12 B and epsilon^2 <= 2 B*kappa/3.
    assert 18 * Fraction(2, 3) == 12
    assert Fraction(1, 4 * 12) == Fraction(1, 48)
    epsilon_bound = Fraction(1, 50)
    assert Fraction(2, 3) * small_weight / 12 < epsilon_bound**2
    variance_bound = Fraction(1, 4) - 2 * epsilon_bound - Fraction(17, 4) * epsilon_bound**2
    assert variance_bound == Fraction(2083, 10000) > Fraction(1, 5)
    assert Fraction(4, 2) / Fraction(1, 5) == 10


def anisotropic_mark_graph(sides, period):
    """Build column and plaquette marks from actual periodic spatial links."""
    sites = list(product(*(range(length) for length in sides)))
    parallel_edges = list(product(sites, range(3)))
    endpoints = {}

    def step(site, axis):
        target = list(site)
        target[axis] = (target[axis] + 1) % sides[axis]
        return tuple(target)

    def column_endpoints(edges, slab):
        return {
            (end, edge)
            for end in (slab, (slab + 1) % period)
            for edge in edges
        }

    for slab in range(period):
        for site, axis in parallel_edges:
            column = (slab, "column", site, (axis,))
            endpoints[column] = column_endpoints([(site, axis)], slab)
        for site in sites:
            for first, second in combinations(range(3), 2):
                edges = [
                    (site, first),
                    (step(site, first), second),
                    (step(site, second), first),
                    (site, second),
                ]
                plaquette = (slab, "plaquette", site, (first, second))
                endpoints[plaquette] = column_endpoints(edges, slab)

    marks_at_endpoint = {}
    for mark, support in endpoints.items():
        for endpoint in support:
            marks_at_endpoint.setdefault(endpoint, set()).add(mark)
    return endpoints, marks_at_endpoint


def check_anisotropic_incidence(sides, period, graph):
    """Check the incidence count and closed neighborhood bound on a sample."""
    endpoints, marks_at_endpoint = graph
    volume = prod(sides)
    counts = Counter(mark[1] for mark in endpoints)
    assert counts == {"column": 3 * volume * period, "plaquette": 3 * volume * period}
    assert len(marks_at_endpoint) == 3 * volume * period
    assert {len(incident) for incident in marks_at_endpoint.values()} == {10}
    for mark, support in endpoints.items():
        assert len(support) == (2 if mark[1] == "column" else 8)
        closed_neighbors = set().union(*(marks_at_endpoint[endpoint] for endpoint in support))
        assert mark in closed_neighbors and len(closed_neighbors) <= 80


def check_anisotropic_time_cover(sides, period):
    """Check local lifting through the time seam on two periodic graphs."""
    base = anisotropic_mark_graph(sides, period)
    cover = anisotropic_mark_graph(sides, 2 * period)
    check_anisotropic_incidence(sides, period, base)
    check_anisotropic_incidence(sides, 2 * period, cover)

    def local_marks(graph, root, radius):
        endpoints, marks_at_endpoint = graph
        found = {root}
        for _ in range(radius):
            found = {
                neighbor
                for mark in found
                for endpoint in endpoints[mark]
                for neighbor in marks_at_endpoint[endpoint]
            }
        return found

    origin = (0, 0, 0)
    radius = (period - 1) // 4
    for kind, axes in [("column", (0,)), ("plaquette", (0, 1))]:
        root = (period - 1, kind, origin, axes)
        downstairs = local_marks(base, root, radius)
        for lifted_slab in (period - 1, 2 * period - 1):
            upstairs = local_marks(cover, (lifted_slab, kind, origin, axes), radius)
            projected = {(mark[0] % period, *mark[1:]): mark for mark in upstairs}
            assert len(projected) == len(upstairs)
            assert set(projected) == downstairs
            downstairs_endpoints = set().union(*(base[0][mark] for mark in downstairs))
            upstairs_endpoints = set().union(*(cover[0][mark] for mark in upstairs))
            assert len(downstairs_endpoints) == len(upstairs_endpoints)
            for mark, lift in projected.items():
                assert {(slab % period, edge) for slab, edge in cover[0][lift]} == base[0][mark]


def check_projected_trace_example():
    """A finite spectral illustration, with no Wilson dynamics assumed."""
    singlet = [Fraction(1)] + [Fraction(1, 10)] * 30
    unprojected = singlet + [Fraction(9, 10)]

    def defect_ratio(spectrum):
        return sum(spectrum)**2 / sum(value**2 for value in spectrum)

    projected_ratio = defect_ratio(singlet)
    raw_ratio = defect_ratio(unprojected)
    assert raw_ratio == Fraction(2401, 211)
    assert projected_ratio == Fraction(160, 13)
    assert 1 < raw_ratio < projected_ratio <= raw_ratio**2


if __name__ == "__main__":
    check_constants()
    for box in [(4, 4, 4, 4), (4, 6, 4, 8)]:
        check_rough_cell_incidence(box)
    check_cluster_and_trace_constants()
    check_aspect_threshold()
    check_winding_constants()
    check_anisotropic_constants()
    for spatial_box, time_period in [((4, 4, 4), 8), ((4, 5, 6), 12)]:
        check_anisotropic_time_cover(spatial_box, time_period)
    check_projected_trace_example()
    print("Exact arithmetic, periodic incidence and time-cover checks passed.")
    print("The unequal-coupling estimate has explicit hypotheses. The isotropic weak-coupling seam bound remains open.")

"""Exact constants for the conditional one-cube seam-disagreement theorem."""

from fractions import Fraction


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


if __name__ == "__main__":
    check_constants()
    print("Exact seam-disagreement constants passed. Wilson probability is an input.")

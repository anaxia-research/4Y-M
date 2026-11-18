"""Exact rational certificates for the single-cube reduction, not a Wilson bound."""
from fractions import Fraction as F
from math import factorial
import json

def bounds(y, m):
    s = sum((y ** k / factorial(k) for k in range(m + 1)), F(0))
    assert 0 <= y < m + 2
    return s, s + y ** (m + 1) / factorial(m + 1) / (1 - y / (m + 2))

def main():
    x = F(1,8192)
    assert 2*x - 3*x*x - F(1,4097) == F(4093,274945015808)
    assert 64*252 < 127**2
    assert F(252,251) <= F(127,126)
    _, upper = bounds(F(64,4160),4)
    lower, _ = bounds(F(64,4159),4)
    assert 4160*(upper-1)**2 < F(99991,100000) < 1
    assert 4159*(lower-1)**2 > F(50007,50000) > 1
    _, mass_upper = bounds(F(677,1000),8)
    assert mass_upper < F(246,125) < F(63,32)
    print(json.dumps({"status":"passed", "arithmetic":"exact rational",
        "scope":"finite constants only; neither weak-coupling Wilson datum nor Clay mass gap proved",
        "purity_margin":str(2*x-3*x*x-F(1,4097)),
        "fixed_point_bracket":["1/4160","1/4159"],
        "mass_log_lower_bound":"677/1000"},indent=2))

if __name__ == "__main__":
    main()

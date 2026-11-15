"""Exact finite checks for the 15 November proof progress.

These are arithmetic examples, not Monte Carlo evidence for a Yang--Mills gap.
The infinite-sequence ascent statement is checked separately by Lean.
"""
from fractions import Fraction as F
from math import factorial
from pathlib import Path
import json
import random

ROOT = Path(__file__).resolve().parents[1]


def main():
    a, c, q = F(1683, 100), F(9, 10), F(187, 200)
    initial = F(1, 20)
    assert a * initial == c * q
    assert c * (1 - c) / a == F(3, 561)
    z = c * q
    saturation = []
    for n in range(7):
        assert z == c * q ** (2 ** n)
        saturation.append({"step": n, "envelope_equals_sequence": True})
        error = c * (1 - c) * q ** (2 ** (n + 1))
        z = z * z + error
    rng = random.Random(20261115)
    samples = 0
    for _ in range(80):
        z = c * q * F(rng.randrange(11), 10)
        for n in range(5):
            assert 0 <= z <= c * q ** (2 ** n)
            error = c * (1 - c) * q ** (2 ** (n + 1)) * F(rng.randrange(11), 10)
            z = z * z + error
            assert z <= c * q ** (2 ** (n + 1))
            samples += 1

    # An admissible geometric error sequence need not satisfy a physical
    # exponential envelope. y_(n+1)=epsilon_n obeys the upper recurrence.
    geometric_failure = None
    for n in range(12):
        y = F(1, 1000) * F(1, 2) ** n
        if a * y > c * q ** (2 ** n):
            geometric_failure = n
            break
    assert geometric_failure is not None

    transport_cases = 0
    for blocking in [2, 3, 5]:
        for t in [3 * blocking, 7 * blocking]:
            volume = (6 * blocking) * (8 * blocking) * (10 * blocking)
            alpha, fc_t, fc_2t = F(7, 13), F(4, 9), F(5, 17)
            rem_t, rem_2t = F(2, 11), F(-3, 19)
            fine_t = alpha * volume * t + fc_t + rem_t
            fine_2t = alpha * volume * 2 * t + fc_2t + rem_2t
            assert 2 * fine_t - fine_2t == 2 * fc_t - fc_2t + 2 * rem_t - rem_2t
            gamma_c, eta = F(1, 100), F(1, 100000)
            yf = 2 * (gamma_c / blocking ** 3 + eta) * (96 * t) ** 3
            yc = 2 * gamma_c * (96 * F(t, blocking)) ** 3
            assert yf == yc + 2 * eta * (96 * t) ** 3
            transport_cases += 1

    # Worst signs attain the loss from two separate free-energy bounds.
    eps, t, volume = F(1, 1000000), 12, 1000
    rem_t, rem_2t = eps * volume * t, -eps * volume * 2 * t
    defect = 2 * rem_t - rem_2t
    assert defect == 4 * eps * volume * t
    assert 2 * defect / volume * (96 * t) ** 3 == 8 * eps * 96 ** 3 * t ** 4

    # Independent exact inequality for the spectral-retention counterexample:
    # exp(20)>20^13/13!>10*96^3 implies 2 exp(-20)<1/(5*96^3).
    exp_lower = F(20 ** 13, factorial(13))
    assert exp_lower > 10 * 96 ** 3
    for n in [21, 40, 100]:
        assert F(20, n * n) / F(1, n * n) == 20
        assert F(1, n * n) > 0

    # Sharp first-step reserve among envelopes touching the initial datum:
    # c=u/q forces the largest admissible e0 to be u(q-u).
    u = a * initial
    for target_q in [F(9, 10), F(187, 200), F(19, 20), F(99, 100)]:
        coefficient = u / target_q
        reserve = coefficient * (1 - coefficient) * target_q ** 2
        assert reserve == u * (target_q - u)
        assert u * u + reserve == coefficient * target_q ** 2

    data = {
        "kind": "exact arithmetic checks; no Yang-Mills measurements",
        "ascent_parameters": {"A": str(a), "c": str(c), "q": str(q),
                              "initial_y": str(initial), "error_prefactor": str(F(3, 561))},
        "saturated_steps": saturation,
        "random_exact_induction_steps": samples,
        "geometric_error_envelope_failure_step": geometric_failure,
        "exact_bulk_cancellation_and_scaling_cases": transport_cases,
        "separate_remainder_precision": "8 * epsilon * 96^3 * T^4",
        "exp20_rational_lower_bound": str(exp_lower),
        "spectral_retention_counterexample_rational_bound": "PASS",
        "base_main": "2e36be0f89e50aeabeb3844418cf9ad58b1e7fd9",
        "paper_revision": "50095e99694feea0d72a9cd1495ea4d88efddb4e",
        "unconditional_yang_mills_gap": "not proved",
    }
    output = ROOT / "research/2026-11-15/verification.json"
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    print(f"PASS: {samples} exact induction steps, {transport_cases} transport cases, spectral bounds and obstructions.")


if __name__ == "__main__":
    main()

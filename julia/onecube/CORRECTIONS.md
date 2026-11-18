# Software corrections of 18 November 2026

These changes repair the verification software. They do not establish the
uniform weak-coupling Wilson bound, a continuum construction, or the Clay
Yang–Mills mass gap.

## J5 root assertion

The earlier recorded run reported **273 PASS and 1 FAIL**. The failed assertion
was the source sentence `T_0 >= 116.7` for the root of

```text
T^3 = (1 - 7.65/T) * 10^9 / (21.97 * (log(2 * 10^9) + 5.42)).
```

That assertion is false: the corrected enclosure is
`116.5888 < T_0 < 116.5889` (approximately `116.5888672343048`). It is not
silently counted as a successful check of the original assertion. The revised
test verifies a negative left bracket, a positive right bracket, and a positive
lower bound for the derivative throughout `[100,130]`. Continuity and strict
monotonicity therefore give exactly one root in that interval. Bisection keeps
both bracket endpoints, and the tested root enclosure uses the lower endpoint
for lower bounds and the upper endpoint for upper bounds. A separate check
certifies `T_0 < 116.7`, explicitly recording the original assertion's failure.

## Rational inputs and directed rounding

Rounding a numerator and its denominator separately in the same direction does
not generally bound their quotient. At 256-bit precision, the former lower
endpoint of `(2^300 + 1)/(2^300 + 2)` was `1`, although the rational is less than
`1`. The reciprocal also exposes an invalid upper endpoint. The constructor now
encloses each integer and divides the resulting intervals with the appropriate
cross endpoints. Regression tests include both ratios, their negatives, zero,
and larger integers, comparing endpoints to exact rational values.

## Failure handling

The earlier one-cube runner printed a failed check and nevertheless exited
successfully. It now raises an error if any rigorous check fails and exports
`Enclosures.lean` only after all such checks pass. The rational interval
regression tests also fail the run on any failed assertion. Numerical sanity
experiments remain separately identified as experiments, not proofs.

The older `julia/constants.jl` reports failures in its printed output. The new
`scripts/run_julia_constants.py` driver checks its process status, rejects
`FAIL` lines, and requires at least one successful check. It must be used when
an automated verification needs a reliable exit status.

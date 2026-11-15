# Progress toward the unconditional Yang–Mills problem

**15 November 2026. The unconditional mass gap is not proved.** Three parallel audits examined the current 170-page manuscript, the Lean project, and the published continuum-construction interfaces. This directory records the deductions and the remaining model estimate.

The source baseline is main commit `2e36be0f89e50aeabeb3844418cf9ad58b1e7fd9` and paper commit `50095e99694feea0d72a9cd1495ea4d88efddb4e`. Older, longer manuscript branches were not treated as the current paper. Existing dense-core gap transfer, spectral tuning, and the zero-error ascent were identified as existing results and are not claimed again as new work.

## What changed

| Result | Verification level | Meaning |
|---|---|---|
| [Error-stable ascent](../../YangMills/ErrorStableAscent.lean) | Six Lean theorem declarations; compilation and axiom checks are recorded by the [proof workflow](https://github.com/anaxia-research/4Y-M/actions/workflows/proof-progress.yml) | The quadratic and exponential ascent tolerate a specified nonzero error budget. Every model-dependent recurrence and error estimate remains an explicit hypothesis. |
| [Scalar thermal-defect transport](rg/RG_THERMAL_DEFECT_AND_ERROR_BUDGET.md) | Written proof and exact arithmetic checks | Bulk vacuum terms cancel in a two-time partition-function ratio. A scalar remainder bound can suffice for base-scale transport without transporting every observable. The actual weak-coupling comparison is still missing. |
| [Continuum-construction interface](literature/construction-to-theorem-f-interface.md) | Pinned primary-source statements and written mathematical adapters | Full support, phase continuity, adjoints, and reciprocal integer spacings have explicit source chains. Real-token and RP/Fubini adapters address particular interface differences. The external full proof was not rebuilt here. |
| [General spacing and moving tests](os/continuum-interface-and-spectral-retention.md) | Written proofs | Sparse integer denominators do not require an arithmetic-progression subsequence. Full distributional ultraviolet convergence also controls smoothly moving tests on a common separated compact set. |
| [Finite-energy retention](os/continuum-interface-and-spectral-retention.md#3-exact-finite-energy-retention-criterion-for-a-prescribed-observable) | Written proof, exact counterexample bounds, illustrative numerical values | A two-time correlation lower bound prevents a prescribed observable from losing all finite-energy spectral weight. A gap upper estimate alone does not ensure that nontriviality. |

Only the six ascent declarations are new Lean formalizations in this update. The interface and spectral lemmas are written mathematical proofs, not additional machine-checked construction theorems. The finite examples are not measurements of the Wilson model.

## The explicit error budget

Let `A=16.83`, `0<c,q<1`, and suppose a nonnegative sequence satisfies

```text
y_(i+1) <= A y_i^2 + epsilon_i,
A y_0 <= c q,
A epsilon_i <= c(1-c) q^(2^(i+1)).
```

Then

```text
A y_i <= c q^(2^i).
```

The exponential-recurrence version uses the existing bound `16(exp(y)-1)^2 <= A y^2` and proves its range `y_i<=1/20` within the induction, provided `c q<=A/20`. At the original base value `y_0=1/20`, the choice `c=9/10`, `q=187/200` has a genuine reserve

```text
epsilon_i <= (3/561) (187/200)^(2^(i+1)).
```

When the same trace-to-spectrum estimates hold, the resulting physical gap lower bound is `-log(q)/t0`. Errors exponential in `2^i` are exponential in physical time because that time doubles at each step. A constant or merely geometric tolerance in the step index does not guarantee this decay; the companion note supplies explicit scalar counterexamples.

For a fixed normalized initial value `u=A y_0` and an envelope touching it, `c=u/q`. Its first-step reserve is exactly `u(q-u)` in normalized units, or `y_0(q-u)` in the original error. This is the sharp reserve within that specific family of touching envelopes: the saturated first recurrence attains it. It is not an optimality theorem for every possible ascent argument.

## The remaining Yang–Mills estimate

With representation dimension `m`, the external action convention and the paper's convention agree at `kappa=m^2 beta`. On the actual couplings of the constructed family, a sufficient raw-partition target is

```text
2 log Z_kappa(s,T0) - log Z_kappa(s,2T0)
    <= y0 V(s) / (2 (96 T0)^3),
0 < y0 <= 1/20,
3 <= T0 <= d_k t0,
2 T0 <= s_j < 48 T0  (j=1,2,3).
```

It must hold on every required rectangle at the **same actual coupling**, uniformly along the relevant cutoffs and volume sequence. A separately retuned construction on each rectangle does not supply it. This estimate includes a neutral-sector gap and a count of states; a center-twist calculation or a one-loop running-coupling formula does not replace either.

If only separate free-energy remainder bounds `|R(s,t)|<=epsilon V(s)t` are available, their worst-case contribution to the dimensionless base invariant is `8 epsilon 96^3 T^4`. Thus those separate bounds would need precision of order `T^-4` to preserve a fixed margin. Controlling the thermal difference directly can retain cancellations that the separate bounds discard. This is a sufficient precision requirement for that comparison, not a lower bound on the true error.

The audits give no unconditional estimate of this thermal defect at weak coupling. They also do not constitute a complete executable adapter for the external construction. These are the remaining tasks; there is no claimed closure of the Clay problem.

## Reproduce and inspect

```sh
python scripts/check_closure_progress.py
lake exe cache get
lake build
lake env lean scripts/ErrorStableAxioms.lean
```

The Python calculation checks 400 exact induction steps, six transport/scaling examples, the sharp first-step reserve, and rational bounds in the spectral example. It regenerates [verification.json](verification.json). Infinite-sequence statements are established by their Lean proofs, not by those finite checks. The six theorem dependency reports are checked against the standard axioms `propext`, `Classical.choice`, and `Quot.sound`.

The previous 170-page paper remains the manuscript baseline. This update publishes research notes, formal proofs, and checks. It creates no release or archival identifier.

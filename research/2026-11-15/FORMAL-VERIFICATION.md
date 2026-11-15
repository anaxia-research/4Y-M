# Formal verification record

Verified code commit: [`ba6b7b695cbb4d0f201912d3cfab75e672d023e8`](https://github.com/anaxia-research/4Y-M/commit/ba6b7b695cbb4d0f201912d3cfab75e672d023e8).

[Successful workflow run](https://github.com/anaxia-research/4Y-M/actions/runs/43677801260), completed 15 November 2026.

- Lean toolchain: `leanprover/lean4:v4.33.0`.
- Mathlib: `v4.33.0`, locked revision `db584cd6d46c92f209a44c0f1c829460d327499d`.
- The complete `lake build` passed, including the original project and `YangMills.ErrorStableAscent`.
- All six new theorem dependency reports contain only `propext`, `Classical.choice`, and `Quot.sound`.
- The exact Python checks and deterministic report regeneration passed.

The new declarations are:

```text
YangMills.ErrorStableAscent.dyadic_power_succ
YangMills.ErrorStableAscent.variable_budget_ascent
YangMills.ErrorStableAscent.error_stable_ascent
YangMills.ErrorStableAscent.rescale_recurrence
YangMills.ErrorStableAscent.scaled_error_stable_ascent
YangMills.ErrorStableAscent.exponential_error_stable_ascent
```

The result is a formal proof of the stated implications for real sequences. Their recurrence, range, base-scale, and error estimates are explicit hypotheses. An axiom audit does not turn those hypotheses into proved facts about the Yang–Mills measure.

The continuum-interface, thermal-transport, and spectral-retention notes contain written mathematical arguments. They were reviewed separately and are not included in the six-declaration Lean claim. The external construction was inspected at source level and through its published assessment; its entire build was not rerun in this task.

Local installation of the pinned Lean toolchain failed because the disk lacked space for extraction. Verification was therefore performed by the GitHub runner using the repository's exact pinned versions. The failed local installation is not counted as a completed check.

Subsequent documentation wording and this verification record do not change the checked Lean or Python sources. No release was made.

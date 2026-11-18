# Complete theorem-dependency audit

Use the Lean toolchain and Mathlib revision pinned by this repository. From
the repository root, run:

```text
lake exe cache get
lake build
python scripts/test_all_axioms.py
python scripts/run_all_axioms.py
```

The final command executes `lake env lean scripts/AllAxioms.lean`, records its
combined output, checks its process exit code, and validates the completed
report. Its default outputs are `verification/all-axioms.jsonl` and
`verification/all-axioms.summary.json`. A failed Lean invocation never passes
the runner, even if a partial report was printed first.

`AllAxioms.lean` enumerates the imported Lean environment and audits every
theorem whose user-facing namespace starts with `YangMills`, including private
and generated theorem declarations. It calls Lean's transitive
`collectAxioms` operation separately for each theorem. The header contains the
number of enumerated declarations; the footer reports completion. The Python
validator requires exactly that many distinct theorem records between one
header and one footer. It rejects incomplete logs, missing footers, duplicate
records, malformed JSON, error diagnostics, `sorryAx`, and any axiom other
than `propext`, `Classical.choice`, or `Quot.sound`.

The default minimum of 741 is a source-count guard for this revision. The
environment count can be higher because Lean generates auxiliary theorems.
After an intentional change that removes source theorems, review and update
this guard explicitly rather than disabling coverage checking.

For an existing log, use:

```text
python scripts/check_all_axioms.py verification/all-axioms.jsonl
```

This validates a report, not the exit status of the command that originally
produced it; the subprocess runner is therefore the preferred path.

The twelve adversarial Python validator tests passed on 18 November 2026.
The pinned Lean 4.33.0 compiler then checked all 34 project modules in dependency
order against the official pinned Mathlib cache. The complete audit passed for
all 1,192 imported theorem declarations, including private and generated
declarations, with only the three allowed standard axioms. Logs, source hashes,
compiled-artifact hashes and the summary accompany this code under verification/.
This is a complete check of the project sources, not a fresh source rebuild of
Mathlib or a formalization of the entire analytical manuscript.

An axiom audit does not discharge the hypotheses of conditional theorems.
Neither this audit nor the library's finite checks establish the uniform
weak-coupling Wilson estimate, a nontrivial continuum Yang--Mills construction,
or the Clay mass-gap theorem.

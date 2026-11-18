# Anaxia/OpenGluon run for the second Yang–Mills paper

Run date: 15 November 2026, Asia/Calcutta.

The user clarified that “ANN” referred to Anaxia/eBLLM. The local engine was inspected and its actual Yang–Mills tools were run. No artificial-neural-network training is claimed.

Engine: `C:\CLAUDE PAPERS\eBLLM`, version `3.4.1rc1`, commit `9ef0454294c8dd293f1ce9c51f7937fbc785bd97`.

Reproduction entry point: `run_anaxia_checks.py` in this directory. It reads the engine and OpenGluon checkouts, writes its records here, and does not modify either repository.

## Executed

- `anaxia routes Yang-Mills -k 20`: retrieved relevant stored construction routes.
- `anaxia superstring --target yang-mills --json`: inspected and checked stored attack records. This is not a fresh theorem-proving service call.
- OpenGluon's `check_yang_mills_one_scale.py`: passed its exact conditional-seed arithmetic checks.
- OpenGluon's `check_thermal_gap_identifiability.py`: passed 90 exact moment matches for 12 sample counts.
- eBLLM's `test_ym_blocks.py`: six tests passed, none skipped. These include sampled block scouts; they do not exhaust all boundary configurations or continuum cutoffs.
- Anaxia `certify_psd` and separate `verify_psd`: four finite rational matrix certificates passed, including the scalar pressure-budget margin and two-state spectral witnesses.

## Scope

The local latest campaign record is sequence 30, timestamp `2026-11-14T20:00:08.475397+00:00`. It says `status: unverified_proposal`, `global_status: not_closed`, and `outcome: completed`. Here “completed” describes completion of the proposal-generation job, not completion of the Clay problem. Its stated model is `anaxia-local-phi3`, with a 384-token proposal budget.

No uniform Wilson partition-function bound is supplied by that record. The precise unresolved estimate remains the equation labelled `eq:missing` in the second manuscript's TeX source. This source label is stable across pagination changes.

The obligation graph in the run script correctly refuses to certify the Clay target when the uniform Wilson seed is unknown. The graph is a dependency record, not an independent analytic proof checker.

All outputs are retained in `anaxia-run-summary.json`, `anaxia-routes.json`, `anaxia-attack-records.json`, `anaxia-finite-certificates.json`, and the associated text logs. Their passing finite checks do not establish the continuum mass gap.

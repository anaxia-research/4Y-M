# Weak Coupling and the Yang–Mills Mass Gap

Current research revision: 18 November 2026. The published-preprint v1 content
is retained and corrected where documented in the preservation manifest.

**The uniform weak-coupling Wilson bound and the Clay theorem remain unproved.**
This repository contains rigorous finite-volume results, conditional continuum
gap theorems and the supporting formal and exact-arithmetic checks.

## Current manuscript

- [PDF — 178 pages](YangMills.pdf)
- [Submission TeX ZIP](ymmdpitex.zip): select `YangMills.tex`.
- [Unpacked source](source/YangMills.tex)
- [Analytical progress and open estimates](PROGRESS.md)
- [Resubmission notes](RESUBMISSION-NOTES.md)
- [Verification scope](VERIFICATION.md)
- [Bibliography audit](BIBLIOGRAPHY-AUDIT.md)

The active Paper-2 folder contains the integrated v2, replacing the earlier
22-page draft. Earlier finite test records are retained under the dated
research folder; superseded PDF and source ZIP copies are removed from the
active branch. Git history preserves prior versions.

## Proved analytical results

The manuscript proves explicit finite-volume Wilson gaps at every finite
positive coupling for compact simple gauge groups; a single-cube datum gives
a physical gap `log(63/32)/t0` in compatible Wightman limits. Exact replica
and tilted-conditional identities isolate the required Wilson estimate.

For the actual SU(2) vacuum, every one-link prefix conditional has Poincare
constant at most `exp(12b)/3` in the unit-round S3 metric, independently of
volume and history. A tilted Fisher budget suffices for the thermal trace
criterion. The comparison is proved; the time-dependent score budget along
the tuning is not. Further proofs characterise retention by finite physical
energy spectral mass and preserve reflection positivity under spatial flow.

## Code and checks

Lean: `YangMills/`, `YangMills.lean`, `lean-toolchain`, `lake-manifest.json`.
Julia: `julia/`. Python: `scripts/`. Exact audit records: `verification/`.

The pinned compiler checked all 34 project modules. The imported-environment
audit checked 1,192 theorem declarations with only `propext`,
`Classical.choice` and `Quot.sound`. These checks concern the formal library's
actual finite and conditional statements. The new analytical Poincare,
Fisher-budget and flow arguments are not Lean-formalised, and the audit does
not establish the missing Wilson estimate or the full manuscript.

Julia runs passed 273 legacy checks, 282 directed-rounding checks, 75 rational
interval regressions and five rational certificates. Numerical sanity and
Monte Carlo routines are experiments, not analytical proofs. See the
verification report for corrections and exact scope.

```text
lake exe cache get
lake build
python scripts/run_all_axioms.py
python -m unittest discover -s scripts -p "test_*.py"
python scripts/run_julia_constants.py
julia -t 4 julia/onecube/run_all.jl
julia julia/onecube/be_certificates.jl
python scripts/check_closure_progress.py
python scripts/single_cube_constants.py
python scripts/wilson_construction_checks.py
python scripts/check_conditional_fisher.py
python scripts/package_manuscript.py --compile
```

## Related construction workspace

[Anaxia](https://github.com/anaxia-research/anaxia), formerly Open Gluon,
is the supporting construction workspace. Its proposals and finite checks
do not substitute for a proof of a missing model-dependent estimate.

No release, tag or Zenodo DOI is created for this revision.

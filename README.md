# Weak Coupling and the Yang–Mills Mass Gap

Current research revision: 18 November 2026. The published-preprint v1 content
is retained and corrected where documented in the preservation manifest.

**The uniform weak-coupling Wilson bound and the Clay theorem remain unproved.**
This repository contains rigorous finite-volume results, conditional continuum
gap theorems and the supporting formal and exact-arithmetic checks.

## Current manuscript

- [PDF — 184 pages](Paper-2/YangMills.pdf)
- [Submission TeX ZIP](Paper-2/ymmdpitex.zip): select `YangMills.tex`.
- [Unpacked source](Paper-2/source/YangMills.tex)
- [Analytical progress and open estimates](Paper-2/PROGRESS.md)
- [Resubmission notes](Paper-2/RESUBMISSION-NOTES.md)
- [Verification scope](Paper-2/VERIFICATION.md)
- [Bibliography audit](Paper-2/BIBLIOGRAPHY-AUDIT.md)

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

## Bounded seam observable

Theorem 20.1 gives a second one-cube criterion. If the Wilson-weighted probability of different seam matchings is at least 2/5 on the cube of side 24T, increasing time eightfold before enlarging space gives a physical gap of at least log(3)/(7t0) in a compatible Wightman limit. The probability lower bound along the weak-coupling tuning and nontrivial continuum existence remain open.

## Long rough clusters

On even periodic Wilson boxes, a chessboard estimate gives an exponential tail for connected rough-cell clusters of every size. Removing clusters of size at least T/2 changes the seam-disagreement probability by at most 432 T^4 (2b)^(-T/2) on a spatial cube of side 24T. The interacting SU(2) transfer trace also admits a positive finite-matrix approximation with an explicit error. The seam probability in the retained ensemble and a matching nontrivial continuum limit remain unproved.

On a spatial cube of side 24T, a seam-disagreement probability of 97/266 suffices for a physical gap of log(2)/(17t0) under the continuum transfer hypotheses. Any fixed probability above one third suffices at a corresponding fixed aspect ratio. Incompatible flat winding fields show why a lower bound conditional on every spatial field fails at fixed volume. The averaged Wilson lower bound along the tuning and continuum existence remain open.

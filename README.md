# Lattice Yang–Mills Gaps and Weak Coupling

Preprints.org revision of [Version 1](https://doi.org/10.20944/preprints202611.1282.v1), posted 12 November 2026. All six authors are retained.

The unequal-coupling theorem proves a gauge-invariant gap uniform in spatial volume at arbitrarily large temporal coupling with sufficiently small spatial coupling. At continuous time and fixed spatial spacing, the SU(2) theory has a finite-energy plaquette excitation with two-sided correlation bounds. For SU(2) at equal couplings, Appendix N determines the exact limiting gap on each fixed spatial cube with free boundary. The limit decreases inversely with the side length. The isotropic physical-scale Wilson estimate and a compatible nontrivial four-dimensional continuum limit remain open.

## Current manuscript

- [PDF (196 pages)](Paper-2/YangMills.pdf)
- [Submission source ZIP](Paper-2/texmdpi.zip) with one main.tex and the figures/ directory
- [Modular source](Paper-2/source/YangMills.tex)
- [Resubmission note](Paper-2/RESUBMISSION-NOTES.md)
- [Bibliography verification](Paper-2/BIBLIOGRAPHY-AUDIT.md)
- [Mathematical results](Paper-2/PROGRESS.md) and [verification scope](Paper-2/VERIFICATION.md)

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
python scripts/seam_disagreement_constants.py
python scripts/check_isotropic_plaquette.py
python scripts/package_manuscript.py --compile
```

## Related construction workspace

[Anaxia](https://github.com/anaxia-research/anaxia), formerly Open Gluon, is the construction workspace. [Project repository](https://github.com/anaxia-research/4Y-M).

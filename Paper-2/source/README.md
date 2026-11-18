# Lattice Yang–Mills Gaps and Weak Coupling

Research revision v2, 18 November 2026. Six-author list retained from the published preprint v1.

## Current files

- `YangMills.tex`: sole manuscript entry point; compile with pdfLaTeX.
- `sec/06d_singlecube.tex`: positive torus systems, one-cube comparison, ascent and zero–one law.
- `sec/06e_continuum.tex`: physical-gap transfer theorem and explicit Clay obligations.
- `sec/06f_replica.tex`: the exact Wilson replica response and tilted conditional trace factorisation.
- `sec/06g_kernel.tex`: an explicit finite-volume gap at every positive coupling and a gauge-invariant large-field witness for deterioration of a global kernel certificate.
- `sec/06h_retention.tex`: spectral retention and the exact Wilson Dirichlet form.
- `sec/06i_fisher.tex`: volume-independent one-link conditional Wilson comparison and the tilted score criterion.
- `app/L_flow.tex`: support-preserving regularisation and reflection-positivity error bounds.
- `app/K_singlecube.tex`: exact rational constants and the zero-eigenvalue convention.
- `anc/single_cube_constants.py`: standalone exact rational certificates.
- `PRESERVATION-MANIFEST.json`: baseline hashes and the complete modification list.
- `RESUBMISSION-NOTES.md`: version notes for the published-preprint revision.

## Mathematical scope

The single-cube theorem derives a continuum gap of at least `log(63/32)/t0` from a bound at the actual tuned Wilson couplings and a compatible Wightman limit. The replica construction identifies the precise signed covariance estimate required for that bound. The kernel witness explains the failure of a global pointwise contraction shortcut. The retention results separate a nonvacuum continuum excitation from a lower spectral gap. The actual uniform Wilson estimates and a nontrivial continuum construction for every compact simple group remain unproved. This revision is not an unconditional Clay solution.

## Data and code availability

The manuscript links the project repository, https://github.com/anaxia-research/4Y-M, and the former Open Gluon workspace now at https://github.com/anaxia-research/anaxia, for supporting code and verification records. No release or Zenodo deposit is requested for this revision.

## Compilation

From this directory run `pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error YangMills.tex` at least twice until cross-references settle. There is no table of contents and no line numbering. The revision includes native TikZ diagrams and PNG figures.







The current compiled manuscript has 187 pages. VERIFICATION.md records executed checks and formal verification status. BIBLIOGRAPHY-AUDIT.md records reference evidence. No release or DOI was created. The upload record identifies the final repository commit when the authorised push completes.

Section 20 derives the bounded seam test in sec/06j_seams.tex. Theorem 20.1 gives a second one-cube criterion. If the Wilson-weighted probability of different seam matchings is at least 2/5 on the cube of side 24T, increasing time eightfold before enlarging space gives a physical gap of at least log(3)/(7t0) in a compatible Wightman limit. The probability lower bound along the weak-coupling tuning and nontrivial continuum existence remain open.

The rough-cluster and transfer-trace proofs are in sec/20_rough_clusters.tex. On even periodic Wilson boxes, a chessboard estimate gives an exponential tail for connected rough-cell clusters of every size. Removing clusters of size at least T/2 changes the seam-disagreement probability by at most 432 T^4 (2b)^(-T/2) on a spatial cube of side 24T. The interacting SU(2) transfer trace also admits a positive finite-matrix approximation with an explicit error. The seam probability in the retained ensemble and a matching nontrivial continuum limit remain unproved.

On a spatial cube of side 24T, a seam-disagreement probability of 97/266 suffices for a physical gap of log(2)/(17t0) under the continuum transfer hypotheses. Any fixed probability above one third suffices at a corresponding fixed aspect ratio. Incompatible flat winding fields show why a lower bound conditional on every spatial field fails at fixed volume. The averaged Wilson lower bound along the tuning and continuum existence remain open.

For SU(2), integrating straight spatial winding rows compares the Wilson seam odds with the odds after pinning every holonomy in one direction to the identity. The error vanishes when n/(1+4b) - 3 log n tends to infinity. Temporal winding gives a spatial-volume-independent upper bound on the transfer spectrum outside the gauge-invariant subspace for every compact connected matrix group. At logarithmic tuning the change in the seam log odds and fixed-order gauge-invariant slice correlations upon dropping the gauge projection is smaller than every inverse power of the inverse spacing at fixed physical sizes. The remaining seam comparison and the continuum spectrum of gauge-invariant excitations are open.

The source used for online submission is flattened into a single main.tex by scripts/package_manuscript.py. The numerical constants for the unequal-coupling theorems are documented in Appendix M.

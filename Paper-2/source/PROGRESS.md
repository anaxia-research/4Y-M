# Analytical progress from the user-designated main source

Main source: the attached ymmdpitex.zip, preserved by SHA-256 in the manifest.
Title: Weak Coupling and the Yang–Mills Mass Gap.
The main source and all prior substantive mathematical sections are retained.

## Proved in this continuation

1. Every SU(2) Wilson vacuum one-link prefix conditional has density ratio
   at most exp(12b), and Poincare constant at most exp(12b)/3 in the unit-round
   S3 metric, at every finite coupling. The bound includes all link fields and
   is independent of volume and the revealed history. It is not a bound on
   label-restricted or fixed-coarse-field fibres, and does not tensorise by itself.
2. Exact tilted conditional score budgets bound the thermal trace:
   X_s(2t) <= -log(1-sum eta_j) <= (sum eta_j)/(1-sum eta_j).
   Combining this with item 1, the sufficient actual Wilson score budget is
   sum E_theta_j |grad log ell_j|^2 <= 3 exp(-12b)/8195.
   That time-dependent budget remains unproved along the continuum tuning.
3. A fixed-time correlation lower bound is equivalent to retaining positive
   spectral mass below a fixed physical energy, when norms are uniformly bounded.
   An upper bound on the energy of the whole unfiltered observable is unnecessary.
4. Spatial finite-lattice Wilson flow preserves the positive-time algebra and
   reflection positivity. Temporal heat smoothing need not preserve it, even
   for a massive free covariance. Quantitative approximation and bad-event
   moment budgets are proved with all assumptions stated.
5. Separate bulk free-energy density errors of size epsilon imply only
   psi <= 32 epsilon T^4 on the relevant cube. This route requires
   epsilon <= 1/(131104 T^4), or a stronger direct mixed-remainder estimate.

## Still not proved

The score budget or equivalent single-cube datum for the actual tuned Wilson
family, and a compatible nontrivial continuum construction with all the needed
identifications and axioms, remain unproved. No Clay solution or breakthrough
claim is made. The existing full Lean audit concerns its library's precise
finite and conditional statements; the new analytical sections are not Lean
formalised. Exact ancillary tests check finite identities, not these open inputs.

## Sources and publication

Recent primary literature, GitHub repositories and construction reports were
examined; scope is recorded in the separate literature audit. Four independent published references were added. No unpublished companion or Zenodo
DOI was introduced. No release or DOI is authorised. Repository links in the
paper are https://github.com/anaxia-research/4Y-M and
https://github.com/anaxia-research/anaxia.

## Bounded seam observable

Theorem 20.1 gives a second one-cube criterion. If the Wilson-weighted probability of different seam matchings is at least 2/5 on the cube of side 24T, increasing time eightfold before enlarging space gives a physical gap of at least log(3)/(7t0) in a compatible Wightman limit. The probability lower bound along the weak-coupling tuning and nontrivial continuum existence remain open.

## Rough plaquettes and the transfer trace

On even periodic Wilson boxes, a chessboard estimate gives an exponential tail for connected rough-cell clusters of every size. Removing clusters of size at least T/2 changes the seam-disagreement probability by at most 432 T^4 (2b)^(-T/2) on a spatial cube of side 24T. The interacting SU(2) transfer trace also admits a positive finite-matrix approximation with an explicit error. The seam probability in the retained ensemble and a matching nontrivial continuum limit remain unproved.

On a spatial cube of side 24T, a seam-disagreement probability of 97/266 suffices for a physical gap of log(2)/(17t0) under the continuum transfer hypotheses. Any fixed probability above one third suffices at a corresponding fixed aspect ratio. Incompatible flat winding fields show why a lower bound conditional on every spatial field fails at fixed volume. The averaged Wilson lower bound along the tuning and continuum existence remain open.

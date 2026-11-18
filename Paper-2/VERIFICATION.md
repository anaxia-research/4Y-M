# Verification record — 18 November 2026

This is an analytical research revision. The uniform Wilson bound along the
continuum tuning, the full continuum construction and the Clay mass-gap theorem
are not proved. The code does not certify those missing inputs.

## Executed checks

- Julia 1.13.4, downloaded from the official distribution and matched to its
  published SHA-256 checksum: 273 legacy constant checks passed.
- One-cube directed-rounding program: 282 checks passed, zero failed.
- Exact rational interval-regression assertions: 75 passed.
- Exact rational line-field certificate program: five certificates passed.
- Numerical sanity routines completed, including Monte Carlo examples. These
  are experiments, not proofs and not part of the analytical argument.
- Python: 17 failure-handling/axiom-validator tests passed; 400 exact induction
  steps and six transport examples passed.
- Exact single-cube constants, 44 replica corner-graph tests, 5,184 frustrated
  plaquettes two correlated tilted-trace examples and 505 exact row-variation comparisons passed.
- The complete-axiom driver passed a Lean 4.33.0 core-only smoke test. The
  twelve adversarial validator tests reject admitted/custom axioms and incomplete
  reports. This smoke test is not a complete-project build.

## Full Lean status

The pinned Lean 4.33.0 compiler successfully checked all 34
project modules, including the root import. The source contains 741 named
theorem/lemma declarations in 33 files below YangMills. Mathlib is pinned to
db584cd6d46c92f209a44c0f1c829460d327499d. All 8,690 official dependency cache
artifacts were retrieved and extracted successfully.

Every project module was compiled directly, in dependency order, with the same
pinned compiler and dependency search paths. The normal Lake build was replaced
after a slow artifact scan; its orphaned workers were stopped before the direct
checks continued. The per-module report records source hashes, compiled-artifact
hashes and successful compiler exits. This is a source compilation of the whole
project, not a claim to have rebuilt Mathlib itself from source.

The complete imported-environment audit checked all
1192 theorem declarations in the YangMills user
namespace, including private and generated declarations. Every dependency is
among propext, Classical.choice and Quot.sound; no sorryAx or custom axiom is
accepted. The full report and summary accompany the code.

These checks concern the formal library's actual statements, including their
hypotheses. The conditional-Poincare, Fisher-budget and flow arguments added in this continuation are analytical proofs and are not included in that Lean audit. These checks do not formalise the entire analytical manuscript or establish
the missing Wilson bound and Clay theorem.

## Repairs made before the fresh Julia run

The previous J5 assertion T0 >= 116.7 was false. Its corrected root bracket is
116.5888 < T0 < 116.5889, with bracket signs and monotonicity verified. The
original failure is recorded in julia/onecube/CORRECTIONS.md.

The rational interval constructor now encloses numerator and denominator before
division. Failed rigorous checks produce a failing process exit. A thread-index
error in the optional sanity program was corrected by assigning one output slot
per loop iteration rather than indexing by a potentially migrating thread ID.

## Manuscript and references

The manuscript compiles with no unresolved references, duplicate labels,
overfull boxes or oversized floats. Every page was inspected at contact-sheet
scale, with enlarged inspection of the cover and new mathematical pages.
Bibliographic identities were checked for all 67 references: 60 DOI records
match their works, and seven non-DOI items have official bibliographic or source
records. Barta's 1937 entry is supported by official archival bibliographies;
its original scan was not inspected. This is identity verification, not an
independent verification of every cited proof.

No release or Zenodo DOI was created. The manuscript's Data and Code
Availability section links to https://github.com/anaxia-research/4Y-M and
https://github.com/anaxia-research/anaxia, the former Open Gluon workspace.
The upload record documents the final repository commit when the authorised push completes.

## Section 20

The exact rational checks in anc/seam_disagreement_constants.py cover the numerical inequalities in Theorem 20.1. The induction and continuum transfer are analytical arguments outside the Lean library. The calculation does not evaluate a tuned Wilson probability.

The updated checker counts square-face incidences on two even four-tori and verifies the cluster, threshold and trace constants by rational arithmetic. The proofs in Sections 20.1 and 20.2 are analytical and outside the Lean audit.

The exact checker also tests the rational constants for the side 24T and time multiplier 18 in the aspect-ratio theorem. The winding obstruction and the variable-aspect induction are analytical.

Sections 20.4 and 20.5 contain analytical proofs. The supporting Python check enumerates all Wilson plaquettes on a two-sheet lattice for the four temporal matchings and checks the row incidences and numerical constants. These results have not been formalized in Lean.

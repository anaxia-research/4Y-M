# Second Yang–Mills paper: current local package

Title: **Thermal Purity Bounds for Yang–Mills Theory at Weak Coupling**

Date: 15 November 2026. PDF pages: **22**.

Status: research draft. The full weak-coupling Wilson partition-function bound and the Clay mass gap have not been proved. No release or DOI has been created for this second paper.

The first paper is cited as *The Yang–Mills Mass Gap from One Bound at One Scale*, DOI **10.20944/preprints202611.1282.v1**. The first paper's PDF and source were preserved. This is a separate paper, not a replacement or a purported new version of it.

The six authors and their source-paper affiliations are retained at the user's request. The new derivations still require author review; approval by all coauthors is not asserted.

## Files

- `Paper-2.pdf`: the complete current manuscript.
- `Paper-2-tex.zip`: Overleaf-ready source; select `main.tex` and compile with pdfLaTeX. Figures are generated directly by TikZ.
- `verification/`: actual Anaxia/OpenGluon runs and finite certificate outputs. The six sampled block tests and four rational certificates do not prove a continuum result.
- `PACKAGE-METADATA.json`: hashes, page count and claim status.

## Proved results

The manuscript proves the optimal purity-to-gap conversion for positive compact transfer operators, trace-norm and partition-function error budgets, an enlarged sufficient one-scale pressure allowance, an explicit Wilson cylinder gap at every finite positive coupling, a thermal trace bound, an exact Wilson response identity, finite-order Haar-cumulant cancellation with an actual Wilson remainder, a finite-rank spectral certificate, and the stated comparisons and counterexamples. It also incorporates explicit thermal-defect transport and error-stable ascent proofs from the repository's current research work. Its continuum conclusion is conditional on the unproved Wilson seed and on the first paper's ascent/convergence framework.

The source includes a complete derivation of the positive-kernel bound and explains why its constant does not survive the needed limits. It does not turn a stored engine proposal, a finite lattice test, or a finite-volume gap into a proof of the Millennium theorem.

## Compile and check

Upload the TeX ZIP to Overleaf and compile `main.tex` with pdfLaTeX, or run pdfLaTeX twice locally. The exact arithmetic script is `anc/check_certificates.py` and needs only the Python standard library. Its JSON output is included. Anaxia replay additionally needs the user's local eBLLM and OpenGluon checkouts; the run script records their paths and commit.

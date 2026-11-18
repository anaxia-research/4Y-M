# One-cube criteria: checks L1–L16 and J1–J12

Checks supporting "The Yang–Mills Mass Gap from a Single-Cube Bound at Weak Coupling".
**None of these checks proves the existence of the continuum limit, the one-cube bound or the mass gap.**
They check numbers and finite identities that the paper uses.

Run: `lake build` (Lean) and `julia -t 4 julia/onecube/run_all.jl` (Julia; the output is in `output.txt`).

The 18 November 2026 run under Julia 1.13.4 passed 282 rigorous checks, 75
interval-regression assertions and all numerical sanity routines. The separate
exact line-field program passed five certificates. `CORRECTIONS.md` records the
former false root assertion, rational-rounding defect and failure-handling
repairs. The sanity routines use floating point and Monte Carlo; they are not
parts of the analytical proof.

## Lean (`YangMills/OneCube/`)

These are exact proofs: no `sorry`, and no axioms beyond Mathlib's standard three.

| Id | What is checked | File |
| :-- | :-- | :-- |
| L1 | `1/4097 ≤ 2x − 3x²` at `x = 1/8192` | `Constants.lean` |
| L2 | `40·96³`, `161·48³`, and `1/17805313 ≤ 2x − 3x²` at `x = 1/(322·48³)` | `Constants.lean` |
| L3 | `3/49155 = 1/16385`, `(1/16385)/(1−1/16385) = 2⁻¹⁴`; `−log(1−1/16385) ≤ 2⁻¹⁴`, `1 − e^{−2⁻¹³} ≤ 2⁻¹³` | `Constants.lean`, `Transcendental.lean` |
| L4 | `16/8191² + 8/511² + 4/255² + 2/127² < 2.17·10⁻⁴ < 1/4097` | `Constants.lean` |
| L5 | `κ_N = (4N³ − 6N + 3)/N³ ≥ 23/8` for every `N ≥ 2` | `Constants.lean` |
| L6–L9 | `K₀ = 239·161·48³`, the bookkeeping identities, the rational margin of 11.4 | `Constants.lean` |
| L10 | Fourier identity `w₀ − w_e = N⁻³ Σ_k (1 − cos(2πe·k/N)) Z(k)/Z` on `(ℤ/N)³` | `Fourier.lean` |
| L11 | Lemma W: trace identities, Gram expansion of `Φ`, `Φ = 1` at the three points and on a curve | `LemmaW.lean` |
| L12 | Link elimination for `S` and `S′`: closedness, counts, `ι^{n₄} d^{F−E} = −2⁻²⁷`, `−2⁻⁴³` | `Haar.lean` |
| L13 | The 12-state count | `Counting.lean` |
| L14, L15 | The X3 ascent chain; the four rational pairs of X1 | `Constants.lean` |
| L16 | `∏_{j<n}(x − 2cos(2πj/n)) = 2(T_n(x/2) − 1)` for every `n ≥ 1` | `Chebyshev.lean` |
| J1–J5, J7, J10–J12 | The exp/log/π inequalities proved directly in Lean, including J1 (the fixed point exists in `(1/4160, 1/4159)`) and J2 for every `i` | `Transcendental.lean` |
| J8, J9 | Every row of both tables: the datum at `T_*` and its failure below `T_*` (J8), the condition for all `T ≥ T_*` and its failure at `T_* − 1` (J9) | `Tables.lean` |
| J1–J12 | Every rational enclosure exported by Julia, re-checked by `norm_num` | `Enclosures.lean` (generated) |

L12 checks the combinatorial part. The pairing rules (R1)–(R4), which are Schur orthogonality for SU(2), are not formalised. Lemma W's inequality `Φ ≥ 1` is not formalised either.

## Julia (`julia/onecube/`)

`jchecks.jl` encloses each constant with 256-bit `BigFloat` and directed rounding (`intervals.jl`), prints PASS/FAIL and exports a rational bound. `sanity.jl` contains the numerical sanity checks. These run in `Float64` and are not proofs.

| Id | What is checked |
| :-- | :-- |
| J1 | `x_c ∈ (1/4160, 1/4159)` for `f(x) = (e^{64x} − 1)²` |
| J2 | `v_i ≤ θ⁻¹u^{2^i}/64`; `log(63/32) > 0.677` |
| J3 | `13 log 2`, `14 log 2`, `−log(e^{1/8192} − 1)`, `−log(e^{2⁻¹⁴} − 1)` |
| J4 | The `e^{−π}` constants, `log(1 + e^{−2π}) > 15/8192`, the counting constant `< 34` |
| J5 | `D`, `log(1/D) ≥ 15.3024`, `ε(6·10⁶)`, and the corrected `β = 10⁹` root bracket `116.5888 < T₀ < 116.5889` |
| J6 | `4/g_c² > 0.09497` |
| J7 | `κ_c`, the 2D thresholds, `log(1/q)` |
| J8 | The strong-coupling table (`θ`, `T_*`, minimality) and `artanh(1/18)` |
| J9 | The large-`N_c` table of `T_*` |
| J10 | The flux constants |
| J11 | The universal steps and the one-directionality witness |
| J12 | The exponential form of L4 and the comparisons of 8.9 |

`be_certificates.jl` (run: `julia julia/onecube/be_certificates.jl`; output in `be_certificates_output.txt`) checks the line-field computation of Section 9 in exact `Rational{BigInt}` quaternion arithmetic: the eigenvalue `9 + √17` of the period-cell operator on the 48 active links, the quotient `304/24` of the alternating field, and the exact Rayleigh quotients `R₊ ≥ 1397/100`, `R₋ ≥ 1394/100` of the two test fields in `certificates/` (the same data as the tables at the end of Appendix A).

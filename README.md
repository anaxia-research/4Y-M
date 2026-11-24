# The Mass Gap Δ > 0 in Four-Dimensional Lattice Yang–Mills Theory

**Deep Bhattacharjee**\*, **Ushashi Bhattacharya**, **James Montgomery Lockwood**,
**Tristan Romanov**, **Ikailo John Sessford** and **Sanjeevan Singha Roy**

**Deep Bhattacharjee.** Formerly, Electro-Gravitational Space Propulsion
Laboratory (EGSPL), Bhubaneswar, Odisha 751030, India; formerly, University of
Calcutta (Heramba Chandra College), 23/49 Gariahat Road, Golpark, Kolkata
700029, West Bengal, India.
Email: itsdeep@live.com, d.bhattacharjee@erl-forschung.de, egspl@proton.me.
ORCID [0000-0003-0466-750X](https://orcid.org/0000-0003-0466-750X).

**Ushashi Bhattacharya.** Formerly, National Taiwan University, Taipei 106319,
Taiwan. Email: rai.bhattacharya.in@gmail.com.
ORCID [0009-0002-2254-3914](https://orcid.org/0009-0002-2254-3914).

**James Montgomery Lockwood.** Independent Researcher, San Antonio, USA.
Email: spectralityworkinggroup@gmail.com.

**Tristan Romanov.** Independent Researcher, San Francisco, CA, USA.
Email: romanov360@gmail.com.

**Ikailo John Sessford.** Ikailo Inc., Whitby, Ontario, Canada.
Email: john@ikailo.com.
ORCID [0009-0002-0150-4027](https://orcid.org/0009-0002-0150-4027).

**Sanjeevan Singha Roy.** Department of Physics, Birla Institute of Technology,
Mesra, Ranchi, Jharkhand 835215, India. Email: sanjeevan9905@gmail.com.
ORCID [0000-0002-6148-1421](https://orcid.org/0000-0002-6148-1421).

\*Corresponding author and head of the project: Deep Bhattacharjee,
itsdeep@live.com. Code and GitHub contact: egspl@proton.me, GitHub
[creelie](https://github.com/creelie).

Preprints.org 202611.1282, version 3 (version 2:
[doi.org/10.20944/preprints202611.1282.v2](https://doi.org/10.20944/preprints202611.1282.v2)).

---

## Abstract

We prove that one inequality at one physical scale, imposed along the
asymptotic-freedom tuning, gives a positive mass gap in every nontrivial
continuum limit of four-dimensional Wilson lattice Yang–Mills theory. For
every compact simple gauge group we prove volume-uniform transfer-matrix gaps
with explicit rates at strong coupling. For SU(2) the underlying cube condition
holds uniformly in the cube size for β_W < (√37 − 5)/3, and we compute the
exact weak-coupling gap on each fixed free cube.

**Keywords:** lattice Yang–Mills theory; mass gap; reflection positivity.

**MSC 2020:** 81T13, 81T25; 82B20, 60K35, 81T08.

## Contents of this repository

| Path | Content |
|---|---|
| [`YangMills/`](YangMills) | Lean 4 formalization, 34 modules |
| [`YangMills.lean`](YangMills.lean) | Root file importing every module |
| [`Axioms.lean`](Axioms.lean) | Axiom audit of every theorem, and `#print axioms` for the main results |
| [`axioms.txt`](axioms.txt) | Output of `Axioms.lean` |

## The Lean formalization

The formalization is to be read beside the paper. It checks the finite,
algebraic and numerical steps of the paper, the explicit constants and
thresholds of the main theorems, and the analytic steps that can be stated on a
finite state space or on the real line.

It consists of 34 modules with 560 theorems and lemmas and 124 definitions,
about 7,000 lines in all. No file contains `sorry`, `admit`, a new `axiom`,
`native_decide` or an `@[implemented_by]` attribute. `Axioms.lean` collects every
theorem in the `YangMills` namespace, 1,062 of them including the auxiliary
ones that Lean generates, and fails unless each depends only on the three
standard axioms `propext`, `Classical.choice` and `Quot.sound`. Every constant
checked here is proved from its definition in exact arithmetic or by explicit
bounds on exp, log and √; none is taken from a floating-point computation.

## Main results

| Result in the paper | Lean theorem | Statement |
|---|---|---|
| No gapped limit from a spacing-uniform gap | `YangMills.nogo_no_gapped_limit` | If the lattice gap is bounded below uniformly in the spacing, the renormalised two-point functions cannot converge to those of a continuum theory with a positive gap. |
| Critical scaling of the lattice gap | `YangMills.limit_ratio_le` | If the lattice gaps are at least m_a · a with m_a → m, the limiting two-point function L satisfies L(t₂) ≤ e^{−m(t₂−t₁)} L(t₁). |
| Holley–Stroock perturbation | `YangMills.holleyStroock_poincare`, `YangMills.holleyStroock_entropy` | A Poincaré or entropy inequality survives a bounded change of potential, with constant multiplied by e^{osc V}. |
| The window is entered | `YangMills.window_entered` | Along the one-loop tuning the scale μ⋆ with g(μ⋆) = g lies between Λ and the cutoff 1/a for every small spacing. |
| Wilson action and volume | `YangMills.wilsonAction_osc_le`, `YangMills.corrAction_var_per_volume_unbounded` | The oscillation of βS is at most 2Nβ\|P\|; bounded nonnegative local terms do not give a volume-uniform cumulant bound. |
| Lattice Bianchi identity | `YangMills.cube_bianchi` | The six oriented plaquette angles of a cube sum to zero. |
| Dobrushin threshold in d = 4 | `YangMills.StrongCoupling.wilson_threshold_d4`, `YangMills.StrongCoupling.gap_d4` | The Dobrushin range is β_W < 2/9, with gap −log(9β_W/2). |
| Zonal half of the sharp quarter | `YangMills.StrongCoupling.zonal_final` | The final inequality 4A′² + T(A) < 0 of the zonal bound. |
| Gauge fixing and block gauge | `YangMills.StrongCoupling.GaugeFix.twelve_neighbours`, `YangMills.StrongCoupling.BlockGauge.invisible_classes` | Every remaining link has twelve remaining partners; exactly twelve active classes meet an invisible line. |
| Star threshold of SU(2) | `YangMills.StrongCoupling.StarThreshold.sevenSys_unique`, `YangMills.StrongCoupling.StarThreshold.lam_lt_one_iff_beta`, `YangMills.StrongCoupling.StarThreshold.svalues` | The seven-spin system has a unique solution, with s(c) = (1+c)/(1−4c−6c²) and exact values at c = 1/12, 7/80, 9/100; λ = 6c·s(c) < 1 exactly when β_W < (√37 − 5)/3. |
| Cube condition uniform in the cube size | `YangMills.StrongCoupling.StarThreshold.half_of_large`, `YangMills.StrongCoupling.StarThreshold.gap_constant`, `YangMills.StrongCoupling.StarThreshold.uniform_numbers_7_20` | The half condition holds for n ≥ 10/(1−λ), the gap is at least (1−λ)/(1250e²), and at β_W = 7/20 the size n ≥ 154 suffices while n = 153 does not. |
| Ascent without a gap hypothesis | `YangMills.GapFree.ascent_decay`, `YangMills.GapFree.log_gap_constant`, `YangMills.GapFree.fixed_point_bracket` | The recursion y_{i+1} ≤ 16(e^{y_i} − 1)² decays doubly exponentially from y₀ ≤ 1/20, with gap constant log(1/0.8415) > 0.172. |
| Free cube: Jacobi determinant | `YangMills.OneCube.Chebyshev.prod_identity` | ∏_j (x − 2cos(2πj/n)) = 2(T_n(x/2) − 1). |
| Free cube: sector-zero Fourier identity | `YangMills.OneCube.Fourier.L10` | The Fourier form of w₀ − w_e on (ℤ/N)³. |
| Free cube: pseudoreal surface integral | `YangMills.OneCube.Haar.L12_S` | The pairing-rule elimination on the 28-plaquette surface gives −2⁻²⁷. |
| Free cube: two-gluon singlets | `YangMills.OneCube.Counting.L13` | There are twelve two-gluon singlet states on the lowest shell. |
| Centre twists | `YangMills.CentreTwists.twist_ratio_bounds`, `YangMills.CentreTwists.datum_twist` | The twisted ratio (1 + Σ εᵢrᵢ)/(1 + Σ rᵢ) lies in [(1 − Σ rᵢ)/(1 + Σ rᵢ), 1]; a ratio at least 2e^{−X} − 1 with X ≤ 1/8192 is at least 1 − 1/4096. |
| Z₂ Peierls comparison | `YangMills.CentreTwists.peierls_threshold_2127`, `YangMills.CentreTwists.peierls_threshold_2495` | For β ≥ 2.127 and every T ≥ 2 the Peierls bound is below 1 − 1/4096, and for β ≥ 2.495 it is at most 10⁻³. |
| Twist eaters | `YangMills.CentreTwists.twistEater_commutator` | On the values 1, i, k the plaquette variable ABA⁻¹B⁻¹ is −1 exactly for the pairs (i, k) and (k, i). |
| Abelian slice | `YangMills.CentreTwists.abelian_slice_cost` | Angles in [−π, π] on m plaquettes with sum π + 2πk give Σ(1 − cos φ) ≥ 2/m. |

## What the paper proves outside Lean

The character expansions on SU(N), the transfer matrices on infinite
lattices, the polymer and cluster expansions, the Dobrushin comparison in
infinite volume, reflection positivity and the passage to the continuum use
analytic machinery that Mathlib does not yet provide. These steps are proved in
full in the paper. Where a module checks the finite part of such a step, its
header says which part is checked and which is proved in the paper.

The continuum criterion of the paper takes the one-scale inequality as its
hypothesis. Its finite and algebraic parts are checked in
[`YangMills/OneScale.lean`](YangMills/OneScale.lean) and
[`YangMills/BoundEquiv.lean`](YangMills/BoundEquiv.lean).

## Building

Requirements: [elan](https://github.com/leanprover/elan). The toolchain
(Lean 4.33.0) and the Mathlib revision (tag `v4.33.0`) are pinned in
[`lean-toolchain`](lean-toolchain) and [`lake-manifest.json`](lake-manifest.json).

```
lake exe cache get
lake build
lake env lean Axioms.lean
```

On a four-core machine, `lake exe cache get` takes about 4 minutes (including
the download of Mathlib and its prebuilt cache), `lake build` about 2 minutes,
and the audit about 20 seconds. The build finishes with no errors and no
warnings, and the audit prints the text of [`axioms.txt`](axioms.txt).
The same three steps run in GitHub Actions on every push
([`.github/workflows/lean.yml`](.github/workflows/lean.yml)).

## Repository layout

```
YangMills/
  SpectralNoGo.lean         no gapped limit from a spacing-uniform gap
  LimitRatio.lean           critical scaling of the lattice gap
  BoundEquiv.lean           what the one bound is
  OneScale.lean             the one-scale hypothesis: finite and algebraic parts
  RunningCoupling.lean      one-loop running coupling, the window is entered
  HolleyStroock.lean        Holley–Stroock on a finite state space
  WilsonAction.lean         Wilson action bounds, lattice Bianchi identity
  CumulantCounterexample.lean  no volume-uniform cumulant bound
  AveragedCondition.lean    averaged cube condition and the ends
  CountSectors.lean         count of states and centre sectors
  ErrorStableAscent.lean    error-stable quadratic ascent
  GapFree.lean              the ascent without a gap hypothesis
  CentreTwists.lean         centre twists, Z₂ Peierls comparison, twist eaters
  StrongCoupling/
    Thresholds.lean         Dobrushin threshold at the sharp quarter
    ZonalBound.lean         zonal half of the sharp quarter
    QxCoefficients.lean     transverse half: coefficient positivity
    GaugeFix.lean           one fixed link in every plaquette
    BlockGauge.lean         block-rooted axial gauge
    DobrushinComparison.lean, WassersteinBridge.lean,
    CouplingMinimizer.lean, CouplingMinimality.lean
                            the W₁ Dobrushin comparison
    IslandLayer.lean        layer theorem and block-map growth
    CubeOpen.lean           perturbations of the cube condition
    StarThreshold.lean      star threshold of SU(2), uniform constants
  OneCube.lean              root of the free-cube checks
  OneCube/
    Constants.lean          exact rational constants
    Transcendental.lean     transcendental constants
    Tables.lean             certified tables
    LemmaW.lean             algebra of Lemma W
    Chebyshev.lean          Jacobi determinant identity
    Fourier.lean            sector-zero Fourier identity
    Haar.lean               pseudoreal surface integrals
    Counting.lean           two-gluon singlet states
YangMills.lean              root import
Axioms.lean                 axiom audit and #print axioms
axioms.txt                  output of Axioms.lean
.github/workflows/lean.yml  build and audit on every push
```

## Citation

```bibtex
@misc{Bhattacharjee2026YangMills,
  author       = {Bhattacharjee, Deep and Bhattacharya, Ushashi and Lockwood, James Montgomery
                  and Romanov, Tristan and Sessford, Ikailo John and Singha Roy, Sanjeevan},
  title        = {The Mass Gap {$\Delta > 0$} in Four-Dimensional Lattice {Yang--Mills} Theory},
  year         = {2026},
  howpublished = {Preprints.org, 202611.1282, version 3},
  url          = {https://github.com/anaxia-research/4Y-M}
}
```

## Licence

The Lean files are under the MIT licence ([`LICENSE`](LICENSE)). Mathlib is
under Apache 2.0.

# Yang–Mills Mass Gap: Lean 4 Formalization

Lean 4 and Mathlib formalization for the paper

**The SU(2) Yang–Mills Mass Gap Δ > 0 from a Single Finite-Volume Bound**

## Authors

- **Deep Bhattacharjee** (corresponding author and head of the project).
  Formerly, Electro-Gravitational Space Propulsion Laboratory (EGSPL),
  Bhubaneswar, Odisha 751030, India; formerly, University of Calcutta (Heramba
  Chandra College), Kolkata 700029, West Bengal, India.
  itsdeep@live.com, d.bhattacharjee@erl-forschung.de, egspl@proton.me.
  ORCID [0000-0003-0466-750X](https://orcid.org/0000-0003-0466-750X).
- **Ushashi Bhattacharya**. Formerly, National Taiwan University, Taipei
  106319, Taiwan. rai.bhattacharya.in@gmail.com.
  ORCID [0009-0002-2254-3914](https://orcid.org/0009-0002-2254-3914).
- **James Montgomery Lockwood**. Independent Researcher, San Antonio, USA.
  spectralityworkinggroup@gmail.com.
- **Tristan Romanov**. Independent Researcher, San Francisco, CA, USA.
  romanov360@gmail.com.
- **Ikailo John Sessford**. Ikailo Inc., Whitby, Ontario, Canada.
  john@ikailo.com.
  ORCID [0009-0002-0150-4027](https://orcid.org/0009-0002-0150-4027).
- **Sanjeevan Singha Roy**. Department of Physics, Birla Institute of
  Technology, Mesra, Ranchi, Jharkhand 835215, India.
  sanjeevan9905@gmail.com.
  ORCID [0000-0002-6148-1421](https://orcid.org/0000-0002-6148-1421).

Previous version of the paper: Preprints 202611.1282, version 2,
doi:[10.20944/preprints202611.1282.v2](https://doi.org/10.20944/preprints202611.1282.v2).

## What the paper proves

| Statement | Status |
|---|---|
| Mass gap Δ = t₀⁻¹ log(63/32) for four-dimensional SU(2) Yang–Mills theory in every Wightman continuum limit along the asymptotic-freedom tuning (one loop, or two loops with the log log N term), given one bound (P) on the pressure of one box of fixed physical size, uniform in the lattice spacing | proved from (P) |
| The box certificate: pressure bound X(1012; b) ≤ x* on the 2024³ × 1012 lattice for 0 ≤ b ≤ 1/3 | proved (exact arithmetic, `StarCert.lean`) |
| One-box reduction: the box certificate and the endpoint condition give the pressure bound on the large box, and a gap bound for it | proved (`OneBox.lean`) |
| Rung count: the two-loop asymptotic-freedom tuning β_N = c₁ log N + c₁γ log log N + O(1), γ = 51/121, meets the size bound of the one-box reduction through the scale function ℓ(β) = β/c₁ − γ log(1 + β/4) | proved (`Tuning.lean`) |
| Free gluons violate (P) on every box: pressure above 1/2 (above 1/50 on colour-invariant states) and 2T·E₁ ≤ 2π, at every spacing | proved (`FreePressure.lean`) |
| Zero-free strip of optimal width and count of the complex zeros of the torus partition functions | proved |
| Volume-uniform transfer-matrix gaps at strong coupling for every compact simple gauge group | proved |
| Cube condition and one-cube datum for SU(2) for β_W < (√37 − 5)/3, uniformly in the cube size | proved |
| Polyakov-loop correlator of two static sources bounded by a centre-vortex free energy | proved |
| The bound (P), equivalently the endpoint condition (E_D): the finite-volume mass gap uniformly in the lattice spacing | hypothesis |

[![Lean](https://github.com/anaxia-research/4Y-M/actions/workflows/lean.yml/badge.svg)](https://github.com/anaxia-research/4Y-M/actions/workflows/lean.yml)

## Overview

The Lean files formalize the finite, algebraic
and numerical parts of four-dimensional Wilson lattice Yang–Mills theory that
the mass-gap argument rests on: the spectral no-go theorem and the critical
scaling of the lattice gap, Dobrushin and star thresholds at strong coupling,
the cube condition and its ascent, the free cube at weak coupling, centre
twists and two static sources, and the quasi-Lee–Yang zeros of two finite tori
together with the transport of zero-free domains to the twisted ratios, the
zero-free strips at every coupling and the count of the zeros, the defect
ledger, the one-box reduction and the box certificate on the star range. Every explicit
constant and threshold of the main theorems is proved here from its definition.

| | |
|---|---|
| Modules | 41 |
| Theorems and lemmas | 733 |
| Definitions | 136 |
| Lines | about 9,800 |
| Theorems audited | 1,331 (all declarations in the `YangMills` namespace, including auxiliary ones) |
| Axioms | `propext`, `Classical.choice`, `Quot.sound` only |
| Toolchain | Lean 4.33.0, Mathlib `v4.33.0` |

No file contains `sorry`, `admit`, a new `axiom`, `native_decide` or an
`@[implemented_by]` attribute. [`Axioms.lean`](Axioms.lean) collects every
theorem in the `YangMills` namespace and fails unless each depends only on the
three standard axioms; its output is [`axioms.txt`](axioms.txt). Constants are
proved in exact arithmetic or by explicit bounds on exp, log and √; none is
taken from a floating-point computation.

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

## Main results

Each row names a statement and the Lean theorems that prove it.

| Result | Lean theorems | Statement |
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
| Compensation inequality: Hölder step | `YangMills.TwoSources.compensation_sector` | For weights c_{ik} ≥ 0 with row and column sums at most N², Σ c_{ik} λ_i^{L−ℓ} μ_k^ℓ ≤ N² (Σ λ_i^L)^{1−s} (Σ μ_k^L)^s with s = ℓ/L. |
| Compensation inequality: final form | `YangMills.TwoSources.two_point`, `YangMills.TwoSources.compensation_final` | ((1+ζ)^{1−s}(1−ζ)^s + (1+ζ)^s(1−ζ)^{1−s})/2 ≤ (1 − ζ²)^{min(s, 1−s)} for 0 ≤ ζ ≤ 1. |
| Log-convexity of the static pair | `YangMills.TwoSources.logconvex_sum` | f(ℓ) = Σ c r^ℓ q^{L−ℓ} with nonnegative terms satisfies f(ℓ)² ≤ f(ℓ−1) f(ℓ+1). |
| Twist–flux exchange | `YangMills.TwoSources.fourier_inversion`, `YangMills.TwoSources.flux_small`, `YangMills.TwoSources.flux_zero_large`, `YangMills.TwoSources.twist_of_Ftw` | Fourier inversion on ℤ₂^m between twisted and electric-flux partition functions; twisted ratios at least 1 − η give flux weights at most η/2 and the converse bound. |
| Polyakov loops as charged traces | `YangMills.TwoSources.trace_sandwich` | The trace of X ↦ A X B* on n × n matrices is Tr A · conj(Tr B). |
| Centre sheets | `YangMills.TwoSources.sheet_expansion` | ∏ (w₊ + ζ_p w₋) expands as the sum over sheets S of ∏_{p∈S} ζ_p w₋ ∏_{p∉S} w₊. |
| Constants for two sources | `YangMills.TwoSources.datum_antipodal`, `YangMills.TwoSources.datum_pair_free_energy`, `YangMills.TwoSources.datum_flux_log`, `YangMills.TwoSources.flux_antipodal` | Under the single-cube datum: antipodal Polyakov correlator at most 0.08839, static-pair free energy at least 2.4260, electric-flux free energy above log 8191 > 9.0107; with η = 1/7169 the antipodal bound 0.066812. |
| Quasi-Lee–Yang zeros: the stack identity | `YangMills.QuasiLeeYang.vieta_norm`, `YangMills.QuasiLeeYang.stack_on_line` | The product of the moduli of the roots is \|g(0)\|/\|leading coefficient\|; if every root lies on the unit circle, the twisted and untwisted partition functions agree. |
| Two-dimensional circle theorem | `YangMills.QuasiLeeYang.circle_zeros`, `YangMills.QuasiLeeYang.standing_wave_poly` | On the circle ρ^F O = E the points ρe^{iπ(2k+1)/F} are zeros of E + θ^F O, and \|E + (ρe^{iφ})^F O\| = 2E\|cos(Fφ/2)\|: nodes and antinodes of a standing wave. |
| Knot lemma and twist areas | `YangMills.QuasiLeeYang.knot_invariance`, `YangMills.QuasiLeeYang.knot_independent`, `YangMills.QuasiLeeYang.area_bound` | A twist is a cocycle: it does not change when a sheet is deformed by a boundary, its parity on a 2-cycle does not depend on the sheet, and a 2-cycle that detects a temporal twist has at least L_j L_3 = 2T² plaquettes. |
| Transport by Borel–Carathéodory and Schwarz | `YangMills.QuasiLeeYang.theoremA_tail`, `YangMills.QuasiLeeYang.theoremA_domain`, `YangMills.QuasiLeeYang.theoremB`, `YangMills.QuasiLeeYang.theoremB_zstar` | A zero-free vortex disc or domain bounds the twisted ratios; a zero-free domain in the coupling, entered through any analytic map of the disc, gives ψ_T ≤ 12288 s T⁵ ω^{4T}. |
| Zeros anywhere | `YangMills.QuasiLeeYang.coef_tail`, `YangMills.QuasiLeeYang.zstar_implies_HZ`, `YangMills.QuasiLeeYang.halfplane_model`, `YangMills.QuasiLeeYang.strip_model` | Coefficients bounded by C that vanish below order m give a sum at most C\|v\|^m/(1−\|v\|); the hyperbolic bound 768 s T⁴ ω^{4T}/(1−ω) is at most a quarter of 12288 s T⁵ ω_D^{4T}; the half-plane and strip models of the modulus. |
| Evenness in the coupling | `YangMills.QuasiLeeYang.stagger_plaquette_odd` | The staggered centre transformation multiplies every plaquette by the centre: the four exponents add up to 1 mod 2. |
| Zero-free strips and the count of zeros | `YangMills.QuasiLeeYang.strip_cos_lower`, `YangMills.QuasiLeeYang.strip_optimal`, `YangMills.QuasiLeeYang.heat_strip`, `YangMills.QuasiLeeYang.jensen_constant` | If \|E\| ≤ P and P\|y\| ≤ π/2 then cos(yE) ≥ cos(Py) ≥ 0, which gives the zero-free strip \|Im β_W\| < π/(2\|P\|); the width is attained by cosh(Pβ); cos u ≥ 1 − u²/2 and the specific-heat strip; the Jensen constant 288e/π < 250. |
| Strong coupling and criticality | `YangMills.QuasiLeeYang.eps_rKP`, `YangMills.QuasiLeeYang.disc_consistency`, `YangMills.QuasiLeeYang.critical_width`, `YangMills.QuasiLeeYang.critflux_width` | ε(0.00539) ≤ 1/(25e²); 12288 · 0.00539 · T⁵ 2^{−4T} ≤ 1/4097 for T ≥ 9; the critical half-widths 11/(6π) and 11/(12π). |
| The projected datum and ℤ₂ | `YangMills.QuasiLeeYang.plus_arith`, `YangMills.QuasiLeeYang.KN_threshold`, `YangMills.QuasiLeeYang.z2_datum_gap` | 1/8194 + 2/16388 = 1/4097 with the flux correction 7/114721 < 1/16388; the ℤ₂ half-plane Re K ≥ ½ log(50e²) and the ℤ₂ datum gap log(2/1.001) > 0.6921. |
| The defect ledger | `YangMills.Ledger.matched_mem`, `YangMills.Ledger.orbit_chain`, `YangMills.Ledger.ledger_bound`, `YangMills.Ledger.ladder_length`, `YangMills.Ledger.ladder_size`, `YangMills.Ledger.step_scaling_defect` | A continuous pressure attains the infimum that defines the pressure-matched coupling; pressures are non-decreasing along the matched orbit until it enters the strong-coupling band; a running defect at most D gives the pressure bound at the top of the ladder, with 2^{n₀} ≤ 2N e^{(C+D)/c₁}; the rung-by-rung step-scaling condition gives a defect at most c₁ log 2. |
| The one-box reduction | `YangMills.OneBox.gap_of_pressure`, `YangMills.OneBox.onebox_bound`, `YangMills.OneBox.onebox_gap`, `YangMills.OneBox.endpoint_le`, `YangMills.OneBox.ref_iterate_le`, `YangMills.OneBox.onebox_size`, `YangMills.OneBox.orb_drop`, `YangMills.OneBox.barrier_chain`, `YangMills.OneBox.barrier_gap` | A pressure at most x forces T E₁ ≥ log(1/(e^x − 1)); the box certificate on [0, β_top] and the endpoint condition give the pressure bound on the large box and hence its gap bound, with 2^n < 2N e^{(C+D−β_top)/c₁}; a uniform drop on a window ends the matched orbit in the strong-coupling band within j rungs and gives the gap bound E ≥ 4 log 2/L − log(2KT⁴)/T. |
| The rung count and the two-loop tuning | `YangMills.Tuning.side_of_rungs`, `YangMills.Tuning.scale_step`, `YangMills.Tuning.scale_iterate`, `YangMills.Tuning.scale_rungs`, `YangMills.Tuning.twoloop_lipschitz`, `YangMills.Tuning.log_incr_le`, `YangMills.Tuning.twoloop_lower_incr`, `YangMills.Tuning.twoloop_strictMono`, `YangMills.Tuning.twoloop_lower`, `YangMills.Tuning.su2_twoloop_endpoint` | The rung count 2^n ≤ 2^K N gives the side T_*2^n ≤ (2^K T_*) N; a reference map with ℓ(ρb) = ℓb − log 2 lowers the coupling by at least c₁ log 2 and has ℓ(ρ^k β) = ℓβ − k log 2, so ℓβ ≤ log N + C gives 2^n ≤ 2N e^{C−ℓ(a)}; the two-loop scale function has slope at most 1/c₁, is strictly increasing for β₁ > c₁γ, and for SU(2) with γ = 51/121, β₁ = 4 satisfies ℓ(b) ≥ log 2 for b ≥ 161/600. |
| The free pressure on one box | `YangMills.FreePressure.omega_le`, `YangMills.FreePressure.gap_le`, `YangMills.FreePressure.mode_ge`, `YangMills.FreePressure.exp_pi_lt`, `YangMills.FreePressure.exp_neg_pi_gt`, `YangMills.FreePressure.free_pressure_ge`, `YangMills.FreePressure.free_pressure_gt`, `YangMills.FreePressure.singlet_pressure_gt`, `YangMills.FreePressure.free_violates`, `YangMills.FreePressure.singlet_violates` | The lowest mode energy 2 arsinh(sin(π/2T)) ≤ π/T, so 2T·E₁ ≤ 2π; each of the 36 lowest modes adds at least e^{−π} > 1/55 to the pressure, so X > 1/2 > 10⁴ x_*; the 78 colour-invariant two-mode states give X ≥ log(1 + 78e^{−2π}) > 1/50 > 500 x_*. |
| The box certificate on the star range | `YangMills.StarCert.ratio_le`, `YangMills.StarCert.q_admissible_third`, `YangMills.StarCert.starBound_third`, `YangMills.StarCert.starBound_seven_twentieths`, `YangMills.StarCert.xstar_lower`, `YangMills.StarCert.certificate_of_star`, `YangMills.StarCert.certificate_third`, `YangMills.StarCert.oneloop_step_lt_third` | The box certificate X(T_*; b) ≤ x_* holds on [0, 1/3] for T_* = 1012 (and on [0, 7/20] for T_* = 2860): x_* ≥ 1/28684, and the star bound 𝔅(1/3, 1012, 575769/500000) ≤ 1/28684 in exact rational arithmetic; the one-loop step c₁ log 2 is below 1/3. |

## Scope

Character expansions on SU(N), transfer matrices on infinite lattices, polymer
and cluster expansions, the Dobrushin comparison in infinite volume,
reflection positivity, the continuum limit, Riemann and covering maps of plane
domains and Carathéodory's coefficient inequality need analytic machinery that
Mathlib does not yet provide, and are not formalized here. Where a module
checks the finite part of such a step, its header says which part is checked.
The finite and algebraic parts of the one-scale hypothesis used by the
continuum criterion are in [`YangMills/OneScale.lean`](YangMills/OneScale.lean)
and [`YangMills/BoundEquiv.lean`](YangMills/BoundEquiv.lean).

## Layout

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
  TwoSources.lean           two static sources: compensation, twist–flux exchange
  QuasiLeeYang.lean         quasi-Lee–Yang zeros: stack identity, circle theorem,
                            knot lemma, transport theorems, zeros anywhere,
                            evenness, zero-free strips, criticality, constants
  Ledger.lean               the defect ledger: matched orbit, ladder bound
  OneBox.lean               the one-box reduction: pressure and gap, one-box
                            bound, size of the box, barrier for a uniform drop
  StarCert.lean             the box certificate on the star range
  FreePressure.lean         free gluons violate the box pressure bound
  Tuning.lean               the rung count and the two-loop tuning
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

## Acknowledgements

The project was organised in [Anaxia](https://github.com/anaxia-research/anaxia),
the research workspace of Deep Bhattacharjee, and its construction engine
[eBLLM](https://github.com/anaxia-research/eBLLM).

## Citation

```bibtex
@misc{Bhattacharjee2026YangMills,
  author       = {Bhattacharjee, Deep and Bhattacharya, Ushashi and Lockwood, James Montgomery
                  and Romanov, Tristan and Sessford, Ikailo John and Singha Roy, Sanjeevan},
  title        = {The {SU(2)} {Yang--Mills} Mass Gap {$\Delta > 0$} from a Single Finite-Volume Bound},
  year         = {2026},
  note         = {Preprint},
  url          = {https://github.com/anaxia-research/4Y-M}
}
```

## Licence

MIT ([`LICENSE`](LICENSE)). Mathlib is under Apache 2.0.

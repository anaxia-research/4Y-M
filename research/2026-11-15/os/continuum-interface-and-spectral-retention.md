# Continuum interface and retention of finite physical energy

Date: 2026-11-15. Status: proved analytical lemmas and source audit; no claim of an unconditional Yang–Mills mass gap; no Lean verification of the new lemmas below.

Repository main inspected: `2e36be0f89e50aeabeb3844418cf9ad58b1e7fd9`. Manuscript inspected: the 170-page PDF on `paper`, commit `50095e99694feea0d72a9cd1495ea4d88efddb4e`. Existing manuscripts were not modified.

## 1. What the current manuscript already supplies

The manuscript's Definition 7.2 assumes a common Wilson family, renormalized fixed-stencil insertions, an ordered ultraviolet/volume limit, and a phase decomposition into Wightman theories. Theorem F adds the one-scale thermal bound `(B*)`. It does not construct that bound at weak coupling.

The proposed dense-observable gap bridge is already present: Proposition H.25 gives the equivalence between a global continuum gap and exponential decay on the generating observable class; Lemma H.26 transfers lattice gaps in physical units. Theorem H.27 deliberately permits cutoff-dependent spectral observables and explains why its abstract gapped limit is not identified with Yang–Mills. Those results must not be presented as new findings of this audit.

In `YangMills/LimitRatio.lean`, `limit_ratio_le` is a conditional scalar two-point statement. Interpreting its conclusion as a gap of the entire reconstructed Hamiltonian additionally uses the dense-class argument already supplied by H.25 or Theorem E, not merely one scalar field.

The complex conjugation bar in Definition 7.1(F3) is present in the rendered PDF, although ordinary text extraction loses it. The page image `definition-7-1.png` records that visual check. No missing-conjugation defect was found.

## 2. A harmless restriction in the existence interface can be removed

**Proposition A (arbitrary integer inverse-spacing subsequences).** In the continuum-family version of Theorems E and F, replace `a_N=1/N` with `a_j=1/D_j`, where `D_j` is any sequence of positive integers tending to infinity. Interpret every mesh-dependent hypothesis only at these spacings, keep the physical sides `L_p` integral, and retain the parity requirements used for reflection positivity. Replace the arithmetic-progression ultraviolet limit by the limit along `j`. The same conclusions and physical gap constants hold.

**Proof.** Reindex all finite lattice objects by the numerical inverse spacing `D_j`. All transfer-matrix, cutting, halving, and ascent inequalities are inequalities at one fixed mesh. They use spatial side `D_j L_p`, the supplied integer time `3<=T_0(j,p)<=D_j t_0` of Theorem F, and comparisons such as `n_j/D_j <= ell`. They neither compare neighboring mesh indices nor sum over all inverse spacings.

In Theorem E, Step 1 uses integer physical translations `sigma`, so its lattice translation is `sigma D_j`, an integer for every `j`. The reflected and translated supports remain separated at fixed positive physical distance; the fixed stencil radius becomes negligible because `D_j -> infinity`. Step 2 passes a finite collection of these inequalities through the assumed ordered limits. Subsequences cause no change to that operation. Step 3 uses arbitrarily large integer physical translations to annihilate the phase variance; Step 4 uses the same translations and the spectral theorem to exclude energies below the claimed gap. Neither step requires a dense set of physical time increments or an arithmetic progression of `D_j`.

In Theorem F, apply Theorem 7.56 separately at each `(j,p)`. Its thermal ascent uses `T_i=2^i T_0(j,p)`, not a mesh refinement. The bound `T_0(j,p)<=D_j t_0` gives the physical lower gap `log(1/u_0)/t_0 > 0.172/t_0` at every sufficiently fine mesh, exactly as in the original theorem. The vacuum-dominance bounds are likewise pointwise mesh estimates followed by the same ordered limits. All conclusions follow. This is a change to the allowed ultraviolet index set, not a weakening of `(B*)`, `(W)`, or the same-family requirement. QED.

If one instead imposes a rounded-time variant with `T_0(j)=ceil(D_j t_0)`, this is a different finite-mesh hypothesis: its upper physical extent is `t_0+1/D_j`. The physical gap rates `D_j log(1/u_0)/T_0(j)` then converge to `log(1/u_0)/t_0`. Carrying those rates through the ordered limit gives that continuum lower bound; it is incorrect to replace the ceiling by `D_j t_0` in a finite-cutoff inequality. For vacuum dominance one may use any fixed smaller positive rate eventually and take `L_p>2t_0` before the limit.

**Use.** A continuum construction with integer inverse spacings formed from growing odd block ratios does not have to be extended to every integer inverse spacing before this argument applies. The physical side must still supply any required evenness. The exact October source `PublicWilson.lean` defines `mesh N=((C.denominator N).val:Real)^(-1)` with a strictly increasing positive integer denominator, and uses side `period p * denominator N`; thus the public family has the required spacing form. If a different construction instead has a reciprocal spacing that is not integral, Proposition A alone does not supply an adapter. Propositions A2 and A3 give rounding alternatives under their respective spectral or distributional hypotheses. None of these propositions proves the thermal estimate on the construction's couplings.

**Proposition A2 (rounding physical time away from the boundary).** Let `nu_j` be positive Borel measures on `[0,infinity)` and put `F_j(t)=integral exp(-tE) d nu_j(E)`. Suppose `F_j(s_0)<=M` for a fixed `s_0>=0`. For `eta>0` and `t,u>=s_0+eta`,

`|F_j(t)-F_j(u)| <= M |t-u|/(e eta)`.

**Proof.** For each `E>=0`, the ordinary mean-value theorem gives

`|exp(-tE)-exp(-uE)| <= |t-u| E exp(-min(t,u)E)`

`<= |t-u| exp(-s_0 E) E exp(-eta E)`

`<= |t-u| exp(-s_0 E)/(e eta)`.

The final inequality is the maximum of `x exp(-eta x)` on `[0,infinity)`, attained at `x=1/eta`. The anchor bound makes the right side integrable. Integrating the pointwise inequality proves the claim, without differentiating under an integral sign. QED.

If `a_j->0`, `t>s_0`, and `t_j` is a lattice time with `|t_j-t|<=a_j`, choose `eta=(t-s_0)/2`. Eventually both times lie above `s_0+eta`, and

`|F_j(t_j)-F_j(t)| <= 2M a_j/(e(t-s_0)) -> 0`.

Thus fixed-time convergence and convergence at these rounded lattice times are equivalent. No denominator divisibility is needed for this statement.

For cross matrix elements of a nonnegative self-adjoint Hamiltonian the corresponding estimate is

`|<psi_j,(exp(-tH_j)-exp(-uH_j))phi_j>|`

`<= |t-u| sqrt(F_psi,j(s_0) F_phi,j(s_0))/(e eta)`.

To prove it, put half of `exp(-s_0 H_j)` on each vector and bound the remaining spectral multiplier in operator norm by the same scalar maximum. The two squared vector norms are the two displayed anchor values.

This lemma applies to positive-energy vacuum spectral representations. A finite-temperature torus two-point function can contain energy differences of both signs, as Remark 7.7 of the manuscript explains; it cannot be substituted into this proof before vacuum dominance or an appropriate separate spectral estimate has been supplied. The estimate also gives no continuity at `t=s_0` from an anchor alone. Those restrictions prevent using the lemma to conceal the nontriviality issue in section 4.

**Proposition A3 (moving tests from full distributional ultraviolet convergence).** Fix a physical volume `p`, a fixed finite tuple of field labels, and a compact set `K` lying strictly inside its period cell and strictly inside the noncoincident configuration domain. Let `D_K` be the Fréchet space of smooth complex functions supported in `K`, with increasing seminorms

`p_r(f)=max_(|alpha|<=r) sup_x |partial^alpha f(x)|`, `r=0,1,...`.

Let `T_j:D_K->C` be the corresponding lattice correlation functionals. Assume they are continuous and that `T_j(f)` converges for every fixed `f in D_K`. If `f_j,f in D_K` and `p_r(f_j-f)->0` for every `r`, then

`T_j(f_j)-T_j(f) -> 0`,

so `T_j(f_j)` converges to the same limit as the fixed-test sequence `T_j(f)`.

**Proof including the uniform-boundedness step.** Pointwise convergence implies `sup_j |T_j(g)|<infinity` for each `g in D_K`. The closed sets

`A_m={g in D_K: sup_j |T_j(g)|<=m}`, `m=1,2,...`,

therefore cover `D_K`. The space is complete and metrizable, so the Baire theorem gives an `A_m` with nonempty interior. Choose `g_0` in that interior. For some `r` and `epsilon>0`,

`g_0+{h:p_r(h)<epsilon} subset A_m`.

Both `g_0` and `g_0+h` belong to `A_m`, giving `sup_j |T_j(h)|<=2m` on this neighborhood. Scaling an arbitrary `h` by `epsilon/(2p_r(h))` when `p_r(h)>0` yields

`sup_j |T_j(h)| <= (4m/epsilon) p_r(h)`.

If `p_r(h)=0`, then `p_0(h)=0`, so `h=0` and the bound also holds. Apply this common seminorm bound to `h=f_j-f`. Its right side tends to zero. QED.

Continuity of each finite-lattice functional is immediate: it is a finite sum of point evaluations, with finite correlation coefficients at that cutoff. The common bound just proved does not require a cutoff-uniform supremum bound on the renormalized insertions.

For a fixed physical translation `sigma`, choose integer lattice shifts `k_j` with `|a_j k_j-sigma|<=a_j`. A fixed smooth test translated by `a_j k_j` converges, with all derivatives, to the test translated by `sigma`. If the original reflected and translated clusters have a strict separation and lie strictly inside the period cell, then all sufficiently late tests have support in one such common `K`. Proposition A3 applies to those reflected-product tests and to each finite collection used in Theorem E's inequality. In particular it applies directly to thermal torus pairings under a full fixed-volume ultraviolet convergence hypothesis. It does not need a positive-energy spectral representation.

The constants `r,C` can depend on `p`, `K`, and the fixed labels. That causes no problem for the iterated limit: first take the ultraviolet limit at each fixed `p`, then take `p->infinity`. This argument supplies no exchange of the two limits and no uniform-in-volume estimate. It also does not permit a changing label tuple, a changing renormalization prescription, supports approaching a collision, or arbitrary `N`-dependent observables. Each of those would require additional hypotheses.

**Consequence for general meshes.** In an analogue of Theorem E with arbitrary `a_j->0` and integral lattice side `L_p/a_j`, replace the translations `sigma N` in Step 1 by `k_j=floor(sigma/a_j)`. For each pair of integer physical times `sigma>=sigma_1`, choose the two floors coherently, so `k_j>=k_1,j`, `a_j(k_j-k_1,j)->sigma-sigma_1`. Proposition A3 identifies the limiting smears with the intended translated clusters. The lattice spectral multiplier converges to the same continuum exponential bound. The phase and spectral arguments then proceed exactly as before. This is a sufficient general-mesh bridge under the full stated convergence of fixed tests; it is not an assertion that all other parts of `(W)` have been matched for an external construction.

## 3. Exact finite-energy retention criterion for a prescribed observable

Let `nu_j` be positive measures on physical energies `[0,infinity)`. In a transfer-matrix application they are the spectral measures after the map

`epsilon_lattice -> E_physical = epsilon_lattice/a_j`,

including the observable's renormalization. Put

`C_j(t) = integral exp(-t E) d nu_j(E)`.

The measures need not have uniformly bounded total mass. Finite positive-time Laplace transforms suffice, which is useful for local fields whose zero-time norm has an ultraviolet divergence.

**Proposition B (two-time retention).** Fix `0 <= t_0 < t_1`, write `d=t_1-t_0`, and suppose, eventually in `j`,

`C_j(t_0) <= B < infinity`, and `C_j(t_1) >= c > 0`.

Then, for

`M = log(2B/c)/d`,

one has, eventually,

`integral_[0,M] exp(-t_0 E) d nu_j(E) >= c/2`.

In fact the same lower bound holds with `t_1` in the exponential.

**Proof.** The assumptions and `H>=0` imply `0<c<=B`, so `M>0`. On `E>M`,

`exp(-t_1 E) <= exp(-d M) exp(-t_0 E)`.

Thus

`integral_(M,infinity) exp(-t_1 E) d nu_j <= exp(-d M) B = c/2`.

Subtract this from `C_j(t_1)>=c`. On `[0,M]`, the weight at `t_0` is at least the weight at `t_1`. Both claims follow. QED.

**Corollary B1.** If `C_j(t_0)->C(t_0)<infinity` and `C_j(t_1)->C(t_1)>0`, then a common finite physical-energy window retains a positive amount of heat-damped spectral weight. For example choose `B=2C(t_0)` and `c=C(t_1)/2` after discarding finitely many indices. Positivity gives `C(t_0)>=C(t_1)>0`.

**Corollary B2 (finite mass as well as a positive lower gap).** Suppose the same prescribed observable produces a nonzero centered vector `psi` in a reconstructed theory, with

`C(t)=<psi,exp(-tH)psi>`, `H>=0`,

and a global gap `Delta>0` has been proved on the full centered Hilbert space. If `C(t_0)<infinity` and `C(t_1)>0`, Proposition B applied to its spectral measure gives

`1_[Delta,M](H) psi != 0`, for `M=log(2C(t_0)/C(t_1))/(t_1-t_0)`.

Consequently the lowest nonvacuum energy is in `[Delta,M]`; in particular it is finite. This is a convenient explicit way to rule out a formal “gap” produced by sending every excitation to infinite physical energy. It does not identify an isolated one-particle eigenvalue.

There is also the sharper infimum bound

`inf supp(nu_psi) <= log(C(t_0)/C(t_1))/(t_1-t_0)`,

obtained from `C(t_1)<=exp(-d inf supp(nu_psi))C(t_0)`. The factor `2` in the window statement supplies a strictly positive quantitative lower bound on the retained weight.

**Converse under a physical lower gap.** If `nu_j` is supported in `[Delta,infinity)` and for some finite `M` the heat-damped weight of `[Delta,M]` at `t_0` is at least `b>0`, then

`C_j(t_1) >= b exp(-(t_1-t_0)M)`.

This follows by bounding the exponential below on that interval. Thus bounded-window retention is exactly the missing lower estimate when a finite positive-time upper estimate is available. It is not a consequence of a spectral-support lower bound alone.

## 4. A concrete test exposing loss of the prescribed local sector

The following is a transfer-matrix example, not a Wilson gauge theory and not a counterexample to Theorem F. It shows why a thermal upper estimate and correctly scaled gaps cannot replace the same-observable nontriviality input.

For integers `n>=21` let `a_n=n^-2`, `T_0=n^2`, and take a three-dimensional Hilbert space with

`H_n=diag(0,20,n)`, `T_n=exp(-a_n H_n)`.

The physical gap is exactly `20`; its lattice value is `20/n^2`. The ground state is unique. At physical time `1`, the excited thermal defect is

`D_n=Tr(T_n^T_0)-1=exp(-20)+exp(-n)`.

If the same transfer system is assigned to every transverse size, its trace obeys the numerical `(B*)` window inequality. Set

`gamma_n=1/(40(96T_0)^3)`, so `2 gamma_n(96T_0)^3=1/20`.

Every side in the window is at least `2T_0`, hence

`gamma_n V >= 1/(5*96^3)`.

For `n>=21`,

`log(1+D_n) <= D_n <= 2 exp(-20) < 1/(5*96^3)`.

The last strict inequality follows, for example, from `exp(20)>20^13/13!>10^7>10*96^3`. This proves the stated numerical window bound without relying on floating point arithmetic.

Now prescribe a centered observable whose vacuum vector is

`psi_n=n^-1 e_low + e_high`.

Its positive-time autocorrelation is

`C_n(t)=n^-2 exp(-20t)+exp(-nt) -> 0` for every fixed `t>0`.

Any fixed positive heat smear has norm tending to zero. The bounded physical-energy window contains only the low vector for large `n`, and its spectral weight is `n^-2 -> 0`. Proposition B correctly fails because there is no positive two-time lower bound.

At every finite `n`, time translates of `psi_n` span both excited eigenvectors: the coefficients are nonzero and the two energies differ. Thus finite-cutoff cyclicity by itself does not prevent the loss. A limit that retains only the vacuum after positive-time smearing is possible at this abstract level. Preserving a nonzero local continuum field is an additional requirement.

## 5. What can be imported from the current external existence assessment

The Yang–Mills group's 10 November 2026 assessment reports a Wilson scaling-limit Wightman construction for simple compact gauge groups. Its `CombinedAcceptance` binds one Wilson family, one extracted table, and one final witness; its scope documentation explicitly separates full fixed-volume ultraviolet convergence from extraction in volume, and does not claim a mass gap or a unique volume limit. These exact quantifiers matter more than an informal claim that “existence is solved.”

For using that input here, establish the following identities on a single witness:

1. Identify the finite Wilson law, trace normalization, and inverse coupling with those used in the one-scale estimate. A one-loop logarithmic slope alone does not identify two trajectories.
2. Use the exact source spacing and physical sides. If the common spacing is `a_j=1/D_j` with integral `D_j`, Proposition A accommodates the sparse mesh set. Otherwise establish the translated-smear convergence needed to use rounded physical times; Proposition A2 gives a sufficient spectral estimate away from a positive-time anchor, not an automatic consequence for thermal tori. All thermal estimates must hold on the actual mesh set and actual couplings.
3. Select a countable set of field labels that generates the reconstructed Hilbert space and is closed under the reflected adjoint. Verify the exact finite-stencil reflection identity, including complex conjugation, rather than only a limiting symmetry.
4. Retain the unselected table as the phase average of those same fields. A chosen pure phase cannot simply be substituted for that average before the phase-collapse argument.
5. Match the separated test pairings, continuity in phase, full support, and Wightman reconstruction needed by Definition 7.2. Reflection positivity without the reconstruction regularity estimates does not supply this.
6. Retain nontriviality for a prescribed physical field. A nonzero connected trace two-point function suffices: smearing it on separated reflected supports gives a nonzero centered OS vector. After a gap is proved, Corollary B2 supplies finite nonvacuum energy. A finite-cutoff positive probe alone need not suffice.

Items 1–5 are a source-level compatibility task, not an extra infrared estimate. Item 6 can use a proved nonzero continuum trace law on the same final witness. The remaining Yang–Mills analytic task is still the actual weak-coupling one-scale bound; no argument in this note proves it.

All lemmas above are independent of center characters, rank, and group type. Applying them to every compact simple group requires the compatible construction and one-scale estimate for each group. A calculation for `SU(2)` or `SU(3)`, or control of only center-charged states, does not discharge that quantifier or the neutral glueball sector.

## Primary sources and exact locations

- [Current 170-page manuscript, fixed paper revision](https://github.com/anaxia-research/4Y-M/blob/50095e99694feea0d72a9cd1495ea4d88efddb4e/papers/4Y-MPaper.pdf): Definition 7.1–7.2, Theorem E, Theorem 7.56/Theorem F, and H.25–H.27. All mathematical claims about the existing paper above refer to those locations.
- [LimitRatio.lean at the inspected main revision](https://github.com/anaxia-research/4Y-M/blob/2e36be0f89e50aeabeb3844418cf9ad58b1e7fd9/YangMills/LimitRatio.lean).
- [Jaffe–Witten, Quantum Yang–Mills Theory, section 4](https://www.claymath.org/wp-content/uploads/2022/06/yangmills.pdf): the official target includes a nontrivial theory and a positive finite lowest nonvacuum energy.
- [Osterwalder–Schrader II, CMP 42 (1975), 281–305](https://projecteuclid.org/journals/communications-in-mathematical-physics/volume-42/issue-3/Axioms-for-Euclidean-Greens-functions-II-with-an-Appendix-by/cmp/1103899050.pdf): the corrected reconstruction theorem includes growth and boundary-value control.
- [October assessment and reproduction entry point, fixed revision](https://github.com/yang-mills-group/YM/tree/55ba9fc36293b3f4d52c6b1f813169a0be76ee98).
- [Exact combined acceptance specification](https://github.com/yang-mills-group/YM/blob/55ba9fc36293b3f4d52c6b1f813169a0be76ee98/submissions/openai-20261028/checks/AcceptanceSpec.lean), especially `LatticeAndScale`, `PhaseAndOS`, `OperatorContent`, and `CombinedAcceptance`.
- [Exact public Wilson-family spacing definition](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/PublicWilson.lean), `WilsonFamily`, `mesh`, `place`, and `Converges`.
- [The assessment's documented check scope](https://github.com/yang-mills-group/YM/blob/55ba9fc36293b3f4d52c6b1f813169a0be76ee98/submissions/openai-20261028/docs/checks.md).

No proof or build of the external million-line construction was rerun during this audit. The source interfaces and dated primary assessment were inspected; the compatibility checklist is not represented as a completed formal bridge.

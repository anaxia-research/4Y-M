# The October construction and the November 13 Theorem F: a source-level interface audit

Date: 15 November 2026. Status: research note, not a full construction audit, new Lean build, or proof of the mass gap.

The strongest relevant contemporary primary source is now public. The October 28 construction has a November 10 assessment, the review specifications, and the submitted source. The November 13 paper already cites that assessment. The useful next step is to connect their exact mathematical objects; repeating an existence announcement does not prove the required infrared estimate.

## Fixed versions and scope

The target is the November 13, 170-page paper on `paper` at `50095e99694feea0d72a9cd1495ea4d88efddb4e`, especially Definitions 7.1--7.2, Theorem F, Proposition 7.57, and Theorem 7.61. The older 392-page `manuscript-v4411-current` branch is not used as the current theorem statement.

Primary external versions inspected:

- [Yang--Mills group review repository](https://github.com/yang-mills-group/YM/tree/55ba9fc36293b3f4d52c6b1f813169a0be76ee98), commit `55ba9fc36293b3f4d52c6b1f813169a0be76ee98`, assembled November 10--11.
- [Original October submission](https://github.com/yang-mills-group/OpenAI-YM-20261028/tree/3456e5e75cf8d4cd558955a5c7638fba2d68f464), commit `3456e5e75cf8d4cd558955a5c7638fba2d68f464`.
- [Assessment, November 10](https://github.com/yang-mills-group/YM/blob/55ba9fc36293b3f4d52c6b1f813169a0be76ee98/docs/assessment-1.pdf), Sections 4--6 and 8--11.
- [Official Jaffe--Witten problem](https://www.claymath.org/wp-content/uploads/2022/06/yangmills.pdf).

The assessment reports a fixed-volume ultraviolet construction and subsequential large-volume phase reconstruction. It explicitly leaves the mass gap and uniqueness across volume subsequences open. This note inspected the statements and several implementation chains below; it did not rebuild the approximately 9,500-file external development or independently certify its full mathematical semantics.

## Compatibility ledger

All paths in this table are repository-relative within the linked fixed commit; they are full source paths, not search-result excerpts.

| Requirement of the November 13 paper | Exact external source and declaration | Finding |
|---|---|---|
| One actual normalized Wilson family, with the same moments used in the limits | Review `submissions/openai-20261028/checks/AcceptanceSpec.lean`, `LatticeAndScale`; review `.../checks/CombinedAcceptance.lean`, `finite_law_on_family`, `lattice_and_scale`; original `WilsonBridge.lean`, `law_eq`, `moment_eq`, `fromWilson` | Explicitly retained by the stronger combined acceptance target. Use that target, rather than the public existence headline alone. |
| Common physical spacing independent of volume | Original `PublicWilson.lean`, `WilsonFamily.denominator`, `mesh`, `place`, `smear`; original `WilsonBridge.lean`, `wilsonFamily`; review `.../checks/CommonScaleAudit.lean`, `physical_side` | **Exactly** `a_k=1/d_k`, where `d_k` is a strictly increasing positive integer. Spatial side in lattice units is `d_k L_p`, with integer `L_p`. It is not a spacing `L_p/d_k` depending on volume. |
| Fixed finite stencil, continuity, gauge invariance | Original `YM/Source/Local.lean`, `SectionData.stencil`, `evaluate`, `places`, `Sound`; original `YM/Source/Construction.lean`, `Family.localO`, `continuousO`, `invariant`; original `HierarchyBridge.lean`, `regular` | Direct source statements with the stencil fixed by degree, independent of cutoff and volume. The coefficients can depend on both cutoff and volume. |
| Translation property (F2) | Original `YM/Source/Construction.lean`, `Family.translation`; original `YM/Extraction/LatticeFamily.lean`, `anchored` | Literal finite-cutoff identities, with no rechoice of renormalization at translated anchors. |
| Reflection property (F3) and its relation to the actual field adjoint | Original `YM/Source/Construction.lean`, `Family.rotated`, `reality`; original `YM/Euclid/Register.lean`, `adj`, `star_mirror`; original `YM/Euclid/Null.lean`, `adj_project`; original `YM/Fields/Star.lean`, `starRead`; original `YM/Fields/System.lean`, `Wightman.Realizes.induced`, `adj` | The chain exists. On conjugation-fixed raw labels, time reflection is the induced adjoint. The countable real-token adapter is proved below. Do not identify plain reflection and an antilinear adjoint on arbitrary complex labels without this step. |
| Compact metric phase space, probability measure, **full support** | Original `YM/Phase/Mixture.lean`, `Spread.Resolution`, `Resolution.Out.normalized`, `support`; review `.../checks/AcceptanceSpec.lean`, `PhaseAndOS.phase_full_support`; review `.../checks/CombinedAcceptance.lean`, `phase_and_os` | Full support is explicitly a proved consumer consequence in the review source, not merely a phrase in the assessment. Its definition is `mu.IsOpenPosMeasure`: each nonempty open set has positive measure. |
| Pointwise continuity in the phase for every separated configuration | Original `ChallengeSpec.lean`, `Hierarchy.Reconstructed.characterContinuity`; original `HierarchyBridge.lean`, `publicReconstruction`; original `YM/Phase/Mixture.lean`, `Resolution.Out.weak`, `receives` | Directly proved by evaluating characters on the compressed **whole-word** operator. This is stronger than knowing one selected phase is regular. |
| Pointwise barycenter identity | Same files: `Hierarchy.Reconstructed.mixture`, `publicReconstruction`, `Resolution.barycenter` | Identifies the unselected lattice-limit table with the phase average. It does not identify an individually selected phase with a periodic-volume subsequential limit. |
| Integrability and barycenter identity after smearing | Pointwise data above plus reflection positivity and smoothness | The RP/Fubini lemma below supplies a short mathematical adapter. Pointwise phase continuity alone would not justify exchanging the phase and position integrals. |
| Unique vacuum and Wightman realization in the phases used by (W) | Original `YM/EveryPhase/Extension.lean`, `Completed.isTheory`, `mink`, `all_characters`, `fixedHeat`, `exactly_fixed`; review `AcceptanceSpec.lean`, `SourceConclusions`; original `PublicView.lean`, `view_axioms` | Source statements cover every character, hence also almost every character. `mink` identifies the full zero-energy PVM subspace with the vacuum line, beyond merely one invariant vector. |
| Finite cylinder insertions defined by the same stencil | Original `YM/Source/Local.lean`, `SectionData.evaluate` is a polynomial cylinder on the infinite integer cover | Extend the same polynomial to rectangular periodic configurations by pullback to the cover. Gauge invariance, locality, and time reflection then follow from the cover identities. The external public API itself is written for symmetric tori; this rectangular implementation is an adapter to record, not a separately claimed construction theorem. |
| Inner mesh limit along an arithmetic progression | External denominator is arbitrary strictly increasing integer, not an arithmetic progression | Literal definitions differ. The meshwise ascent and the integer-physical-translation proof do not require an arithmetic progression; see the cofinal formulation below and the companion OS note. Do not assert an AP subsequence exists. |
| The one-scale rectangular partition-function bound at the construction's actual coupling | No discharged counterpart was found in the inspected construction/review targets | This remains the substantive infrared input. It includes the neutral gap and a count of states, as Theorem 7.61 of the paper already explains. |

Stable links for the larger source chains:

- [Acceptance specification](https://github.com/yang-mills-group/YM/blob/55ba9fc36293b3f4d52c6b1f813169a0be76ee98/submissions/openai-20261028/checks/AcceptanceSpec.lean) and [proof](https://github.com/yang-mills-group/YM/blob/55ba9fc36293b3f4d52c6b1f813169a0be76ee98/submissions/openai-20261028/checks/CombinedAcceptance.lean).
- [Actual family and finite-cutoff symmetries](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Source/Construction.lean).
- [Polynomial stencils on the integer cover](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Source/Local.lean).
- [Compact phase space, support, and whole-word characters](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/Phase/Mixture.lean).
- [Pointwise continuity and barycenter adapter](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/HierarchyBridge.lean).
- [All-phase reconstruction and zero-energy vacuum line](https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/YM/EveryPhase/Extension.lean).

## Proved adapter 1: countable real tokens and exact reflection adjoints

Let each raw degree space `V_d` be finite dimensional over the complex numbers, with an antilinear involution `c`, and let the finite signed-coordinate group act complex linearly and commute with `c`. These are the real and signed structures in the source files above.

There is a finite conjugation-fixed complex spanning set in every degree: from a complex basis `v_j`, use

    r_j = (v_j+c(v_j))/2,
    s_j = (v_j-c(v_j))/(2i).

Both are fixed by `c`, and `v_j=r_j+i s_j`. Close this finite set under the finite signed-coordinate group. Its elements remain fixed by `c`, it still spans `V_d`, and it is closed under time reflection. The union over the integer degrees is a countable token set.

For a token `v` of degree `d`, define its cutoff insertion to be zero when `k<ref(d)` and the source insertion otherwise. This changes only finitely many cutoff values for each token and for each finite word. Thus every stated ultraviolet limit is unchanged. It makes the source's eventual `Family.rotated` and `Family.reality` identities sufficient for the all-cutoff version of (F3), while preserving continuity, translation, gauge invariance, and the fixed stencil.

Write `r` for time reflection. On this token set, `c(v)=v`, so the source's raw reflection-adjoint map is `adj(v)=r(v)`. The quotient identity `Table.adj_project` and the reconstruction identity `starRead` then give

    J(pin(project(v))) = pin(project(r(v))).

`Wightman.Realizes.adj` is the actual smeared adjoint identity for these same field operators on their common domain. Therefore the field assigned to the reflected token is the adjoint field required in (W), with the source's Euclidean-to-Minkowski conventions. Complex linear span recovers all raw labels, hence all quotient labels and the same polynomial field domain; restricting to this token set loses no field content.

This is an ordinary finite-dimensional deduction from the inspected source statements, not a new Lean adapter. To make it executable, one still needs to write the explicit token enumeration, the time-axis permutation (the source puts time last), and the rectangular-torus evaluation of the same cover polynomial.

## Proved adapter 2: pointwise phase decomposition implies smeared decomposition

Assume a probability space of phases, smooth separated kernels `S_chi`, a smooth mixed kernel `S`, and the pointwise identities

    S(w) = integral_chi S_chi(w),     S_chi(empty)=1.

Assume each phase is reflection positive, with the same reflected adjoint labels. For every compact set `K` of separated `n`-point configurations and every test `t` supported there,

    integral_chi integral_K |t(x) S_chi(x)| dx dnu(chi)
        <= ||t||_1 sqrt(M_K) < infinity,

for a finite constant `M_K` determined by the mixed reflected-square kernel. Consequently phase-smearing is integrable and

    integral_chi [integral t(x) S_chi(x) dx] dnu(chi)
        = integral t(x) S(x) dx.

Proof. Translate all points of every configuration in `K` by a common time shift `R` so that they lie at strictly positive times, uniformly away from the reflecting plane. The union of a shifted configuration and its reflected copy stays in a compact separated `2n`-point set: points in each half remain distinct, and opposite halves have a uniform time separation. Reflection positivity, applied to the empty word and that whole word, gives the positive two-by-two Gram matrix and hence

    |S_chi(w_x)|^2 <= S_chi(theta_R(w_x) w_x).

If reflection positivity is originally stated for smooth tests, approximate the distinct point insertions by tests in disjoint small balls and pass to the smooth-kernel limit. If some original time coordinates coincide, first perturb them to distinct times and then use continuity of the separated kernels; no point field operator is assumed to exist. Translation invariance removes the common shift from the left side. Integrating in the probability measure of phases and using Cauchy--Schwarz yields

    integral_chi |S_chi(w_x)| <= sqrt(S(theta_R(w_x) w_x)) <= sqrt(M_K).

The last bound follows from smoothness of `S` on the compact separated reflected-square set. Joint measurability follows from continuity in phase at each point and continuity in position at each phase: approximate positions by Borel simple maps with values in a countable dense set and pass to the pointwise limit. Tonelli followed by Fubini proves the assertion. Empty words are immediate.

The pointwise phase continuity, pointwise barycenter, smoothness, and all-phase realization have direct declarations in the ledger. This lemma closes the additional integrability step needed when comparing their pointwise phase API with the smeared form of (W). It does not provide infrared decay.

## Proved adapter 3: support restriction, if full support were not available

For completeness, full support would not be an independent analytic obstruction for the *supported physical mixture*. If `X` is compact metric and `nu` a Borel probability, its support `Y` is closed and compact, `nu(X\Y)=0`, and the induced probability on `Y` gives positive measure to every nonempty relatively open set. A countable base proves the null-complement assertion by expressing that complement as a countable union of zero-measure basic open sets. Restriction preserves all barycenters, continuity, and almost-everywhere phase properties.

Thus a theorem formulated on `Y` loses no state in the mixture. It cannot assert equality with deliberately appended zero-measure phases outside `Y`. In the present external source no restriction is necessary: full support is already explicit.

## Cofinal-integer-denominator version of Theorem F

Use arbitrary strictly increasing positive integers `d_k`, spacings `a_k=1/d_k`, integer physical sides `L_p` tending to infinity, and symmetric lattice sides `d_k L_p`. Require the ordered symmetric-torus limit and phase data of (W) along `k`, with the stencil and adjoint adapters above. No arithmetic-progression extraction of `d_k` is assumed.

For fixed `t0>0` and `0<y0<=1/20`, put

    u0 = 16.83 y0 < 1,     Delta = log(1/u0)/t0.

For every sufficiently large pair `(k,p)`, require an integer

    3 <= T0(k,p) <= d_k t0

such that at the **single coupling beta_(k,p) of that constructed family**,

    log Zhat_beta(s,T0) <= y0 V(s)/(2 (96 T0)^3)

for every integer spatial triple with `2T0 <= s_i < 48T0`. Here `Zhat` is normalized by the leading transfer eigenvalue, exactly as in the paper. This is the original (B*) with its finite time extent and its rectangular window, not only a bound on symmetric tori.

The paper's meshwise ascent applies separately at each `(k,p)`. For `L_p>=2t0`, its conclusions become

    Zhat_(k,p)(d_k L_p)-1 <= 1.9e-11 exp(-Delta L_p/2),
    lambda_1/lambda_0 <= exp(-Delta/d_k).

Indeed `d_k L_p>=2T0`, and `u0^(d_k L_p/(2T0)) <= exp(-Delta L_p/2)`. The physical gap bound is therefore `Delta`, independent of the denominator schedule. No mesh-universality theorem is needed.

For the continuum passage, the proof of Theorem E/F uses integer physical translations, which remain exact grid translations because `d_k` is integral. The companion note `../os/continuum-interface-and-spectral-retention.md` proves this cofinal extension and the positive-energy time-rounding estimate. The external `PublicWilson.mesh` definition has exactly the required reciprocal-integer form. If one elects to use `ceil(d_k t0)` instead, the exact hypothesis above has upper physical extent `t0+1/d_k`; the finite-cutoff rates converge to `Delta`, and one must carry that limit through the gap estimate, rather than silently replace the ceiling by `d_k t0`.

After the same-family (W) adapter is written, these finite estimates and the existing reconstruction passage give the conclusion of Theorem F. The new statements in this note do not establish the displayed one-scale hypothesis.

## Proved adapter 4: raw partition functions and exact coupling matching

Let `m` be the matrix representation dimension. The external action is

    kappa sum_p (1-Re Tr(U_p)/m),

whereas the paper's weight is `exp(m beta sum_p Re Tr(U_p))`. The same normalized Wilson law therefore has

    kappa = m^2 beta.

This is different from the `beta_lgt=kappa/m` conversion in the review's comparison with its separate `lgt` library.

For integer side lengths at least three, let `Z^ext_kappa(s,T)` denote the product-Haar integral with the external action and `Z^paper_beta(s,T)` the raw integral with the paper's weight. There are `6V(s)T` plaquettes, so

    Z^ext_kappa(s,T) = exp(-6 kappa V(s)T) Z^paper_(kappa/m^2)(s,T).

The bulk factors cancel exactly in the finite doubling defect:

    2 log Z^ext_kappa(s,T)-log Z^ext_kappa(s,2T)
      = 2 log Z^paper_(kappa/m^2)(s,T)-log Z^paper_(kappa/m^2)(s,2T).

Hence Proposition 7.57's (B**) can be checked directly using the external action, without extracting an unknown vacuum energy or normalizing a transfer matrix. This is an algebraic identity for the same coupling on all tori in the comparison.

A useful finite continuity bound makes the tuning issue quantitative. Put

    D_kappa(s,T) = 2 log Z^ext_kappa(s,T)-log Z^ext_kappa(s,2T).

The one-plaquette energy is between zero and two. Differentiation of the finite compact integral gives

    |D_kappa(s,T)-D_kappa'(s,T)| <= 24 V(s) T |kappa-kappa'|.

Proof: `d log Z_kappa/dkappa=-E_kappa(sum_p energy_p)`. The smaller torus has `n=6V(s)T` plaquettes and the doubled torus has `2n`; thus the derivative of the defect lies in `[-4n,4n]`. Integrate that derivative.

This bound is sufficient for transferring a defect estimate with a margin when the coupling mismatch is `O(T^-4)` with an appropriately small constant. It does **not** say that such precision is necessary; cancellation could improve it. It does show why merely matching the leading asymptotic-freedom coefficient, or knowing that volume-dependent tunings differ by a bounded amount, is no proved transfer argument for (B**).

The actionable infrared target is therefore the following exact finite inequality, uniformly along the accepted family, at some fixed physical `t0`:

    2 log Z^ext_(kappa_(k,p))(s,T0)
      -log Z^ext_(kappa_(k,p))(s,2T0)
        <= y0 V(s)/(2 (96 T0)^3),

with `3<=T0<=d_k t0`, every `s_i` in `[2T0,48T0)`, and the **same** `kappa_(k,p)` in both raw integrals and throughout the window. Establishing this at separately retuned couplings attached to the different rectangular volumes would need an additional error estimate.

## What has and has not advanced

The source audit locates explicit full support, pointwise phase continuity, all-phase vacuum uniqueness, fixed stencils, and the induced adjoint on the same accepted construction witness. The real-token and RP/Fubini arguments remove two small mathematical mismatches in the stated interfaces; the normalization identity gives an exact finite target in the external convention. The arbitrary-denominator condition is a harmless cofinal generalization for this construction, not an additional ultraviolet universality problem.

No inspected primary theorem proves the required one-scale rectangular defect bound at weak coupling. A Gaussian fibre comparison, short-distance asymptotic freedom, the existence of a nonzero local probe, and a centre-twist estimate do not supply that bound. There is no unconditional closure here.

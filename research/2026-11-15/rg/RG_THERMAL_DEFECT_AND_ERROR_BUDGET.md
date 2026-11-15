# RG transport through a thermal defect and a quantitative ascent error budget

Date: 2026-11-15. This is a proved arithmetic reduction and a specification of missing model estimates. It is not an unconditional Yang--Mills mass-gap proof.

## Source state and existing results

The default branch was read at commit `2e36be0f89e50aeabeb3844418cf9ad58b1e7fd9`. Its `README.md` explicitly lists the weak-coupling one-scale bound, the Wightman limit, the weak-coupling lattice gap, and the neutral glueball gap/count as open. `YangMills/RunningCoupling.lean` proves inversion and limiting properties of the explicitly defined one-loop function. It does not construct the exact blocked Wilson measure, identify its nonperturbative running coupling, or bound a terminal effective action.

The current 170-page paper was checked from branch `paper`, commit `50095e99694feea0d72a9cd1495ea4d88efddb4e`, file `papers/4Y-MPaper.pdf`, SHA256 `c5aba3f0ea29f6fe565f832b0693da3352790dd331703a8e21b2454393ad4d5f`. It agrees byte-for-byte with the root task's downloaded copy. The relevant existing statements are:

- Theorem 7.56, printed pp. 59--60: the exact gap-free ascent `y_{i+1}=16(exp(y_i)-1)^2`, with `y_0 <= 1/20`, yields a gap and vacuum dominance. The theorem already remarks that any initial value below the positive fixed point works with modified constants; increasing `1/20` to approximately `0.0589` is therefore not a new advance.
- Proposition 7.57, printed p. 61: the finite thermal defect `Psi_s(T)=2 log Z(s,T)-log Z(s,2T)` controls the vacuum-normalized trace, with `log calZ_s(T) <= Psi_s(T) <= 2 log calZ_s(T)`. Its sufficient datum is invariant under multiplication of `Z(s,T)` by a factor exponential in four-volume.
- Section 11.8, printed pp. 117--119, especially (11.3): a response estimate after blocking, uniform over the relevant boxes and exterior configurations, is an unproved weak-coupling input. The paper already discusses why a Hilbert--Schmidt density bound can grow with transverse area while the relevant operator norm does not.
- Section 12, printed pp. 120--121: intermediate coupling and transport back to the fine lattice are both missing. The text does not claim that ultraviolet estimates continue through an order-one running coupling.

Primary repository links: [main tree](https://github.com/anaxia-research/4Y-M/tree/2e36be0f89e50aeabeb3844418cf9ad58b1e7fd9), [paper](https://github.com/anaxia-research/4Y-M/blob/50095e99694feea0d72a9cd1495ea4d88efddb4e/papers/4Y-MPaper.pdf), [one-loop definition and theorems](https://github.com/anaxia-research/4Y-M/blob/2e36be0f89e50aeabeb3844418cf9ad58b1e7fd9/YangMills/RunningCoupling.lean).

An additional bibliographic check: Dimock's *The Renormalization Group According to Balaban -- I. Small fields*, [arXiv:1108.1335](https://arxiv.org/abs/1108.1335), explicitly treats a scalar phi-four model in three dimensions. It is an exposition of the method, not a proved four-dimensional Yang--Mills infrared bridge. No estimate needed below is imported from that paper.

## 1. Exact transport needs only the finite thermal defect

Write `F_f(s,T)=log Z_f(s,T)`, where `s` has spatial volume `V`, and let `b` divide its three sides and `T`. Set `tau=T/b`, `V_c=V/b^3`. Suppose an exact integration or comparison establishes

```text
F_f(s,t) = alpha * V * t + F_c(s/b,t/b) + R(s,t),    t=T,2T.       (1)
```

The coefficient `alpha` may depend on cutoff and coupling. It must be the same at the two time extents. The coarse partition function is positive. No transfer matrix for the coarse reference is needed for the following identity.

**Thermal-defect transfer lemma.** Define `Psi=2F(T)-F(2T)`. Then

```text
Psi_f(s,T) = Psi_c(s/b,tau) + 2 R(s,T) - R(s,2T).                (2)
```

In particular, if

```text
Psi_c(s/b,tau) <= gamma_c V_c,
2 R(s,T)-R(s,2T) <= eta V,
```

then `Psi_f(s,T) <= gamma_f V`, with

```text
gamma_f = gamma_c/b^3 + eta.
```

The dimensionless invariant from Theorem 7.56 transforms as

```text
y_f := 2 gamma_f (96T)^3
     = y_c + 2 eta (96T)^3,
y_c := 2 gamma_c (96tau)^3.                                    (3)
```

**Proof.** Twice the bulk term at `T` equals the bulk term at `2T`, so it cancels exactly. Substituting the two bounds in (2) proves the first inequality. Substitute `T=b tau` in the definition of `y_f` to obtain (3). All equalities and inequalities are finite-volume statements. QED.

Thus a margin `delta=1/20-y_c>0` is preserved whenever

```text
eta <= delta / (2(96T)^3).                                      (4)
```

The bounds have to hold uniformly for every spatial shape in the base window and for every cutoff required by Theorem F. They must also include every large-field and topological sector in the fine partition function. Divisibility is an explicit restriction of this simple statement: to cover all integer shapes in the paper, one must provide an exact treatment of leftover boundary strips or another rounding comparison with its own error budget.

Equation (2) provides a weaker target than transport of every observable or of a boundary-uniform slab norm. An effective action need not return to Wilson form for this scalar partition-function comparison to be useful. The reflection positivity and transfer-matrix statements used after this transport are those of the original fine Wilson theory. Establishing (1) with an error satisfying (4) remains an unproved model-specific input.

### Bulk ultraviolet stability is quantitatively too weak for this comparison

Suppose only a separate free-energy remainder bound is available:

```text
|R(s,t)| <= epsilon V t,    t=T,2T.
```

Then the triangle inequality gives `|2R(s,T)-R(s,2T)| <= 4 epsilon V T`. By (3), the dimensionless loss is at most

```text
8 epsilon 96^3 T^4.                                            (5)
```

To preserve a fixed margin `delta`, this estimate requires

```text
epsilon <= delta / (8 * 96^3 * T^4).
```

At fixed physical time, `T` grows proportionally to the inverse spacing. An error density bounded by a constant, or merely tending to zero with inverse logarithms of the cutoff, does not satisfy this sufficient precision bound. This statement is about what can be deduced from the separate remainder bounds; it does not say that the true thermal defect is large. An extensive term exactly linear in time cancels regardless of size. Controlling the *difference* in (2) retains that cancellation.

For a sequence of exact RG steps with blocking factors `b_k`, let `R_k` be measured at scale `k`, volume `V/b_k^3` and time `T_k=T/b_k`. If its thermal defect is bounded by `eta_k V/b_k^3`, the total dimensionless loss is bounded by

```text
sum_k 2 eta_k (96T_k)^3.                                       (6)
```

Hence a summable budget of thermal defects suffices; separate uniform bounds on each complete effective action are stronger and can discard the relevant cancellations.

## 2. Error-stable gap-free ascent

The following arithmetic theorem is implemented in [`YangMills/ErrorStableAscent.lean`](../../../YangMills/ErrorStableAscent.lean), under namespace `YangMills.ErrorStableAscent`. The file contains proofs with no axioms or `sorry`. Compilation status is reported by the root task; this note does not infer compilation from a text audit.

**Normalized theorem.** Let `z_i>=0`, `0<=c<=1`, `0<=q<=1`, and suppose

```text
z_0 <= c q,
z_{i+1} <= z_i^2 + e_i,
e_i <= c(1-c) q^(2^(i+1)).                                     (7)
```

Then, for every `i>=0`,

```text
z_i <= c q^(2^i).                                              (8)
```

Nonnegativity of `e_i` is not needed for this algebraic implication; nonnegative errors are the intended application.

**Proof.** The base case is (7). If (8) holds at `i`, nonnegativity allows squaring, and

```text
z_{i+1}
 <= c^2 q^(2^(i+1)) + c(1-c) q^(2^(i+1))
  = c q^(2^(i+1)).
```

This proves the induction. QED.

**Unnormalized theorem.** If `A>0`, `y_i>=0`, and

```text
y_{i+1} <= A y_i^2 + epsilon_i,
A y_0 <= c q,
A epsilon_i <= c(1-c) q^(2^(i+1)),                              (9)
```

then `A y_i <= c q^(2^i)`. This follows by taking `z_i=A y_i` and `e_i=A epsilon_i`, since multiplying the first inequality by `A` gives `z_{i+1}<=z_i^2+e_i`.

**Variable budget.** More generally, take nonnegative coefficients `b_i` and errors with

```text
b_i^2 + eta_i <= b_{i+1},
e_i <= eta_i q^(2^(i+1)),
z_0 <= b_0 q.
```

Then `z_i<=b_i q^(2^i)`. The proof is the same induction. The Lean implementation proves this more general statement first, then obtains the fixed reserve by `b_i=c`, `eta_i=c(1-c)`.

### Application to the paper's constants

For `0<=y<=1/20`, the existing `YangMills.GapFree.exp_sub_one_le` and `YangMills.GapFree.doubling_step` already prove the bounds used in Theorem 7.56:

```text
exp(y)-1 <= 1.0255 y,
16(exp(y)-1)^2 <= 16.83 y^2.
```

If an approximate argument establishes

```text
0 <= y_{i+1} <= 16(exp(y_i)-1)^2 + epsilon_i,
```

choose `A=16.83`, `c,q in (0,1)` with `c q/A<=1/20`, and impose the base/error bounds (9). A simultaneous induction proves both `y_i<=1/20` and `A y_i<=c q^(2^i)`, because `q^(2^i)<=q`. Thus the analytic majorant is used only inside its valid interval. This simultaneous induction is implemented as `exponential_error_stable_ascent`, importing the existing `YangMills.GapFree` result instead of duplicating its analytic proof.

For the original base value `y_0=1/20`, an exact rational choice is

```text
A=1683/100,   c=9/10,   q=187/200,
c q = A/20 = 1683/2000.
```

The error budget becomes

```text
epsilon_i <= (3/561) (187/200)^(2^(i+1)).                       (10)
```

Here `c(1-c)/A = (9/100)/(1683/100)=9/1683=3/561`. This is a concrete nonzero error reserve. It sacrifices some decay rate compared with the exact zero-error ascent.

**Spectral consequence, conditional on the same trace-to-spectrum estimate.** Suppose, for every relevant torus in the scale-`i` window, one has the paper's estimate

```text
r_1^(2^i T_0) <= exp(y_i)-1 <= 1.0255 y_i.
```

Since `1.0255 c/A<1` for `A=16.83` and `c<=1`, (8) gives

```text
r_1 <= q^(1/T_0),   m_lattice >= -log(q)/T_0.                   (11)
```

If the lattice spacing is `1/N` and `T_0<=N t_0`, then `N m_lattice >= -log(q)/t_0`. For the rational example, `-log(187/200)` is approximately `0.06721`. This is an implication of the error and trace bounds; none of those bounds is established here for weak-coupling Yang--Mills.

If the finite defect transfer in Section 1 already gives the exact fine-theory base bound, the original fine-theory positivity argument runs with *zero* subsequent ascent error. In that case it is preferable to spend an error budget only once, at the base, instead of carrying approximate RG errors through every scale. The noisy theorem is useful when the recurrence itself is what has been established approximately.

## 3. What rate of approximation suffices

An error exponential in `2^i` is exponential in the physical time `2^i T_0`, not an unusually strong exponential in physical scale.

For example, suppose an actual model analysis gives

```text
epsilon_i <= K 2^(p i) exp(-mu T_0 2^i),   K,p>=0.
```

Put `a=-log q>0` and `beta=mu T_0-2a`. A simple sufficient condition for (9) is

```text
beta >= p log 2,
A K exp(-beta) <= c(1-c).                                     (12)
```

Indeed, the scaled remainder is at most `A K 2^(p i) exp(-beta 2^i)`. The ratio of this expression at `i+1` to its value at `i` is `2^p exp(-beta 2^i)<=1` under (12), so its maximum is at `i=0`. This proves the required uniform bound.

If a convergent cluster argument supplies exact cancellation of nonwrapping clusters together with an exponential bound on the *remaining thermal defect*, (12) specifies how much decay and prefactor control is sufficient. The existence, cancellation, and summability of such a decomposition for the required Yang--Mills terminal measure are additional hypotheses here. A generic small-field expansion or a rare-large-field statement does not supply them by itself.

By contrast, the scalar recurrence alone cannot turn a fixed additive tolerance into a gap certificate. For `0<epsilon<1/(4A)`, take the small positive solution

```text
r = (1-sqrt(1-4A epsilon))/(2A)
```

of `r=A r^2+epsilon`. The constant sequence `y_i=r` obeys the noisy recurrence exactly and does not approach zero. Its trace upper bound yields only `r_1<=constant^(1/(2^i T_0))`, which approaches one. Likewise a merely geometric tolerance `epsilon_i=K theta^i`, `0<theta<1`, permits `y_i=(K/theta)theta^i`, since `y_{i+1}=epsilon_i<=A y_i^2+epsilon_i`; its logarithm divided by `2^i T_0` tends to zero. These examples refute a guarantee from those scalar tolerances alone. They are not counterexamples to the Wilson theory.

## Remaining unconditional input

The exact fine/coarse identity, the coarse base-window thermal bound, and a uniform error estimate (4) or (6) must still be proved for the full four-dimensional nonabelian measure through the order-one coupling regime. An alternative would prove the actual noisy recurrence and the exponentially physical error budget (9). The arithmetic result does not provide either estimate. Separately, the source-level and mathematical adapters to the external Wightman construction must be recorded on the same witness; the companion [construction interface audit](../literature/construction-to-theorem-f-interface.md) verifies several of these ingredients. This note does not assert that the external existence theorem is absent, or that a complete formal bridge has already been built. No one-loop formula, theorem count, or finite numerical sample removes these analytic requirements.

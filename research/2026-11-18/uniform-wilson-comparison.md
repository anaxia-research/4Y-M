# A uniform approximation to the Wilson thermal defect

Fix the four-dimensional periodic Wilson lattice with gauge group \(SU(2)\), normalized product Haar measure and plaquette weight \(\exp(bx_p)\), where \(x_p=\tfrac12\operatorname{ReTr}U_p\). Put \(s=(2T,2T,2T)\) for an integer \(T\ge3\), and use the same \(s,b\) for both time lengths. The one-cube test in the manuscript asks for

\[
 \psi_b(T)=2\log Z_b(s,T)-\log Z_b(s,2T)\le 1/4097 .
\]

Along a continuum tuning the test must succeed at some \(3\le T\le t_0/a\) with a common physical time bound \(t_0\), for all sufficiently fine cutoffs in the family. The result below bounds the error in computing the left-hand side. Its value on the tuned cubes is still unknown.

## Polynomial comparison on the actual Wilson lattice

For \(M=T,2T\), let \(n_M=6(2T)^3M\) count plaquettes, once per base vertex and unordered pair of axes. Define

\[
 P_{M,K}(b)=\int\prod_p\left(\sum_{r=0}^{K}
       \frac{b^r(1+x_p)^r}{r!}\right)dU,\qquad
 \psi_{b,K}(T)=\log\frac{P_{T,K}(b)^2}{P_{2T,K}(b)} .
\]

**Proposition.** For \(b\ge0\) and \(0<\delta\le1\), the integer

\[
 K=3\lceil b\rceil+
 \left\lceil\log_2\!\left(\frac{192T^4}{\delta}\right)\right\rceil
\]

gives \(\lvert\psi_b(T)-\psi_{b,K}(T)\rvert\le\delta\). The constant holds for every field and both time lengths, with arbitrary plaquette correlations. The polynomials \(P_{M,K}\) have nonnegative rational coefficients and constant term one.

**Proof.** Write \(z=b(1+x_p)\in[0,2b]\). The ratio of the truncated weight \(e^{-b}\sum_{r=0}^K z^r/r!\) to the Wilson weight is the probability that a Poisson random variable \(N\) of mean \(z\) satisfies \(N\le K\). From \(\mathbb E 2^N=e^z\) we get

\[
 \mathbb P(N>K)\le 2^{-(K+1)}e^{2b}
 \le 2^{-(K+1)+3\lceil b\rceil}\le \eta,\qquad
 \eta=\frac{\delta}{192T^4}.
\]

Here \(e^2<8\). The Poisson variable is used only to estimate the scalar exponential series. Multiplication of the pointwise inequalities and Haar integration give

\[
 0\le d_M:=\log Z_b(s,M)-\log(e^{-bn_M}P_{M,K}(b))
 \le -n_M\log(1-\eta).
\]

Since \(n_{2T}=2n_T=96T^4\), the deterministic factors cancel and \(\psi_b-\psi_{b,K}=2d_T-d_{2T}\). Both \(2d_T\) and \(d_{2T}\) belong to the same interval \([0,-96T^4\log(1-\eta)]\). Its length is at most \(192T^4\eta=\delta\), using \(0\le\eta\le1/2\).

For rationality identify each \(SU(2)\) link with a unit quaternion. The scalar part of the ordered plaquette product is a polynomial with integer coefficients in the link coordinates, since inversion is quaternion conjugation. Haar measure is uniform on \(S^3\). A monomial with any odd coordinate power integrates to zero. For even powers the integral on one link is

\[
 \int_{S^3}\prod_{i=1}^4 u_i^{2m_i}\,d\sigma(u)=
 \frac{\prod_i(1/2)_{m_i}}{(2)_{\sum_i m_i}},
\]

where \((z)_m=z(z+1)\cdots(z+m-1)\) and \((z)_0=1\). To see this, take a standard four-dimensional Gaussian \(G\) with direction \(U\) independent of its length. Its coordinate even moments are \(2^{m_i}(1/2)_{m_i}\), and its radial moment of order \(2m\) is \(2^m(2)_m\). Divide the first product by the radial moment. Independence of the link Haar measures now gives a rational integral term by term. Before expanding in quaternion coordinates, each coefficient in \(b\) integrates a sum of nonnegative multiples of products of \(1+x_p\ge0\), so each coefficient is nonnegative. This finishes the proof.

**One-sided test.** Set \(\delta=1/8194\). At the chosen coupling the polynomial inequality

\[
  8194\,P_{T,K}(b)^2 \le 8195\,P_{2T,K}(b)
\]

implies \(\psi_b(T)<1/4097\), since \(\log(1+1/8194)<1/8194\). At rational \(b\) this test involves rational arithmetic only. A common \(K\) based on an upper endpoint also works throughout a bounded interval of couplings. No estimate on the number of operations needed for the polynomial integrations is asserted. Taking a smaller \(\delta\) permits certification arbitrarily close to the strict threshold.

The required degree per plaquette grows as \(O(b+\log T+\log(1/\delta))\), but the number of plaquettes grows as \(T^4\). Positive coefficients of the two partition polynomials give no comparison of their difference. The uniform inequality for their ratio along the tuning is the unresolved step in this approach.

## What gauge invariance removes exactly

On the connected spatial torus, order the \(3V\) terminal links by first revealing the \(V-1\) links of a spanning tree, where \(V=(2T)^3\). The Wilson transfer kernel is invariant under independent gauge transformations of its initial and terminal slices. Its positive normalized vacuum eigenfunction is gauge invariant, by simplicity and preservation of its norm. Consequently the vacuum measure and each fixed-initial-field transition row of its vacuum-normalized Markov chain are gauge invariant in the terminal field, for every integer time \(t\ge1\).

Root the tree and fix the gauge transformation at its root to the identity. A gauge transformation \(q_e\mapsto g_xq_e g_y^{-1}\) on each parent-child edge can carry any tree assignment to any prescribed assignment, solving for the child transformation recursively. Averaging independent Haar transformations at the non-root vertices makes the tree links independent Haar variables: conditional on previously drawn ancestor transformations, each new child supplies an independent Haar variable. Thus the tree marginals of the vacuum and transition row agree exactly. All \(V-1\) tree likelihood ratios equal one, and their conditional variances vanish for every coupling. The manuscript's squared-likelihood identity therefore has only \(2V+1\) potentially nonzero contributions. Gauge symmetry alone gives no decay over physical time for these remaining cycle variables.

## Source

The conventions, continuum quantifiers and thermal-defect criterion are those of the [current manuscript, Paper-2](https://github.com/anaxia-research/4Y-M/tree/9a509337304580499bfd81409aaca7af00ffc549/Paper-2).

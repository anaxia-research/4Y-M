# Conditional vacuum inequalities and a tilted Fisher criterion

18 November 2026. These are exact finite-cutoff results. They provide a volume-independent one-link conditional Poincare constant and a sufficient Fisher-information budget for the one-cube datum. The required Fisher budget is not established along the weak-coupling tuning.

## 1. A complete conditional chi-square to score theorem

Let pi be a probability law on a finite product Y=Y_1 times ... times Y_k, with a strictly positive smooth density relative to product Riemannian volume, each Y_j connected and compact. Let x have law pi independently of y. Suppose p(x,y)>0 is a smooth likelihood satisfying integral p(x,y) pi(dy)=1 for every x. Write pi_j(dy_j|y_<j) for its terminal conditional distributions. Define the conditional likelihoods

\[
\ell_j(x,y_{\le j})=
\frac{dP(x,dy_j\mid y_{<j})}{d\pi_j(dy_j\mid y_{<j})},
\qquad p(x,y)=\prod_{j=1}^k\ell_j(x,y_{\le j}).
\]

Here P(x,dy)=p(x,y)pi(dy). Conditional densities are obtained from conditional expectations of p; strict positivity makes all denominators positive. Put

\[
W_j=\prod_{i=1}^j\ell_i^2,\qquad
S_j=\int W_j\,d(\pi\otimes\pi),\quad W_0=S_0=1,
\]

and let theta_j be the probability distribution on (x,y_<=j) with density W_j/S_j relative to the corresponding marginal of pi tensor pi. In particular theta_j contains y_j, whereas theta_{j-1} does not. Define

\[
q_j=\mathbb E_{\theta_{j-1}}\chi_j^2,
\qquad
\chi_j^2=\int (\ell_j-1)^2\,d\pi_j.
\]

The exact chain identity is S_j/S_{j-1}=1+q_j.

**Theorem 1 (weighted conditional Fisher budget).** Suppose, at each history (x,y_<j), the conditional law pi_j satisfies

\[
\operatorname{Var}_{\pi_j}(f)\le
C_j(x,y_{<j})\int \|\nabla_j f\|^2\,d\pi_j
\tag{1}
\]

for smooth real f, with a measurable finite coefficient C_j. (The conditional law does not depend on x, but allowing C_j to do so permits a valid history-dependent upper bound.) Set

\[
\eta_j=
\mathbb E_{\theta_j}\left[
C_j(x,y_{<j})\|\nabla_j\log\ell_j\|^2\right].
\tag{2}
\]

If every eta_j<1, then

\[
q_j\le\frac{\eta_j}{1-\eta_j},\qquad
\log S_k\le\sum_{j=1}^k-\log(1-\eta_j).
\tag{3}
\]

If sum eta_j<=s<1, the stronger common-budget bound is

\[
\log S_k\le-\log(1-s).
\tag{4}
\]

**Proof.** The conditional mean of ell_j is one, so its conditional variance is chi_j squared. Applying (1) to ell_j, multiplying by W_{j-1} and integrating gives

\[
S_j-S_{j-1}
\le\int W_{j-1}C_j\|\nabla_j\ell_j\|^2\,d(\pi\otimes\pi)
=S_j\eta_j.
\]

The last equality uses grad ell_j=ell_j grad log ell_j and the definition of theta_j. Dividing by S_j gives q_j/(1+q_j)<=eta_j, and rearrangement proves the first inequality in (3). Telescoping log S_k=sum log(1+q_j) proves the second. Since every eta_j>=0, induction gives product_j(1-eta_j)>=1-sum_j eta_j>=1-s; taking minus the logarithm proves (4). QED.

For a reversible Markov operator P unitarily equivalent to a nonnegative transfer contraction R and likelihood p=p_t of P^t, one has S_k=Tr R^{2t} by the Hilbert--Schmidt identity. On the paper's even time scale T=2t this means

\[
X_s(T)\le\sum_j-\log(1-\eta_j).
\tag{5}
\]

A sufficient condition for X_s(T)<=1/8194 is

\[
\sum_j\eta_j\le 1-e^{-1/8194}.
\tag{6}
\]

The simpler, slightly stronger rational condition

\[
\sum_j\eta_j\le\frac1{8195}
\tag{7}
\]

also suffices: for 0<=s<1, -log(1-s)<=s/(1-s), so s<=1/8195 gives -log(1-s)<=1/8194. Then psi_s(T)<=2X_s(T)<=1/4097. On s=(2T)^3 this is the one-cube datum. The earlier conservative budget 1/16388 is valid but unnecessary.

This argument has no lower density floor for p_t and does not replace theta_j by the stationary law. It does require the weighted score averages (2). If ell_j can vanish, formulate the right side first as the integral of C_j |grad ell_j|^2, rather than dividing by ell_j; the positive Wilson case avoids that issue. For disconnected supports a gradient-only Poincare inequality can fail; a jump Dirichlet form or a connected-support assumption is essential. The Wilson SU(2) conditional laws used below have smooth positive densities on the connected manifold S^3, so this caveat does not arise.

## 2. A volume-independent conditional inequality for the actual Wilson vacuum

Fix the three-dimensional spatial torus with every side at least three. Let b=beta_W>=0 and

\[
T_b(Q,Q')=D_b(Q)A_b(Q,Q')D_b(Q'),\quad
D_b(Q)=e^{S_{\mathrm{sp}}(Q)/2},\quad
S_{\mathrm{sp}}(Q)=\frac b2\sum_{p\text{ spatial}}\operatorname{ReTr}Q_p.
\]

Let h_b>0 be the unit Perron eigenfunction of this exact SU(2) transfer operator, and pi_b(dQ)=h_b(Q)^2dQ its vacuum law. Every Haar measure is normalized to mass one. Equip each SU(2) factor with its unit-round-S^3 metric and each product with the product metric.

**Theorem 2 (conditional vacuum Poincare bound).** Order the spatial links arbitrarily and reveal them in that order. For every prefix history, the conditional law of the next link under pi_b has density rho_j relative to Haar satisfying

\[
\frac{\rho_j(u)}{\rho_j(v)}\le e^{12b}
\qquad(u,v\in\mathrm{SU}(2)),
\tag{8}
\]

and hence

\[
\operatorname{Var}_{\pi_{b,j}}(f)
\le\frac{e^{12b}}3\int\|\nabla f\|^2\,d\pi_{b,j}.
\tag{9}
\]

These constants are independent of the spatial volume, the ordering and the particular prefix history. They depend exponentially on b and do not give a coupling-uniform mass gap.

**Proof.** If Q and Qtilde differ in one spatial link, that link occurs in four spatial plaquettes. Each plaquette term (b/2) ReTr Q_p lies in [-b,b], so

\[
|S_{\mathrm{sp}}(Q)-S_{\mathrm{sp}}(\widetilde Q)|\le8b.
\tag{10}
\]

In the temporal action defining A_b, a bottom spatial link appears in exactly one temporal plaquette. For every fixed Q' and every temporal field, changing that link changes the exponent by at most 2b. Pointwise comparison of the integrands, followed by temporal Haar integration, gives

\[
e^{-2b}\le\frac{A_b(Q,Q')}{A_b(\widetilde Q,Q')}\le e^{2b}.
\tag{11}
\]

Put g_b=h_b/D_b. The Perron equation becomes

\[
\lambda_b g_b(Q)=
\int A_b(Q,Q')D_b(Q')h_b(Q')\,dQ'.
\]

The weight in this integral is positive and independent of Q. Applying (11) under the integral yields g_b(Q)/g_b(Qtilde) in [e^{-2b},e^{2b}]. Since h_b^2=e^{S_sp}g_b^2, (10) gives

\[
\frac{h_b(Q)^2}{h_b(\widetilde Q)^2}\le e^{8b}e^{4b}=e^{12b}.
\tag{12}
\]

Fix a prefix, replace the next link u by v, and integrate the remaining links with their product Haar measure. Inequality (12) holds pointwise in those remaining links, so their integrals obey the same ratio. Normalization of the resulting one-link conditional density cancels in its ratio. This proves (8).

The first nonzero Laplace--Beltrami eigenvalue of the unit round S^3 is 3, hence Haar satisfies Var_Haar f<=(1/3) integral |grad f|^2 dHaar. If m_j and M_j are the minimum and maximum of rho_j, (8) gives M_j/m_j<=e^{12b}. Taking the Haar mean as a comparison constant in the variational formula for variance gives

\[
\operatorname{Var}_{\pi_{b,j}}f
\le M_j\operatorname{Var}_{\mathrm{Haar}}f
\le\frac{M_j}{3}\int|\nabla f|^2d\mathrm{Haar}
\le\frac{M_j}{3m_j}\int|\nabla f|^2d\pi_{b,j}.
\]

This proves (9). Smoothness needed above follows at fixed volume because the Wilson kernel is smooth on a compact product group, all derivatives can be passed through its integral, and h_b=lambda_b^{-1}T_b h_b. Strict positivity makes h_b bounded below by a positive constant. QED.

The same local ratio 12b holds for a compact connected matrix subgroup with temporal exponent (b/N_c) sum ReTr(...) and spatial exponent (b/N_c) sum ReTr Q_p. Replace 1/3 by the Haar Poincare constant for the explicitly chosen metric. For a block containing r links, changing links one at a time gives density ratio at most e^{12br}; comparison with product Haar gives its Poincare constant at most C_G e^{12br}. Using single-link blocks avoids that extra exponential block-size loss.

The theorem is about the exact unconditioned transfer-vacuum law and its prefix conditionals. It makes no assertion for a law restricted to labels, calm charts, a specified coarse fibre or a disconnected bad set.

## 3. The combined exact Wilson target

Take the Doob Markov kernel of the same transfer operator and its time-t density p_t. Reveal each of the 3V terminal spatial links separately. Applying Theorem 1 and Theorem 2 gives

\[
\eta_j=\frac{e^{12b}}3
\mathbb E_{\theta_j}\|\nabla_{y_j}\log\ell_j\|^2,
\qquad
X_s(2t)\le\sum_j-\log(1-\eta_j)
\tag{13}
\]

whenever every eta_j<1. Consequently the concrete sufficient score estimate

\[
\sum_{j=1}^{3V}\mathbb E_{\theta_j}
\|\nabla_{y_j}\log\ell_j\|^2
\le\frac{3e^{-12b}}{8195}
\tag{14}
\]

would imply the one-cube datum at the even scale T=2t and s=(2T)^3. Both the law and the conditional Poincare estimate are actual Wilson objects, not a product-law replacement. The remaining estimate (14) is still unproved along the continuum tuning. The bound is volume independent on the Poincare side, but the number of scores is 3V and the factor e^{-12b} shrinks with the tuned coupling. Under a logarithmic tuning b(a)=kappa log(1/a)+O(1), the comparison factor e^{12b(a)} grows as a^{-12kappa} up to constants; it is not an exponential in the whole lattice volume. This is a quantified improvement over a global density-oscillation comparison, not a completion of the required score-decay estimate.

## 4. Why untilted averages cannot replace the weighted score/chi-square targets

Here is a full-support reversible positive-operator example stronger than merely finding two unequal averages.

Let M>=2, 0<delta<1 and 0<theta<1. The state space is the product {0,1} times {1,...,M}. Its stationary law has independent coordinates, with pi(J=1)=delta and K uniform. Define the label L(J,K) to be one common label when J=0, and the individual label K when J=1. Let Kcal be conditional expectation onto functions of L: it forgets K on the common group but keeps it on the rare group. This is an orthogonal Markov projection on L^2(pi), of rank M+1. Let Jcal be expectation onto constants and

\[
P=\theta\mathcal K+(1-\theta)\mathcal J.
\]

Both projections commute, Jcal Kcal=Jcal, so P is reversible and nonnegative, with eigenvalues 1, theta (multiplicity M), and zero (multiplicity M-1). Its transition density relative to pi is strictly positive, bounded below by 1-theta.

Reveal the terminal variables Y_1=J_y and Y_2=K_y. The first likelihood is

\[
\ell_1=1-\theta+\theta\frac{\mathbf 1[J_x=J_y]}{\pi(J_y)},
\qquad S_1=1+\theta^2,
\qquad\mathbb E_{\pi\otimes\pi}\chi_1^2=\theta^2.
\]

Every second conditional likelihood is one unless J_x=J_y=1. On that rare matching history,

\[
\ell_2=1+c\bigl(M\mathbf 1[K_x=K_y]-1\bigr),\qquad
c=\frac{\theta}{\theta+(1-\theta)\delta},\qquad
\chi_2^2=c^2(M-1).
\]

The bare probability of the rare matching history is delta squared; its partial-likelihood-square weight is ell_1 squared. Therefore, exactly,

\[
\mathbb E_{\pi\otimes\pi}\chi_2^2
=\delta^2c^2(M-1),\qquad
\mathbb E_{\theta_1}\chi_2^2
=\frac{\theta^2(M-1)}{1+\theta^2},\qquad
\operatorname{Tr}P^2=1+M\theta^2.
\tag{15}
\]

Now take an integer n>=2 and set M=n^3, delta=n^{-3}, theta=n^{-1}. Then both untilted block means tend to zero:

\[
\mathbb E\chi_1^2=n^{-2},\qquad
\mathbb E\chi_2^2<n^{-3}.
\]

But

\[
\mathbb E_{\theta_1}\chi_2^2=\frac{n^3-1}{n^2+1}\longrightarrow\infty,
\qquad\operatorname{Tr}P^2=1+n\longrightarrow\infty.
\]

Even the spectral contraction theta tends to zero. Thus neither small untilted conditional chi-square means nor a strong spectral gap alone controls the thermal state count. This is a finite reversible counterexample, not a Wilson model. It does not disprove (14); it explains why the theta_j weighting in that target is indispensable.

## 5. Scope

Proved here: the conditional Fisher criterion; the volume-independent one-link vacuum conditional Poincare estimate for the exact Wilson transfer matrix; their combination; and the counterexample excluding a tempting replacement of the tilted measures. Not proved here: the Fisher-information decay (14) at growing physical block size along the tuned coupling, the full weak-coupling one-cube datum, or the unconditional Clay mass-gap theorem.

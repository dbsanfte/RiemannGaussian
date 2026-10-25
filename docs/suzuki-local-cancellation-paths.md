# Repository paths to the local Suzuki prime estimate

23 October 2026. Follow-up to the request to search the recent semiprime
factoring and other investigations. This is a research synthesis, not a new
Lean theorem or an assertion of (T).

The search found two concrete arithmetic directions. No inspected note
supplies the missing signed estimate. The Vaughan calculation below has
now been developed into the more precise
[coprime prime/Möbius reduction](suzuki-local-cancellation-vaughan.md):
exponent-dependent cutoffs pay every proper-power and shared-prime sector
within the desired error allowance. The joined ordinary-prime remainder
is still open. A second route
uses the factoring notes' same-prime/distinct-prime energy split to isolate a
precise prime-pair covariance. The finite-ring recurrence algorithms do not
by themselves give order or sign control over the real prime sum.

## 1. A bounded-cost Vaughan specialization

Keep \(h=\log2\), \(c=\sqrt2\), the unchanged signed kernel \(W\), and
\[
K_X(y)=y^{-1/2}W(\log(y/X)),\qquad y>0,
\]
extended by zero outside \([X,8X]\). Then
\(G(X)=\sum_n\Lambda(n)K_X(n)\).

The **existing compiled input** is `ZetaVaughanReduction.vaughan` in
[ZetaVaughanReduction.lean](../RiemannGaussian/ZetaVaughanReduction.lean).
It retains all four terms of
\[
\Lambda=\Lambda_{\le V}+\mu_{\le U}*\log
 -\mu_{\le U}*\Lambda_{\le V}*1
 +\mu_{>U}*\Lambda_{>V}*1.
\]
Here \(*\) denotes Dirichlet convolution. The mean-density cancellation for
\(W\) is now compiled in `suzukiLocalSignedKernel_transform_half`. The
following sharp variation and sampling calculation has been independently
checked on paper by two agents. A coarser actual lattice estimate
`53/sqrt X` and the resulting small-factor cross bound
`318 U V/sqrt X` are now compiled in
[SuzukiLocalCancellationSampling.lean](../RiemannGaussian/SuzukiLocalCancellationSampling.lean).
The sharper constants in the following derivation are **not formalized**.

The physical kernel increases on \([X,2X]\), decreases on \([2X,4X]\),
and increases on \([4X,8X]\), with values
\[
0,\quad h/\sqrt X,\quad-h/(2\sqrt X),\quad0.
\]
Consequently
\[
\int_0^\infty K_X(y)\,dy=0,
\qquad \operatorname{TV}(K_X)=3h/\sqrt X.
\]
Centered Euler summation, with both exterior endpoint values zero, gives
the uniform bound
\[
\left|\sum_{m\ge1}K_X(qm)\right|
 \le\frac{3h}{2\sqrt X}\qquad(q>0).
\tag{L}
\]
In particular, there is no factor \(q\) in this error. Applying an absolute
value before the mean cancellation would lose this estimate.

For \(1\le d\le X\), the log-weighted sampling identity is
\[
\sum_m\log m\,K_X(dm)=\frac{J\sqrt X}{d}+e_d,
\qquad
|e_d|\le\frac{3h}{2\sqrt X}\bigl(\log(8X/d)+h\bigr),
\]
where
\[
J=-4hc(c-1)^2<0.
\]
The constant is the first logarithmic moment of the kernel, namely the
derivative of its transform at \(1/2\). Density cancellation removes the
\(\log(X/d)\) main term; it does **not** remove \(J\).

For real \(X\ge2\) and integers \(1\le U,V\le X\), put
\[
M(U)=\sum_{d\le U}\frac{\mu(d)}d,
\qquad
B_{U,V}(X)=\sum_{\substack{d>U,\ell>V,\ m\ge1}}
 \mu(d)\Lambda(\ell)K_X(d\ell m).
\]
Only \(X<d\ell m<8X\) contributes. All shared prime factors and proper
prime powers remain; neither coprimality nor comparable factor size is
assumed. The direct \(\Lambda_{\le V}\) term vanishes, including at the
left endpoint. Using (L), the log-weighted identity, and the existing
Chebyshev bound \(\psi(V)\le6V\) yields the paper estimate
\[
\boxed{
\left|G(X)-J\sqrt X\,M(U)-B_{U,V}(X)\right|
\le\frac{3hU}{2\sqrt X}\bigl(\log(8X)+h+6V\bigr).
}
\tag{V}
\]
For \(U=V=\lfloor X^{1/4}\rfloor\), its right side is at most
\(15h+6h^2\), uniformly for \(X\ge2\). To verify this constant, set
\(y=X^{1/4}\): use \(U,V\le y\), \(\log X=4\log y\),
\(\log8=3h\), \(1/y\le1\), and \(\log y\le y\).

This provides a precise next **unproved arithmetic estimate**:
\[
B_{U,U}(X)+J\sqrt X\,M(U)\ge-C_\varepsilon X^\varepsilon,
\qquad U=\lfloor X^{1/4}\rfloor.
\tag{J}
\]
The harmonic head must stay joined to the bilinear term. No bound for
either separately is claimed. The already compiled constant proper-power
cost transfers this target to \(G_{\rm pr}\).

This is a specialization of classical Vaughan/Euler summation, not a novel
decomposition. The local benefit is that the complete small-factor error
has bounded cost. It gives **no improved bound on the complete \(G\)**
until (J) is proved. The repository's older
[Vaughan cutoff budget](zeta-vaughan-cutoff-budget.md) concerns a different
factorial-moment kernel and does not automatically supply (J).

## 2. The distinct-prime covariance suggested by the factoring notes

The factoring investigation's equations N10–N11 already distinguish paid
same-prime energy from unpaid distinct-prime covariance; see the energy
section of
[semiprime-factorisation-investigation.md](semiprime-factorisation-investigation.md).
The following is a faithful analogue for the present prime source, rather
than an application of its unproved D11 estimate.

For \(T\ge\log2\), set \(F(t)=G_{\rm pr}(e^t)\),
\(a_p=\log p/\sqrt p\), and
\[
\mathcal K_T(p,q)=\int_T^{T+1}
 W(\log p-t)W(\log q-t)\,dt.
\]
All contributing primes belong to \([e^T,8e^{T+1}]\). The exact finite
Gram expansion is
\[
\int_T^{T+1}|F(t)|^2dt
=D_T+2C_T,
\quad D_T=\sum_p a_p^2\mathcal K_T(p,p),
\quad C_T=\sum_{p<q}a_pa_q\mathcal K_T(p,q).
\]
Elementary Chebyshev bounds give \(D_T=O(T+1)\). More generally, taking
absolute values only on the close pairs gives
\[
\sum_{\substack{p\ne q\\|p-q|\le H}}
 a_pa_q|\mathcal K_T(p,q)|\ll(H+1)(T+1),\qquad H\ge0.
\]
Indeed \(q\ge e^T\), each integer interval has at most \(2\lfloor H\rfloor+1\)
eligible partners, and \(\vartheta(8e^{T+1})\ll e^T\). These calculations
are **paper-level, not new Lean results**. They show that a subpower-width
near-diagonal strip is affordable. For example, take \(H=(T+1)^2\).
The unproved target is the **upper** bound below on the full signed
covariance; the close-pair estimate makes it equivalent to the same
all-exponent upper bound on its separated-prime part:
\[
C_T\le C_\varepsilon e^{\varepsilon T}
\quad\text{for every }\varepsilon>0.
\tag{C}
\]

Only the second moment is needed for an alternative analytic RH route.
Given (C), Cauchy–Schwarz supplies absolute exponential-damped integrability
of \(F\) for every positive damping. The bounded proper-power difference
does the same for the full \(G(e^t)\). Its Laplace transform is therefore
holomorphic on \(\Re z>0\). The finite-shift identity gives
\[
\mathcal L G(z)=p_h(z)\mathcal L S(z)-H(z),
\quad p_h(z)=(e^{hz}-c)(e^{hz}-1)^2,
\]
where the entire finite-head term is exactly
\[
H(z)=\sum_{j=1}^3a_j e^{jhz}
 \int_0^{jh}S(u)e^{-zu}\,du,
\quad(a_1,a_2,a_3)=(1+2c,-(2+c),1).
\]
Nonvanishing of \(p_h\) on \(0<\Re z<1/2\) retains every hypothetical
right-half-zero pole and its multiplicity. The existing cleared-xi/residue
argument can then exclude those poles. This covariance-to-RH analytic
bridge still needs formalization; (C) itself is unproved. A second moment
alone does not give the pointwise all-exponent bound by a simple spike
estimate, so those two arguments must not be confused.

## What the newest factoring constructions actually contribute

The 23 October sections **Fast fixed-matrix core and joint correction
identities** and **Executed causal feedback inverse and explicit terminal
projection** genuinely solve part of their own algebraic problem. The latest
state is stronger than the earlier summaries: the causal block inverse and
short rational numerator are acquired. Only the long terminal projection
remains unacquired at the desired cost. It would be stale to describe the
feedback inverse or startup as still missing.

Their useful principle here is to retain the entire forced correction
before applying a transform or norm. They supply no theorem controlling
the sign of (J) or (C). In particular, conjugation to a Toeplitz operator
does not preserve a quadratic-form order without the appropriate adjoint
and metric, and a finite-ring invertibility statement is not an inequality
over the real prime measure.

There is a legitimate positive operator identity: if \(E\) is unitary
log-translation, \(D=E-I\), and \(P=(E-c)D^2\), then
\[
\Re\langle E^*Pf,f\rangle
=(c-1)\|Df\|^2+\tfrac12\|D^2f\|^2\ge0.
\]
But the actual quantity is the linear evaluation \(PS(t)\), not this
quadratic form. A prime-source Gram or covariance estimate would be the
additional bridge; operator positivity alone does not bound it. This is
also a paper diagnostic, not a new compiled theorem.

The Charlier recurrence can organize repeated-index terms of higher prime
moments, but Poisson orthogonality does not hold for actual primes without
an arithmetic theorem. The second-moment route above already isolates the
first missing correlation, so higher-moment reorganization is not the
first recommended operation.

The existing carry/Gram collapse and eta-current dominant-energy audits
also retain unpaid signed arithmetic, rather than furnishing it. The recent
genuine cubic-square-sector bound applies to its original metaplectic
carrier; its odd-core term and the identification with the present kernel
remain separate obligations. See
[suzuki-carry-collapse.md](suzuki-carry-collapse.md),
[eta-current-dominant-energy-asymptotic.md](eta-current-dominant-energy-asymptotic.md),
and [arithmetic-operator-source-normalized-marked-gates.md](arithmetic-operator-source-normalized-marked-gates.md).

The small-factor sampling bounds now have checked Lean implementations.
The complete finite rearrangement (V) still needs a formal adapter. The
next substantive estimate is the **joined coprime-prime residual** in the
[follow-up](suzuki-local-cancellation-vaughan.md), using exact quotient cells
and retaining product-cutoff complements. In parallel, test whether
a source-preserving prime-pair identity can bound (C). These are specific
open arithmetic operations; the repository search has not resolved either.

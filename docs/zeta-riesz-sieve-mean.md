# One all-count quadratic budget for the literal Riesz response

The new checked estimate keeps the Mobius divisor cross terms until after
their common-factor rows are summed. Its constant does not grow with the
number of prime factors. This is an independent arithmetic estimate, but
neither the whole `-79/1000` floor nor the `3/2` ceiling is proved.

## Checked inequalities

For integer `R` and real `R <= x < R+1`, put

\[
\lambda_x(d)=\mu(d)\log(x/d),\qquad 1\le d\le R.
\]

`ZetaRieszSieveQuadratic.logarithmic_quadratic_bound` proves

\[
\sum_{d,e\le R}\frac{\lambda_x(d)\lambda_x(e)}{[d,e]}
\le196(1+\log R).
\]

The proof uses the exact Selberg diagonalization

\[
\sum_{d,e\le R}\frac{\lambda_x(d)\lambda_x(e)}{[d,e]}
=\sum_{g\le R}\varphi(g)
 \left(\sum_{\substack{d\le R\\g\mid d}}\frac{\lambda_x(d)}d\right)^2.
\]

The signed logarithmic Mobius bound, with all excluded primes retained,
gives a row bound `7/phi(g)`. The complete reciprocal-totient sum is at
most `4*(1+log R)`. No count truncation or prime-density approximation
is used. These are elementary sieve arguments; no historical novelty
is claimed.

`ZetaRieszSieveMean.riesz_mean_square_le` then proves, for every `x>0`,

\[
\boxed{\sum_{n\le X}\mathcal R_{\log x}(n)^2
\le196X(1+\log R)+16x^2.}
\]

This is the repository's original `VaughanLogAverage.riesz`. The proof
retains the exact floor `floor(X/[d,e])`, and bounds its error only after
the signed quadratic form has been evaluated. The error uses the checked
coefficient mass `sum |lambda_x(d)| <=4x`. If `x^2<=X`, the bound improves
to `(212+196*log R)*X`. That premise is explicit.

## Application to the actual residual

For an arbitrary finite selection `S` of original squarefree composite
labels in `[1,X]`, write its exact real residual as

\[
J=\sum_{n\in S}w(n)\mathcal R_{\log x}(n),
\]

\[
w(n)=(1-\theta_A(n))\frac{-\log n}{\log x}
       \operatorname{Re}K_N(3/2+iy,n).
\]

`re_residual_eq_weight` proves this identity for the existing coefficient.
`literal_residual_bounds` gives both signed sides with the same allowance:

\[
-B\le J\le B,\qquad
B^2=\left(\sum_{n\in S}w(n)^2\right)
     \left(196X(1+\log R)+16x^2\right).
\]

The selected labels, allocation, factorial order, full phase, physical
support and all prime counts remain literal. Arbitrary clipped or radial
selections can be included in `S`; this does not justify counting repeated
incidences twice. The theorem does not replace the retained signed prime
sum by independent divisor signs. Cauchy--Schwarz is applied only after
the complete signed divisor square has an independent bound.

## What is still unpaid

The actual weight energy and cutoff-square term are displayed, not assumed
small. At the campaign's original large cutoff, `16x^2` may exceed the
population scale. Reflection changes the cutoff with the integer label;
a fixed-cutoff mean-square theorem cannot be transferred to that moving
cutoff silently. Nor may already credited phase-selected sectors be
added again after completing their prime periods. This slice does not
provide source-normalized decay, a new zero-free region or a contradiction.

The subsequent [sharp-cutoff slice](zeta-riesz-cutoff-mean.md) now proves a
cutoff-independent sharp quadratic constant and the literal interval bound
`sum_(Y<n<=X) M_R(n)^2 <= E*(X-Y)+R^2`. It transfers this to both signed
sides of cutoff differences. Coupling that bound to moving prime-period
weights, and paying its finite error at source scale, remain open.

## Numerical probe and literature audit

Run the optional `scripts/probe_riesz_sieve_mean.py` with the project
Python environment. It uses actual integer Mobius and totient arrays,
floating logarithms, the exact common-factor quadratic sum and direct
finite integer second moments. It runs no certificate verification and
is not part of ordinary CI. Recorded output and source hashes are in
`riesz-sieve-mean-audit.json`.

For cutoffs from 32 through 32000 the logarithmic quadratic form divided
by `log R` rises from about 0.838 to 0.941. The corresponding **sharp**
quadratic form is about 0.44074 at 32000. At half-width `pi/54`, the
two-cutoff difference energy divided by the half-width squared is about
0.43489 there. These finite observations are not asymptotic proofs or
certificates for the masked carrier.

The probe also sums the actual sharp-cutoff and two-cutoff responses over
integers, retaining the counting floors. At `R=32000`, `X=1000000`, their
second moments divided by `X` and by `X*(pi/54)^2` are approximately
0.442922 and 0.437459. Here `R^2>X`, so this check goes beyond the regime
where the elementary floor-error allowance is useful. It still does not
test the campaign's moving ownership and phase masks.

The classical truncated-divisor correlation framework is discussed by
[Goldston and Yildirim](https://arxiv.org/pdf/math/0111212).
For the sharp cutoff `M(n,z)=sum_(d|n,d<=z) mu(d)`,
[de la Breteche, Dress and Tenenbaum, 2020](https://tenenb.perso.math.cnrs.fr/PPP/Sxz.pdf)
prove a bound `sum_(n<=X) M(n,z)^2=O(X)` uniform in both parameters,
and an interior asymptotic. This addresses the large-cutoff weakness of
the elementary floor estimate. A
[2026 preprint by Ramare and Zuniga-Alterman](https://arxiv.org/html/2603.25961v2)
gives explicit bounds for the associated Mobius lcm quadratic form and
its perturbed exponents. The uniform `O(X)` mean and those explicit
constants have **not** been formalized or assumed in the new Lean proofs.
The subsequent slice proves an unevaluated constant for the sharp quadratic
using existing repo inputs. The stronger literature results' applicability to
moving cutoffs and the actual remaining signed selections still needs
a proof.

The immediate intended use of the uniform sharp-cutoff theorem is the
inequality

\[
\sum_{n\le X}\left(\mathcal R_{D+h}(n)-\mathcal R_D(n)\right)^2
\le C Xh^2\qquad(h\ge0),
\]

obtained by integrating the sharp cutoff and applying Cauchy--Schwarz.
The subsequent slice removes the growing logarithm from this **cutoff
variation** budget while retaining a finite error `h^2*R^2`. The displayed
`C X h^2` bound without that error is still open in the general cutoff
range. Transferring it to prime periods must keep the actual ownership endpoints,
allocation variation, rough-prime support and signed paid-sector overlaps.

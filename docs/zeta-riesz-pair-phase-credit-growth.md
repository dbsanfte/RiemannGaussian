# Cofinal actual-prime credit in the retained signed sum

The independent cofinal target remains

\[
\operatorname{Re}\mathrm{prefixPairDefect}_{N_j}
\le\frac{399}{5000}+o(1).
\]

[`ZetaRieszPairPhaseCreditGrowth`](../RiemannGaussian/ZetaRieszPairPhaseCreditGrowth.lean)
now gives a cofinal quantitative estimate for an actual signed contribution
to that same sum. For fixed \(54\le |y|\) and
\(1/2<u\le10001/20000\), there is \(c_{u,y}>0\) such that, eventually,

\[
\operatorname{Re}\left[u^{N+1}\sum_{n\in F_N}
 (\mathrm{prefixCoefficient}_N(n)-\mathrm{selbergCoefficient}(n))
 K_N(3/2+iy,n)\right]
\le-c_{u,y}\frac{(2u)^N}{(N+1)^3}.
\]

Here \(F_N\) is exactly the existing `favorableLabels`, with its original
semiprime, complete-period, radial and endpoint masks. There is no
exposed-zero hypothesis in this estimate. The height and radius are fixed;
neither its entry order nor a height-uniform constant is certified.

This is a signed estimate on a literal population, not a bound for the full
main sum. The global floor, multiple-zero ceiling and zero exclusion remain
open.

## Funding actual labels, rather than coefficients alone

For \(z=|y|>0\), the proof chooses fixed widths and a bounded translation:

\[
h=\frac1{8(z+1)},\qquad C=\frac{\pi}{z}.
\]

At every order there is \(N\le a_N\le N+C\) such that

\[
2a_N+h\le T\le2a_N+3h
\quad\Longrightarrow\quad\cos(yT)\le-\tfrac12.
\]

Select actual primes in the two adjacent logarithmic boxes

\[
a_N<\log p\le a_N+h,
\qquad a_N+h<\log q\le a_N+2h.
\]

Their products are squarefree, have exactly two prime factors, and satisfy
\(p<q\). The product map is injective: the largest prime identifies \(q\),
then \(p\). For every sufficiently large order, both log shares are at least
\(12/25\), and the product lies strictly inside the original central core:

\[
\tfrac{1971}{1000}N+1<\log(pq)
\le\tfrac{2029}{1000}N-1.
\]

The existing interior-period theorem therefore retains its complete-period
mask. `pairProducts_subset_favorable` proves membership in the literal
favorable set, without completing a mask or spending an earlier boundary
payment.

The already-proved prime-count theorem for fixed logarithmic width, uniform
over bounded translates, supplies \(c>0\) and eventually

\[
\#\{pq\}\ge\frac{c^2e^{2N}}{(N+1)^2}.
\]

This use of PNT only counts a fixed-width funding population. It is not
transport of the signed main to a continuous density, a short-interval
phase approximation, or a fixed-power error estimate.

## Full factorial and phase weights

Put \(D=2C+3h\). Every funded label satisfies \(2N\le\log n\le2N+D\), hence

\[
\lVert K_N(3/2+iy,n)\rVert
\ge e^{-(3/2)(2N+D)}\frac{(2N)^N}{N!}.
\]

Its actual squared cosine is at least \(1/4\). Keeping the full factorial
weight and summing only this literal subset proves

\[
\mathrm{signCredit}_N
\ge\frac{u\,c^2e^{-3D/2}}{4800}
       \frac{(2u)^N}{(N+1)^3}.
\]

The coefficient and factorial inequalities are exact Lean theorems. The
constant comes from the actual prime-count lower bound; no numerical
population or continuum probe is used in the proof.

`signCredit_le_exact` transfers the benchmark to the ENTIRE favorable
contribution. The new results prove that both `signCredit` and
`exactSignCredit` tend to positive infinity, including on the native
dyadic moment sequence. In particular, this population is eventually
nonempty. This closes the population-size limitation of the preceding
[`JoinedPairSignCover`](zeta-riesz-joined-pair-sign-cover.md) slice.

## The joint estimate still required

The exact existing ledger remains

\[
\operatorname{Re}\mathrm{prefixPairDefect}_N
=\operatorname{Re}\mathrm{signedRest}_N
 -\mathrm{exactSignCredit}_N.
\]

The new lower bound is not permission to discard the excess exact credit,
replace it by a fixed charge, or assign a separate positive allowance to
the rest. Since \(2u>1\), the signed favorable contribution has unbounded
magnitude. A finite upper bound for the whole sum requires controlling its
correlation with the rest. The new theorem supplies no numerical improvement
to `399/5000`, and no fraction of the remaining global gap is measured.

The next estimate must compare **the signed rest minus the full exact
credit together** with `399/5000 + o(1)`. The original native floor ledger,
all four joined coefficient slots, moving length, order cutoffs, prior
payments and every no-go remain unchanged. No new carrier is introduced.

## Focused validation

The strict leaf build and
[`CheckRieszPairPhaseCreditGrowth`](../scripts/CheckRieszPairPhaseCreditGrowth.lean)
are optional local checks. The checker lints the namespace and collects
axioms for every declaration, including private/generated helpers; only
standard Lean axioms are accepted. The scoped audit is
[`riesz-pair-phase-credit-growth-audit.json`](riesz-pair-phase-credit-growth-audit.json).

All 230 preceding Riesz source/artifact pins were verified before updating
the guide. Earlier proof and numerical snapshots are preserved. This slice
has no root registration, wider gates, CI run, commit or push.

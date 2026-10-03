# Residual global semiprime/head price: exact no-go

`ZetaRieszGlobalHeadPriceAudit` tests the **exact positive right side** of
the previously proved global semiprime/head cancellation. It does not
test, bound, or assert divergence of the actual signed sum. The whole floor
and the independent signed boundary estimate remain open.

The radius is fixed with

\[
\frac12<u\le\frac{10001}{20000}.
\]

Write `D2_N = semiprimePrice u N`, `H0_N = nativeHead u 0 N`, and
`E_N = radialConstant * exp(-N/1000000)`. The previous theorem proves

\[
\|P_{2,N}+\text{same full head}_N\|
\le D_{2,N}-H_{0,N}+2E_N.
\]

The new theorem proves that this positive allowance tends to infinity,
including on the exact native dyadic sequence. No cofinal subsequence
can keep it below **any** fixed real ceiling. This does not revoke the
true same-label credit or either of its funded radial transfers.

## Literal untouched population

Take ordinary primes in two disjoint adjacent intervals:

\[
N<\log p\le N+1,\qquad N+1<\log q\le N+2.
\]

The products have one incidence, are squarefree semiprimes, and satisfy

\[
2N+1<\log(pq)\le2N+3,\qquad\log\operatorname{largestPrime}(pq)\le N+2.
\]

For `N >= 65536` they belong to the actual central semiprime boundary
`1.971N < log n <= 2.029N` and fail the original head owner threshold
`log largestPrime n >= 1.02N`. They receive no head credit. The coefficient
uses the actual floor-defined moving length, not `L = -2N log u`. The
two prime logs lie below `L`, their total lies above it, and their restored
completion coefficient has norm at least one.

The fixed-width PNT is used **only for a lower bound on their number**:
eventually there are at least

\[
\frac{e^{2N}}{36(N+1)^2}
\]

distinct such products. This uses an existing proved PNT theorem, not an
assumed prime-cancellation estimate. Its starting order is unevaluated.
Every selected atom retains its full factorial/source weight.

Combining the count with the factorial lower bound gives the explicit
eventual envelope

\[
\boxed{
\frac{u e^{-9/2}}{216}\,
\frac{(2u)^N}{(N+1)^3}
\le D_{2,N}-H_{0,N}+2E_N.
}
\]

Every matching head label spends only its own opposite semiprime
coefficient. The funded zero-height radial transfer shows that taking
the full head credit cannot remove the untouched population. Since
`2u > 1`, the envelope diverges. This is uniform in the actual ordinate
in the sense that the diagnosed price is height-independent; no actual
complex phase is removed from the signed carrier.

## Numerical diagnostic and scope

The optional `scripts/probe_riesz_global_head_price_audit.py` has two
separate parts. Its scalar log-domain calculation evaluates the **eventual
expression**, not certified finite-order lower bounds. At the radius
ceiling the expression crosses `399/5000` near `N = 472391.52`; this is
**not a native certified starting order**, because the PNT threshold
has not been evaluated.

The exhaustive small-order part retains the frozen toy data for `N=6,7,8`,
heights `54,65,100`, all central ordinary primes/semiprimes, raw high
owners at every count, and the same full original head. It joins all
coefficients before grouping by actual phase periods, retains partial
periods and exterior endpoints, and passes 45 frozen complex regressions.
Its length, schedule and deletion masks differ from native data; no
eventual theorem is applied at those orders.

The toy whole signed sums are much smaller than atom prices. Complete
interior periods are also smaller than partial/end periods in these
cases. These observations motivate a signed whole-period estimate,
but they supply neither an asymptotic saving nor a fraction of the floor
gap. No divergence of the signed sum is inferred from the allowance.

## Actual remaining target

Keep `P1 + P2 + rawHighOwners + same full head` assembled and prove its
**independent signed real** upper bound `<= 399/5000 + o(1)` on a cofinal
native sequence, or an equivalent paid complete-period target. Do not
optimize or reuse the divergent semiprime-minus-head atom allowance.
No floor, multiplicity ceiling, restricted exclusion, or RH claim follows
from this no-go audit.

Strict leaf validation, targeted build, frozen-root namespace lint and
all-declaration transitive axiom checks are recorded in
`docs/riesz-global-head-price-audit.json`. The probe is outside ordinary
builds and CI. Everything remains local and uncommitted.

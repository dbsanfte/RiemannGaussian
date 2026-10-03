# Selberg completion does not pay the joined remainder by absolute value

Local Lean audit, 2026-10-03. The signed complete-period floor is still open.

The numerical prime/semiprime opposition suggests testing the classical
second logarithmic convolution. The repository already proves its exact
identity in `SuzukiLogarithmicConvolution`:

\[
\Lambda(n)\log n+(\Lambda*\Lambda)(n)
=\sum_{db=n}\mu(d)(\log b)^2.
\]

The new leaf `ZetaRieszLowCountSelbergAudit` tests the normalized coefficient

\[
b_{\mathrm{Sel}}(n)
=-\frac{\Lambda(n)\log n+(\Lambda*\Lambda)(n)}{\log n}
\]

against the **existing literal** `joinedCoefficient`. It does not replace
the carrier, claim a masked Selberg estimate, or add a payment to its ledger.

`selbergDefect_prime_eq_zero` proves exact agreement on every original
central ordinary-prime label. For distinct primes it proves

\[
b_{\mathrm{Sel}}(pq)=-\frac{2\log p\log q}{\log(pq)}.
\]

## The difference occupies the interior bulk

Take the two ordered fixed-width prime boxes

\[
N<\log p\le N+1,\qquad N+1<\log q\le N+2.
\]

At every order `N >= 65536`, these are squarefree two-prime labels in the
actual central window. Their largest prime has logarithm at most `N+2`,
which is below the literal `1.02N` owner threshold. Consequently both the
original allocated/sieved head and the **new full unallocated correction**
are absent. This uses their actual masks, not a continuum share limit.

Write `T=log(pq)` and let `L` be the actual floor-dependent Riesz length.
The exact joined coefficient is then

\[
b_N(pq)=-\frac{T(T-L)}L.
\]

Its difference from Selberg is

\[
\Delta_N(pq)
=T-\frac{T^2}L+\frac{2\log p\log q}T.
\]

`balanced_defect_lower` proves the explicit bound

\[
\boxed{\Delta_N(pq)\ge N/20}
\]

uniformly for `1/2 <= u <= 10001/20000`, with the original moving length.
`balancedProducts_subset_periods` proves that every such label belongs to
a complete retained phase period at every fixed `|y| >= 54`. Thus the
difference cannot be assigned to an exterior radial or partial-period
error that has already been paid.

## A rigorous no-go for absolute completion errors

For this audit only, define the diagnostic price over the **same complete
period support**:

\[
\mathfrak D_N
=\sum_n\left|
 u^{N+1}\Delta_N(n)K_N(3/2+iy,n)
\right|.
\]

The existing proved prime-box counting lower bound and exact factorial
normalization give

\[
\mathfrak D_N\ge
 \frac{u e^{-9/2}}{216}\frac{(2u)^N}{(N+1)^3}
\]

eventually. For every `u > 1/2`, `selbergDefectPrice_tendsto_atTop` proves
that this price tends to infinity. The native-dyadic corollary excludes
**any cofinal fixed bound** for this absolute remainder price, including
`399/5000`. No evaluated eventual counting threshold is claimed.

This is a new negative test of **Selberg completion followed by an absolute
defect payment**. It does not prove that the signed defect diverges, or
that the classical identity cannot help a genuinely joined signed estimate.
Neither the signed floor nor the multiplicity ceiling is improved here.

The original target remains

\[
\mathrm{lowCountPeriods}(u,y,j)\le399/5000+o(1)
\quad\text{cofinally}.
\]

Any further Selberg approach must retain the bulk prime-pair difference
inside the signed convolution/phase estimate. Numerical anticorrelation
cannot license its removal by a positive allowance.

## Optional quantitative check and validation

`scripts/probe_riesz_low_count_selberg_audit.py` checks 40 rational corners
of the prime-log boxes and the proved moving-length bracket, at orders
65536 through 1000000. It does not enumerate astronomical prime sets.
The smallest checked `Delta/N` is about `0.11185`; the formal uniform bound
is the weaker `1/20`. The script also reports the unsigned geometric growth
exponent `log(10001/10000)`, about `9.9995e-5` per order. These diagnostics
are outside CI and are not signed arithmetic certificates.

Validation is limited to strict leaf compilation, its targeted build,
the frozen ordinary compiled root plus an explicit leaf import with all
14 namespace linters, and a transitive standard-axiom audit of all 38 new
declarations, including 35 theorems and private/generated helpers. This
slice does not edit root registration, public frontier metadata or README,
and runs no wider gates or commits. Concurrent semiprime changes are preserved.
See `docs/riesz-low-count-selberg-audit.json` for immutable evidence pins.

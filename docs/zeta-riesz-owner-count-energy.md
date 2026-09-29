# One cofactor budget for every prime count

Lean now pays the cofactor part of the reciprocal-log weight energy in
both signed owner-slope estimates. The bound includes every prime count,
keeps the original owner and moving interval endpoints, and allows
complex coefficient and cofactor phases. The period coefficients still
have to be fixed across the cofactor population. Their remaining
energy, irregular signed prime-moment dependence and the matching signed
cutoff correction are not bounded at source scale.

Let `omega(n)=card(n.primeFactors)` and let `H_X` be the literal finite
prime sum `sum(p<=X, prime p) 1/p`. Counting ordered prime-divisor
incidences gives

\[
\sum_{1\le n\le X}\omega(n)^2\le X(H_X^2+H_X).
\]

Distinct prime pairs contribute at most `X/(pq)`; diagonal pairs
contribute at most `X/p`. No density approximation or maximum number of
prime factors is used.

For a squarefree cofactor whose prime factors are all below the marked
owner prime, the exact sum of prime logarithms gives

\[
0<\frac{\log n}{\omega(n)}\le\log p.
\]

Consequently, on any selected shell `M<n<=2M`, with `M>=2` and
`|w(n)|<=W/n`, the complete reciprocal-log energy satisfies

\[
\boxed{\displaystyle
\sum_{n\in S}
 \left|\frac{w(n)}{\log n/\omega(n)}\right|^2
\le \frac{2W^2(H_{2M}^2+H_{2M})}{M(\log M)^2}.}
\]

This is an upper bound for all counts together. It does not charge a
separate exponential constant to each count, and it does not replace
every cofactor's owner logarithm by the worst one in the population.

## The signed estimate with the cofactor energy paid

Combine this with the earlier uniform separated-cutoff mean and exact
owner maximal bound. For `2^b` logarithmically separated cutoffs, the
real or complex signed sum has both bounds `-K<=Re J<=K`, with

\[
\boxed{\displaystyle
K^2=\frac{144(b+1)^2E_hW^2}{(\log M)^2}
 (B_M^2+B_M)\sum_{i<2^b}|a_i|^2,}
\]

where one proved, unevaluated constant `E_h>0` depends only on the fixed
logarithmic separation, and

\[
B_M=2e^{1/2}\log4\,
 \bigl(1+\log(4\log(2M)+8)\bigr).
\]

The existing Chebyshev prime counts prove `H_(2M)<=B_M`. Thus no
unevaluated cofactor sum remains in this budget. The complex theorem
absorbs one fixed factor two into `E_h`; it keeps the phases in the
whole sum before taking the real part.

The literal summand retains the owner weight at `log(n)/T(n,i)`, the
strict `cutoffSlope(D_i,n)`, and the reciprocal factor
`1/(T(n,i)-log(n))`. Ownership supplies the lower bound for this last
denominator. Positive increasing `T(n,i)` and both cofactor-dependent
interval endpoints remain in the statement. Squarefreeness and the
population mask are retained.

This estimate removes the exponential population size from the
cofactor cost. It is not a bound for the whole carrier: `a_i` must still
be fixed across labels, and the original prime moments have additional
irregular cofactor dependence. Noncontiguous holes in the period
selection are not covered. The remaining coefficient energy, radial
aggregation and signed cutoff correction must be controlled together
without counting previously paid sectors twice. Both the whole
`-79/1000` floor and `3/2` ceiling remain open. No RH or zero-free claim
follows from this slice.

## Optional finite diagnostic

`scripts/probe_riesz_owner_energy.py` uses actual integers through
`32768`, `262144` and `1048576`. At the last endpoint the squarefree
shell energy, multiplied by `X*log(X/2)^2`, is approximately `4.71685`,
while the proved bound evaluates to approximately `44.9894`. Retaining
the actual largest prime gives a smaller sampled energy. The floating
diagnostic does not certify a source-scale estimate and remains outside CI.

[Lean proof](../RiemannGaussian/ZetaRieszOwnerCountEnergy.lean).
[Audit](riesz-owner-count-energy-audit.json).

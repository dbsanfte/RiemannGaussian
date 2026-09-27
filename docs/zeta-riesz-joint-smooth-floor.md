# Exact small-composite cancellation in the joint core

[`ZetaRieszJointSmoothFloor`](../RiemannGaussian/ZetaRieszJointSmoothFloor.lean)
removes a class of actual integer labels at **zero cost**. It combines
the stronger count bound with the already paid large-prime deletion; no
new carrier, phase approximation or cofactor completion is introduced.

Write a selected squarefree label as `n = p*q*a`, with `p,q` prime and
`a` a composite factor whose prime divisors are all at most `N_j^2`.
In the remaining smaller-count core,

\[
\log a\le N_j/2048,\quad
1.95N_j<\log n\le2.03N_j,\quad
\log p,\log q<0.601\log n.
\]

The last restriction holds on every nonzero residual coefficient after
the proved dominant-prime deletion. Eventually the actual length satisfies
`5N_j/4 <= L_j <= 7N_j/5`. These inequalities imply

\[
\log(pa),\log(qa)\le L_j\le\log(pq).
\]

## Cancellation before estimation

The exact prime-insertion identity is

\[
\mathcal R_L(pqa)=\mathcal R_L(a)
-\mathcal R_{L-\log p}(a)
-\mathcal R_{L-\log q}(a)
+\mathcal R_{L-\log p-\log q}(a).
\]

For composite squarefree `a`, its complete Möbius mass and logarithmic
moment are both zero. The first three cutoffs contain every divisor of
`a`, so these three terms vanish. The final cutoff is nonpositive and
its term also vanishes. Therefore the original `coefficient L n` and
`residualCoefficient` are **exactly zero**, before observing any complex
phase or allocation weight.

`sum_without_two_primes_composite` proves the corresponding finite-sum
deletion for arbitrary complex weights on any selection of this retained
support. All endpoints and inherited masks are retained.

## Direct consequence for the whole signed target

`eventually_re_core_ge_without_large_and_composites` gives a one-sided
comparison for the original whole core. It first pays the count reduction
and the large-prime deletion, then removes the zero class just proved.
The remaining finite sum stays inside one real observation. Its total
allowance is exactly

\[
32U\log 2\;N_j(49999/50000)^{N_j}
+2M_{1+1/262144}e^{-N_j/1000000}\longrightarrow0,
\qquad U=10001/20000.
\]

The limit is checked by `tendsto_reduction_allowance`. The result has no
zero hypothesis and is uniform in the real phase height. Its eventual
starting index remains unevaluated. The independent outer-radial savings
remain available; exact cancellation is valid on further intersections
with their retained support as well.

This is **not** a signed floor for the surviving sum. The composite
condition on `a` is essential: prime `a` has a nonzero logarithmic moment.
Thus this theorem does not remove the troublesome triples, nor labels
with three or more remaining large prime factors. Their signed response
and the central allocation transition still need the joint
`-79/1000-o(1)` floor. No RH contradiction or new zero exclusion follows.

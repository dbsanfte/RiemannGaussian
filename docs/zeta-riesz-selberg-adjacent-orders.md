# Fixed-mask adjacent-order Selberg test

The requested complex identity is proved for the **actual** balanced
`selbergDefect`, with the original pair mask and phase held fixed. The
literal `prefixPairDefect` has two additional factorial prefixes; these
are retained exactly and covered by their existing geometric payment.
No independent floor or constant ceiling has been proved by this test.

The checked leaf is
[ZetaRieszSelbergAdjacentOrders.lean](../RiemannGaussian/ZetaRieszSelbergAdjacentOrders.lean).
It reuses the existing balanced box, without subdividing it:

```math
S_N=\{(p,q):p,q\text{ prime},\quad
N<\log p\le N+1<\log q\le N+2\}.
```

For the original radius interval and `N >= 65536`, this whole box lies
inside the original complete-period pair mask and the inner two-hinge
regime. Its canonical owner is `q`, its cofactor is `p`, count two is
automatic, and the two prime windows are disjoint, so no diagonal is
deleted. The original joined head/correction flags are evaluated exactly.

Put `x = log p`, `z = log q`, `T = x+z`, and use the **moving** literal
`L_N = SquarefreeVaughanLogSource.length u N`. The proof establishes

```math
\Delta_N(p,q)
=\frac32T-\frac{T^2}{L_N}-\frac{(x-z)^2}{2T},
```

and, for arbitrary complex evaluation centre `s`,

```math
\Delta_N K_N(s,pq)
=\frac32(N+1)K_{N+1}(s,pq)
-\frac{(N+1)(N+2)}{L_N}K_{N+2}(s,pq)
-\frac{(x-z)^2}{2N}K_{N-1}(s,pq).
```

There is no phase approximation: each term retains the same `p*q` and
`exp(-s*log(p*q))`. The statement is also summed over any **unchanged**
subset of `S_N`. Expanding the imbalance gives the exact prime-order
convolution

```math
(x-z)^2K_M(s,pq)
=\sum_{k=0}^M\left[
(k+1)(k+2)K_{k+2}(s,p)K_{M-k}(s,q)
+(M-k+1)(M-k+2)K_k(s,p)K_{M-k+2}(s,q)
-2(k+1)(M-k+1)K_{k+1}(s,p)K_{M-k+1}(s,q)
\right].
```

The masked pair moments therefore factor into the two **literal finite
one-prime windows** at shifted orders. All factorial endpoints, including
orders zero and one, remain. These are finite masked prime moments, not
complete-prime moments.

## The literal prefix correction

On this box, the actual prefix atom satisfies

```math
(\operatorname{prefixCoefficient}_N-\operatorname{selbergCoefficient})K_N
=\Delta_N K_N-Q_N(p,q),
```

where, with `c_N = floor(13*N/32)`, the signed factorial prefix is exactly

```math
Q_N(p,q)=\frac{N+1}{L_N}\left[
(L_N-x)\sum_{k=0}^{c_N}K_{N+1-k}(s,p)K_k(s,q)
+(L_N-z)\sum_{k=0}^{c_N}K_{N+1-k}(s,q)K_k(s,p)
\right].
```

`prefixPairDefect_adjacent_ledger` expresses the **whole original**
`prefixPairDefect` as this three-order combination, minus these prefixes,
plus its original signed sum over
`nativePairMask \ balancedProducts N`. That remaining sum is kept
literal; it is not declared small or bounded by a positive allowance.

Only the prefix error is paid:

```math
\left\|u^{N+1}\sum_{(p,q)\in S_N}Q_N(p,q)\right\|
\le 12e^2(N+1)e^{-N/1600}\longrightarrow0.
```

This uses the existing coefficient-error budget once. It supplies no new
credit for the three neighbouring masked moments or the signed rest.

## Mask-transfer gate

Holding `S_N` fixed produces **no commutator**. Replacing it by another
mask `D` produces the exact signed difference

```math
M_{S_N,k}-M_{D,k}
=\sum_{e\in S_N\setminus D}K_k(s,pq)
-\sum_{e\in D\setminus S_N}K_k(s,pq).
```

In particular, replacing the old native box by the one at `N+1` does not
produce a thin boundary: `S_N` and `S_(N+1)` are disjoint, as are their
product masks. The removed side is the **whole old box**, contained in
the original complete phase periods, rather than a paid radial exterior.

The proof quantifies the absolute cost of that removed side while retaining
the joined defect:

```math
\sum_{n\in\operatorname{balancedProducts}_N
               \setminus\operatorname{balancedProducts}_{N+1}}
\left\|u^{N+1}\Delta_N(n)K_N(s_0,n)\right\|
\ge c(u)\frac{(2u)^N}{(N+1)^3}\longrightarrow+\infty
\qquad(u>1/2).
```

The positive `c(u)` and actual prime-population bound are checked in
Lean. The divergence also rules out a constant cofinal absolute budget
on the original dyadic order schedule.

This closes **absolute payment of that mask replacement** negatively.
It does not refute a future signed estimate with `S_N` held fixed, or
every possible signed completion argument. In particular, the existing
exposed-zero limits for complete prime moments cannot be substituted
for these finite-window moments without a new, valid signed transfer.
No such transfer is assumed here.

## Scoped validation and interpretation

The optional algebra-first probe retains every signed order component,
the full phase, both factorial prefixes, and the moving length before
collection. It checks 216 actual-prime atom controls at orders 64, 128
and 256, and four separate scalar geometry rows at orders 65536 and
131072. An independent 420-bit consumer enumerates the divisor response
and computes prefixes through binomial marginals, checking 3248 ball
comparisons and their relative widths.

The actual-prime controls are below the native theorem's order threshold;
the large-order rows are scalar log geometry, **not prime labels**. These
are regression checks, not native-core enumeration, actual-zero samples,
or certification of a native entry order. The reported retained scalar
fractions are not a percentage of progress toward the floor or ceiling.

The scoped leaf builds, namespace linters and transitive standard-axiom
check are recorded in
[the local audit](riesz-selberg-adjacent-order-audit.json). All 321 prior
proof/probe pins are preserved. No root registration, public metadata,
wider gate, commit or push is part of this slice.

The earlier unregistered `ZetaRieszCeilingAdaptiveFejer` leaf is preserved
and checked, but further work on that track was postponed for this test.
It proves the degree-dependent actual multiplicity bound
`m <= (2u)^(32d) + (5/4)*(H+11)/d` for `d >= 1`; it does not yet prove
an optimized height bound or a new native ceiling transfer.

The independent simple floor and full fixed-strip/all-height ceiling
**42/25** remain open. The next mathematical target, if this identity
is used, is the **joint signed neighbouring-order expression on the
unchanged literal mask**, together with its retained signed rest.

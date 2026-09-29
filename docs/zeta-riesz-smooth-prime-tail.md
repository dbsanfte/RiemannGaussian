# Joined smooth prime tails and the original retained carrier

`ZetaRieszSmoothPrimeTail` pays the signed smooth response left explicit by
[the retained-discrepancy comparison](zeta-riesz-retained-discrepancy.md).
Both signs of the original retained carrier are now bounded on common
eligible, coprime prime intervals. The interval can contain arbitrarily
many phase periods and can be clipped at its exterior endpoints.

The [proof audit](riesz-smooth-prime-tail-audit.json) records compiled
endpoints, transitive axioms, source hashes and the optional diagnostics.

## The oscillatory estimate

For every integer order `j >= 0`, the actual prime-density amplitude is

```math
f_j(t)=e^{-t/2}t^{j-1},\qquad t>0.
```

Its derivative has the sign of `2(j-1)-t`. Orders zero and one are
decreasing; higher orders have a single maximum. Integration by parts
therefore gives, for `0<a<=b`, `y!=0`, every real phase shift `c`, and
`|exp(-t/2)t^j|<=W` on the interval,

```math
\left|\int_a^b e^{-t/2}t^{j-1}\cos(y(t+c))\,dt\right|
\le \frac{2W}{a|y|}.
```

The proof retains the oscillation inside the integral. Endpoint values
plus total variation cost at most twice the peak density; there is no
factor counting periods. The same estimate applies to every partial
tail entering the two Riesz cutoffs.

The theorem uses the already proved amplitude cap

```math
W_j=\min\{e^{-a/2}b^j,\ e^{-j}(2j)^j\},\qquad
q_j=\frac{2W_j}{a|y|}.
```

The `j=0` convention is the ordinary natural power `0^0=1`. No order is
deleted. After passing through the logarithmic divisor increments,
`factorial_smooth_profile_energy` bounds their squared energy by `b*q_j^2`.
Cosine/sine rotation retains the arbitrary cofactor phase before the
squarefree mean. The resulting mean has the bound `E*X*b*q_j^2` for every
squarefree selection in `(1,X]`, with one proved, unevaluated `E>0`.

## The literal carrier bound

Let `S subset (M,2M]` contain squarefree cofactors with at least two prime
factors. The common marked-prime interval is `exp(a)<p<=exp(b)`. Every
prime in it must be eligible and coprime to every selected cofactor.
The earlier arithmetic discrepancy estimate gives

```math
\varepsilon_j=
 \frac{5W_j[2+(|j/a-1/2|+j(b-a)/a^2+|y|+2)(b-a)]}{a^3}.
```

The new `joinedCost` is `q_j+epsilon_j`. Thus the original finite sum

```math
J=\Re\sum_{n\in S}\sum_{p\in P}
 \operatorname{residualCoefficient}(A,L,N,pn)K_N(3/2+iy,pn)
```

obeys `-sqrt(E)*K <= J <= sqrt(E)*K`, where

```math
K=\frac{e^{-\log M/2}\sqrt b}{LN!}
 \sum_{j=0}^{N+1}{N+1\choose j}
    (\log(2M))^{N+1-j}(q_j+\varepsilon_j).
```

This is `exists_literal_joined_bounds`. The exact nonnegative retained
coefficients are used in its proof before applying their binomial caps.
The original `1-boundedShare`, full product phase, all factorial orders,
both Riesz hinges and every selected cofactor remain. There is no upper
prime-count ceiling or unproved density hypothesis.

`exists_literal_joined_family_bounds` uses the same `E,T` for any finite
radial/count family and pays `sqrt(E)*sum K_i` for either sign of its sum.
Both constants are **unevaluated**; `T>=5000` does not assert that the
sharper arithmetic estimates hold from 5000 itself. No zero or simplicity
hypothesis is used. The earlier theorem retaining the joint smooth term
`sum H_i` with its signs remains available and is not replaced.

## Quantitative scope and remaining work

The optional `scripts/probe_riesz_smooth_prime_tail.py` checks 820 partial
smooth tails, including orders zero and one, and 16 literal finite blocks
with total prime counts three through five. Those arithmetic blocks are
below the eventual threshold and use floating quadrature; they are not
certificates. The maximum tested smooth-tail/bound ratio is about `0.842`.

For a 4,096-period saddle block at `N=16384`, the new explicit single-order
cost is about `0.0472` times the previous joined-period cost, with both
unevaluated mean constants omitted. **This is not a uniform improvement**:
on a 16-period block at the same order, the ratio is about `9.77`. Keep
both proved estimates and choose only within their actual hypotheses.

The all-order binomial-cap diagnostic still gives growing source-normalized
positive budgets. For 16-period blocks their base-ten logarithms, omitting
`sqrt(E)` and other cofactor shells, are about `-5.24, -3.71, 4.23, 37.78`
at `N=16384,65536,262144,1048576`. A positive budget is not a carrier lower
bound, and this finite probe is not an asymptotic impossibility theorem.

The common-block smooth contribution is paid. What remains is the **total
source-scaled cost**, the actual cofactor-dependent prime holes, and a
unique ownership/incidence partition of the remaining carrier. A family
bound does not justify counting a label or previously paid credit twice.
Neither the whole `-79/1000-o(1)` floor nor the `3/2+o(1)` ceiling follows.
There is no new zero exclusion or RH proof.

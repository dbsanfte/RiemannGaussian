# Linear cost for the original Riesz cutoff difference

The joint estimate now pays a linear, rather than quadratic, cost for large
cutoff displacements. This is an independent arithmetic inequality for every
squarefree cofactor count and every real cutoff. The whole `-79/1000` floor
and `3/2` ceiling remain open.

Write `R_D(n) = sum_{d|n} mu(d) * (D-log d)_+`. Lean proves that one constant
`E > 0` satisfies, for every `A <= B` and squarefree subset `S` of `(1,X]`,

```text
sum_{n in S} (R_B(n)-R_A(n))^2 <= E*X*min((B-A)^2, B-A).
```

The earlier all-cutoff theorem had only `E*X*(B-A)^2`. The new estimate
improves the displacement power; it does not evaluate `E` or certify a
numerical starting order. The unit is excluded explicitly, as required by
the exact complementary-divisor reflection.

## Why the bound improves

For the exact hinge difference `f(d)`, finite Abel summation has positive
weights `b_k = f(k)-f(k+1)`. Lean proves

```text
0 <= b_k <= 1/k,    sum_k b_k = f(1) <= B-A.
```

The previous argument estimated each sharp-prefix mean separately. Here
the cross terms remain together. The proved signed Gram kernel decays as
`(4+|log k-log l|)^(-2)`, and the new numerical row inequality gives

```text
sum_l 1/[l*(4+|log k-log l|)^2] <= 4.
```

Thus the joint quadratic form pays `sum b_k`, instead of its square.
One split at `k^2 <= X` uses the existing direct and complementary Gram
estimates. Exact finite counting errors and the reflected `(n-1)/k`
endpoint are already paid. No fixed prime-count ceiling, prime-density
approximation, or hypothetical zero is used.

## Both signed sides, with the original weights

For any real weight `w(n)`, including the original correlated cosine,
allocation, and factorial factors, put

```text
J = sum_{n in S} w(n)*(R_B(n)-R_A(n)),
K^2 = (sum_{n in S} w(n)^2)*E*X*min((B-A)^2, B-A).
```

Lean proves `-K <= J <= K`. The terminal theorem applies this directly to
`residualCoefficient * zetaPrimeLogKernel` on an actual marked-prime fibre.
Squarefreeness, coprimality, at least two cofactor factors, the selected prime
set, the full phase, the original allocation, and all finite selections
remain in that statement. Exact composite reflection retains `mu(n)`.
Its squared budget is

```text
(sum_a (signedPrimeWeight(a,p)/a)^2)
  * E*X*min((log p)^2, log p).
```

For large `p` this saves a factor `log p` in the squared budget, or
`sqrt(log p)` in the two-sided error. It does not pay the displayed weight
energy or its aggregation over prime/radial periods. In particular, it
does not remove the original signed crossing corrections or the endpoint
terms created by deleting already-paid sectors. No credit is counted twice,
and no source-normalized smallness or zero exclusion is claimed.

## Verification and diagnostic

The source is
[`ZetaRieszLinearCutoffMean.lean`](../RiemannGaussian/ZetaRieszLinearCutoffMean.lean),
with audit record
[`riesz-linear-cutoff-mean-audit.json`](riesz-linear-cutoff-mean-audit.json).
The optional `scripts/probe_riesz_linear_cutoff.py` uses actual finite Mobius
divisor sums at three populations and 84 cutoff pairs. Floating results
illustrate both displacement regimes and separate composite cofactors from
prime labels. They neither certify `E` nor estimate the full signed carrier.

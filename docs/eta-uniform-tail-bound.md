# Exact adjacent eta ratios and uniform tail bounds

For every `s` with `Re(s)>0`, write `X=2N+1` for the first omitted odd
endpoint. Lean now proves, whenever `X>=|s|`,

```text
|eta(s)-eta_N(s)| <= 2 X^(-Re(s)),
|X^s(eta(s)-eta_N(s))-1/2| <= 3|s|/(2X).
```

The second estimate replaces the earlier bound `|s| |s+1|/X` on this
range. Its dependence on the argument is linear, allowing the cutoff
to dominate the ordinate itself rather than its square. In particular,
the normalized tail tends to `1/2` along arbitrary moving complex
arguments and cutoffs with `Re(s)>0` eventually and `|s|/X -> 0`.
There is no compactness or fixed-height assumption.

These are unconditional estimates for the actual eta function. They
improve the analytic error budget but do not provide the independent
signed finite-prefix bound needed to exclude higher interior zeros.

## The complex information retained

For real `x>0`, define

```text
delta(x) = log((x+1)/x),
q(s,x) = exp(-s delta(x)),
g(s,x) = 1/(1+q(s,x)),
H(s,x) = g(s,x) x^(-s).
```

Here `q` is the exact complex neighboring ratio:

```text
(x+1)^(-s) = q(s,x) x^(-s).
```

When `x>=|s|`, the phase step has absolute value at most one radian.
Consequently `Re(q)>=0`, `|1+q|>=1`, and `|g|<=1`. All denominators
are proved nonzero on the stated domain.

The complex exponential is contractive on the closed left half-plane.
For `y>=x>=|s|` and `Re(s)>=0`, this gives

```text
|q(s,y)-q(s,x)| <= |s|(delta(x)-delta(y)),
|g(s,y)-g(s,x)| <= |s|(delta(x)-delta(y)).
```

The step is decreasing and `0<=delta(x)<=1/x`. Thus the entire
variation cost telescopes. Bounding each original eta summand
separately would lose this cancellation.

These statements are proved in
[EtaAdjacentRatio.lean](../RiemannGaussian/EtaAdjacentRatio.lean), including
`cpow_add_one_eq_pairedEtaAdjacentRatio_mul`,
`pairedEtaAdjacentInverse_mul_add`, and
`norm_pairedEtaAdjacentInverse_sub_le`.

## Exact summation before the bound

Keep the two-step complex remainder

```text
R(s,x) = (g(s,x)-g(s,x+1)) (x+1)^(-s)
         + (g(s,x+2)-g(s,x+1)) (x+2)^(-s).
```

The adjacent multiplier identity gives exactly

```text
x^(-s)-(x+1)^(-s) = H(s,x)-H(s,x+2)+R(s,x).
```

For `x>=X>=|s|`, the variation estimate bounds a whole pair by

```text
|R(s,x)| <= |s| X^(-Re(s)) (delta(x)-delta(x+2)).
```

Summing this bound proves absolute convergence of the remainder and
the full-tail estimate

```text
sum_(n>=N) |R(s,2n+1)| <= |s| X^(-Re(s)) delta(X).
```

The paired eta series itself is already absolutely convergent on
`Re(s)>0`. Its finite boundary tends to zero, so the exact identity is

```text
eta(s)-eta_N(s) = H(s,X) + sum_(n>=N) R(s,2n+1).
```

No unordered convergence of the unpaired alternating series is assumed.
All three neighboring phases in each remainder, the complex boundary,
and the full signed series remain available.

After complex endpoint normalization,

```text
|X^s(eta(s)-eta_N(s))-g(s,X)| <= |s| delta(X).
```

Also `|g(s,X)-1/2|<=|s| delta(X)/2`. The normalized bound follows
using `delta(X)<=1/X`; the full tail bound follows from `|g|<=1` and
`|s| delta(X)<=1`.

The declarations in
[EtaUniformTailBound.lean](../RiemannGaussian/EtaUniformTailBound.lean)
include:

- `pairedEtaCorePartialSum_sub_eq_adjacent`;
- `summable_pairedEtaAdjacentDefect_tail`;
- `pairedEtaCore_tail_eq_adjacent`;
- `norm_pairedEtaCore_tail_sub_adjacent_le`;
- `norm_pairedEtaCore_tail_le_two`;
- `norm_pairedEtaCoreNormalizedTail_sub_adjacent_le`;
- `norm_pairedEtaCoreNormalizedTail_sub_half_le_scale`;
- `tendsto_pairedEtaCoreNormalizedTail_of_norm_div_endpoint_zero`.

## Consequence for the active RH problem

For every actual nontrivial zero `rho=beta+i*gamma`, at every cutoff
`X>=|rho|`, Lean proves

```text
|eta_N(rho)| <= 2 X^(-beta).
```

The theorem is `norm_pairedEtaCorePartialSum_zero_le_two`. The complete
complex identity additionally retains the finite prefix together with
`g(rho,X) X^(-rho)` and its explicitly controlled signed remainder.

An independent arithmetic inequality must still contradict those
forced finite-prefix values for every right-half zero. This slice does
not prove that inequality, does not exclude additional interior zeros,
and does not change the global RH objective. The earlier
[all-height edge strip](eta-centered-euler-zero-free.md) remains intact.

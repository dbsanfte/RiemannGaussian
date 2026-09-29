# Signed-main boundary investigation — no new bound

This investigation does **not** meet the requested mathematical milestone of
bounding the signed main expression. No new Lean theorem, cofinal floor,
ceiling, or zero exclusion is claimed. The previously checked results in
`ZetaRieszCofactorDiscrepancy` remain unchanged.

The [optional probe](../scripts/probe_riesz_main_boundaries.py) and
[recorded output](riesz-main-boundary-probe.json) examine the density part of
the [joint numerical probe](riesz-joint-main-probe.json). Ordinary primes in
the outer sum remain actual enumerated primes. The virtual prime subtraction
in the composite model is retained from that enumeration, with its original
complex phase. It is not replaced by a prime-density integral.

## What was evaluated

Write `t=log p`, `v=log n`, and let `U_N` be the existing `unpaidOrders`.
The exact owner polynomial in the diagnostic is

```math
P_N(t,v)=\sum_{k\in\{0,\ldots,N+1\}\setminus U_N}
             {N+1\choose k}t^{N+1-k}v^k.
```

For the density term alone, replace its ordinary-integer cofactor sum by
the ordinary integral. Under `n=exp(v)`, its integrand contains
`exp(-(1/2+iy)v) P_N(t,v)`. The recurrence

```math
I_0(v)=-\frac{e^{-\lambda v}}\lambda,\qquad
I_k(v)=-\frac{e^{-\lambda v}v^k}\lambda+\frac{k}{\lambda}I_{k-1}(v),
\qquad \lambda=\frac12+iy,
```

has derivative `exp(-lambda*v)*v^k`. It evaluates this integral without
freezing the total logarithm, deleting any owner factorial order, or
discarding the phase. The script keeps the lower radial endpoint, the upper
radial endpoint, and the endpoint `n=p-1` separately before adding them.

**The endpoint `n=p-1` comes from the extra diagnostic restriction
`p>whole cofactor`. It is not the actual largest-prime boundary of the full
carrier.** The full carrier also contains composites whose whole cofactor
exceeds their largest prime. An estimate for this diagnostic sector cannot
silently discard its neighboring sectors or their boundary cancellations.

## Results at height 54

All entries below include the source normalization, and are uncertified
floating real parts.

| Order | Lower radial term | Upper radial term | Sector boundary | Exact prime subtraction | Sector boundary + prime subtraction |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 14 | -1.13757e-6 | 0 | 7.49661e-8 | 1.26022e-7 | 2.00989e-7 |
| 16 | -3.11873e-6 | 1.08345e-7 | 2.24773e-7 | 2.92772e-7 | 5.17545e-7 |
| 18 | 1.83387e-5 | -9.42499e-6 | 1.31811e-7 | -1.06254e-6 | -9.30725e-7 |

The real differences between the discrete and integrated density terms are
approximately `-2.61e-11`, `-7.00e-11`, and `-2.14e-11`. Two independent
70-digit quadrature checks agree with the antiderivative at relative error
below `1e-50`. These checks validate the numerical implementation; they
are not proofs of the displayed errors or an asymptotic transport theorem.

The small-order total is dominated by radial endpoints. After those are
separated, the remaining signed quantity changes sign and grows in absolute
size across these tests. No decay conclusion follows. Moreover, the divisor
cutoffs are only 1, 2, and 3, respectively. These experiments do not test the
exponentially growing cutoff regime of the endgame.

All earlier limitations remain: nonowner allocation is omitted, the full
nested eligibility masks have not been verified, and the squarefree density
uses its floating Euler-product formula. Neither the numerical sum nor its
integral replacement is a bound for the complete literal masked carrier.

## Literature check

Friedlander and Iwaniec's [Asymptotic sieve for primes](https://arxiv.org/abs/math/9811186)
requires bilinear information in addition to divisor-sum error control.
Ford and Maynard's [On the theory of prime-producing sieves](https://arxiv.org/html/2407.14368v1)
formulates explicit Type I and Type II hypotheses and studies when their
ranges suffice. Its conclusions do not supply the missing Type II input for
our weights. In particular, the squarefree counting theorem alone is not an
application of either prime-producing theorem. Their logarithmic-error
statements also do not by themselves provide the fixed exponential saving
needed after the present source normalization.

This is an applicability audit, not a proof that the actual signed bound is
impossible or equivalent to RH. The unresolved mathematical target remains
the joint density/prime expression with the original correlated weights and
masks. No additional carrier representation has been introduced into Lean.

## Reproduce locally

```bash
../.venv/bin/python scripts/probe_riesz_main_boundaries.py --check-only
../.venv/bin/python scripts/probe_riesz_main_boundaries.py --max-order 18
```

The second command deliberately opts into the larger order-18 enumeration.
The default stops at order 16. Neither command belongs in ordinary CI or
in numerical-certificate verification.

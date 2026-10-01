# A geometric payment for complete polynomial-owner populations

[ZetaRieszPolynomialOwnerPayment](../RiemannGaussian/ZetaRieszPolynomialOwnerPayment.lean)
proves an independent source-scale bound for all original central labels
whose canonical largest prime is at most `(N+1)^32`. The entire selected
partial divisor response is paid, with its original factorial kernel,
allocation, complex phase and physical/count/radial masks retained. The
whole signed floor and zero exclusion remain **open**.

For every sufficiently large original order, uniformly over any selected
subset of that population, phase height and original incidence mask,

```math
\left\|u^{N+1}\sum_{n\in S}
 w_n c_{N,D_n}^{\mathrm{partial}}(n)K_N(3/2+iy,n)\right\|
 \le (39/40)^N,
\qquad 0\le u\le10001/20000,\quad\|w_n\|\le1.
```

The physical length hypothesis is the existing eventual `L >= 11N/8`.
The arbitrary original divisor selection may include both current affine
zero deletions. No new scalar carrier or completed prime row is introduced.

The finite Rankin comparison uses

```math
\sigma=63/64,\quad\sigma_0=129/128,\quad q=33/64,
\qquad
\sum_{p\le(N+1)^{32}}p^{-\sigma}
 \le (N+1)^{3/4}\mathcal M(\sigma_0).
```

Here `M` is the existing convergent positive integer count mass. The entire
squarefree divisor-choice Euler product is bounded by
`exp(2 M (N+1)^(3/4))`, which is eventually at most `exp(N/256)`.
The resulting explicit pre-absorption source bound is

```math
\frac{203}{50}\frac{10001}{20000}\,N r^N,
\qquad r=\frac{10001}{20000}\frac{64}{33}e^{1/256}<39/40.
```

The linear prefactor is then absorbed into the rational geometric rate.
These are bounds on an independently negligible population, not a norm
estimate for the whole central carrier. Every count is included in the
finite Euler identity; the estimate is uniform over the selected labels.

`eventually_central_smallOwner_crop_bound` removes this population inside
the current main. `eventually_polynomial_remaining_crop_bounds` combines
it with the earlier geometric hinge-allocation payment directly in
`polynomialCentralRemaining`. The large-owner, owner-gap and polynomial-row
credits are unchanged and subtracted exactly once.

The exponent 32 is deliberate. The original count ceiling implies that
labels with all primes at most `(N+1)^16` are eventually already absent:
their maximal total-log slope approaches `2 log 2 < 1.97`. Raising the
threshold to 32 avoids presenting that automatically empty population as
a new cofinal saving. This audit motivated the stronger
[all-geometry reduced-count payment](zeta-riesz-reduced-count.md), which is
the latest global floor-ledger endpoint. Do not add two overlapping
population credits without an explicit disjoint decomposition.

There are 16 checked public theorems. The
[proof audit](riesz-polynomial-owner-audit.json) records their transitive
axioms, source hashes and focused checks. The optional
[regression](../scripts/probe_riesz_polynomial_owner.py) checks the exact
finite Euler/count identity and original dyadic core labels at `(640,16)`
and `(1536,32)`. It is outside builds and CI. Neither the full comparison
mass nor the effective geometric starting order is evaluated. Displayed
finite-order rate values and underflowed sample amplitudes are not floor
certificates. Wider publication gates are deferred; this work is local.

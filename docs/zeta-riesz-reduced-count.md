# A global signed count-population payment

[ZetaRieszReducedCountPayment](../RiemannGaussian/ZetaRieszReducedCountPayment.lean)
lowers the independently paid count threshold from `omega >= K_j` to
`256 omega >= K_j`. The bound applies to the actual retained central labels
across **all share geometries and radial periods**, with the full original
complex phase, allocation and partial divisor selection. It uses no zero
or unproved cancellation hypothesis. The whole `-79/1000` floor remains
**open** on the complementary signed rows.

Keep the original schedule

```math
K_j=2^{j+3},\qquad N_j=8(j+4)K_j,
\qquad 1.97N_j<\log n\le2.03N_j.
```

For the literal selected incidence population, the checked eventual bound is

```math
\left\|u^{N_j+1}\sum_{n\in S_j}
 c^{\mathrm{partial}}_{N_j,D_n}(n)K_{N_j}(3/2+iy_j,n)\right\|
 \le \frac{203}{50}\frac{10001}{20000}(N_j+1)r_*^{N_j},
\qquad 256\omega(n)\ge K_j.
```

This is **one** aggregate error, not a price per count or per prime period.
Both Riesz hinges and the original product label on the factorial kernel
are retained. The theorem is uniform in moving heights and selected masks.
The existing eventual `L >= 11N/8` supplies the coefficient normalization.

The exact saving is

```math
b=\exp\!\left(\frac{\log(17/16)}{256}\right),\qquad
b^{N_j}\le K_j^{\omega(n)}.
```

It follows by raising the original dyadic count inequality to the matching
256th-power comparison. The whole selected count mass is then bounded by

```math
\sum_{n\in S_j}2^{\omega(n)}n^{-\sigma}
\le\frac{\exp(2K_j\mathcal M(\sigma))}{b^{N_j}},
\qquad\sigma=1000001/1000000>1.
```

With `q = 499999/1000000`, the normalized geometric rate before absorbing
the sublinear count cost is

```math
r=\frac{10001/20000}{q b}<1,
\qquad r_*=(1+r)/2<1.
```

Numerically `r` is about `0.9998651892` and `r_*` about `0.9999325946`.
Lean proves their strict inequalities by exact rational arithmetic and the
identity `b^256 = 17/16`. The count Euler cost is sublinear because
`K_j/N_j = 1/(8(j+4)) -> 0`, so it can be absorbed in the fixed geometric
slack. This beats the unwanted source growth; it does not just improve a
polynomial prefactor of `(2u)^N`.

`eventually_central_reducedCount_crop_bound` removes the complete selected
population after both affine zero deletions. The terminal
`eventually_remaining_reducedCount_bounds` is a **direct two-sided inequality
for `polynomialCentralRemaining`**, including the earlier hinge-allocation
error. Every previous large-owner, owner-gap and polynomial-row credit is
unchanged and subtracted once. No high-count credit is reused elsewhere.
The sum of the two errors tends to zero.

`count_lt_after_crop` states the exact new support: `256 omega < K_j`.
`retained_hinge_count_bounds` also keeps the proved hinge lower endpoint,
so those remaining genuine hinges have `7 <= omega < K_j/256`.
This is a factor-256 reduction of the count threshold, **not a percentage
bound on the remaining signed mass**. Fixed low counts and all still-retained
growing counts need their independent joint estimate. The old divergent
positive allowance is not reused. The source, floor, ceiling, restricted
zero exclusion and RH claims are unchanged.

There are 15 checked public theorems. The
[proof audit](riesz-reduced-count-audit.json) records the focused build,
ordinary-root-plus-module namespace lint, all public transitive axioms and
source hashes. The optional
[regression](../scripts/probe_riesz_reduced_count.py) checks the exact power
saving at original dyadic orders and revisits mask-preserving hinge labels.
The full comparison mass and starting order are **not evaluated**. In
particular, although small sample orders satisfy the count predicate, the
eventual rate does not certify a finite-order payment there. Numerical
underflow is never cancellation evidence. The probe is outside builds/CI;
this slice is local and the published README/explorer endpoint is unchanged.

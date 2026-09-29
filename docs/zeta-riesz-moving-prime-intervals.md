# Moving prime intervals with exact retained factorial costs

`ZetaRieszMovingPrimeIntervals` proves both signed bounds for the original
retained carrier when each cofactor chooses its own prime interval. The
earlier common-interval restriction is removed. The price is a binary
maximal-sum budget, rather than variation of all endpoints across cofactors.
The [audit](riesz-moving-prime-intervals-audit.json) records the compiled
theorems, source hashes, axioms and optional numerical regression.

## The inequality

Take finite prime cells `P_i`, padded by empty cells to `2^b` entries.
For each squarefree composite cofactor `n` in `S subset (1,X]`, retain
only cells `lo(n) <= i < hi(n)`. The endpoints can depend arbitrarily on
`n`. Eligibility and coprimality are required only for retained primes.
For order `j`, the two common signed prime coefficients are

```math
c_j(p)=\frac{e^{-\log(p)/2}(\log p)^j}{p}\cos(y\log p),\qquad
s_j(p)=\frac{e^{-\log(p)/2}(\log p)^j}{p}\sin(y\log p).
```

For a binary block `I`, define its two finite divisor profiles by

```math
f_{j,I}^{c}(d)=\sum_{i\in I}\sum_{p\in P_i}c_j(p)
 \big[(L-\log d)_+-(L-\log p-\log d)_+\big],
```

and likewise with `s_j`. For any integer `R` with `exp(L)<R+1`, put

```math
Q_j(I)=\sum_{k=1}^{R}k\left[
 (f_{j,I}^{c}(k)-f_{j,I}^{c}(k+1))^2+
 (f_{j,I}^{s}(k)-f_{j,I}^{s}(k+1))^2\right].
```

Every prime sum is taken **before** squaring, retaining its cross terms.
Let `D_j` be the sum of `Q_j(I)` over the nodes of the binary subdivision.
The exact retained factorial coefficients satisfy

```math
(1-\operatorname{boundedShare}(A,N,pn))(\log(pn))^{N+1}
 =\sum_{j=0}^{N+1}B(n,j)(\log p)^j.
```

They are nonnegative. The new terminal theorem uses their **exact** energy,
not their binomial caps. With `w_j(n)=exp(-log(n)/2)B(n,j)/n`, one proved
but unevaluated constant `E>0` gives `-K<=J<=K`, where

```math
J=\Re\sum_{n\in S}\sum_{i=\mathrm{lo}(n)}^{\mathrm{hi}(n)-1}
 \sum_{p\in P_i}\operatorname{residualCoefficient}(A,L,N,pn)
 K_N(3/2+iy,pn),
```

```math
K=\frac{2\sqrt{EX(b+1)}}{LN!}
 \sum_{j=0}^{N+1}\sqrt{\sum_{n\in S}w_j(n)^2}\sqrt{D_j}.
```

Lean writes the square roots as a single square root per order in
`retainedMovingCost`. This is the same nonnegative quantity for `L>0`.
The proof combines the existing unconditional squarefree divisor mean,
exact cosine/sine rotation, two prefix bounds and finite Cauchy–Schwarz.
All orders, including zero and one, remain. No prime-density approximation,
zero hypothesis, simplicity assumption or upper prime-count ceiling enters.
Unlike the analytic prime-tail estimate, this finite-energy inequality has
no eventual starting-height condition: its actual energy must still be paid.

## Literal masks and ownership

`exists_literal_union_bounds` identifies disjoint prime cells with their
actual selected union. `exists_literal_owned_bounds` additionally uses
strict largest-prime ownership to identify a genuine finite set of integer
labels. Thus those selected labels are counted exactly once.

The endpoints can encode radial, largest-prime and other interval masks.
This theorem does not assert that every current core mask has already been
reindexed into such intervals. Internal holes require explicit separate
runs; arbitrary missing primes cannot be filled. The finite-family theorem
adds the exact costs without an extra family-cardinality multiplier, but
applying it to the whole core still requires a disjoint cover.

## Optional numerical test

Run `../.venv/bin/python scripts/probe_riesz_moving_prime_intervals.py`.
It uses actual primes, exact integer squarefreeness and ownership, the
moving physical length, `1.95N<log(pn)<=2.03N`, the nondominant `.65` mask,
the original allocation formula and full phase at `y=54`. It checks every
selected interval is contiguous and every integer label is unique. The
original allocation and its polynomial expansion agree to floating error.

| N | Cofactor population cap | Selected labels | Old variation cost | New moving cost |
|---|---:|---:|---:|---:|
| 6 | 4,096 | 2,130 | 14.1284 | 0.155837 |
| 8 | 65,536 | 285,908 | 71.1341 | 0.165997 |

These are source-normalized cost formulas **before the unevaluated
`sqrt(E)`**, at `u=10001/20000`. They use the same labels and reproduce the
earlier signed sums. In the stricter subpopulation where every cofactor
prime exceeds `N^2`, the new costs are `0.0392035` and `0.0477379`.
This diagnostic is optional and never part of ordinary CI. Finite floating
results do not certify `E`, an eventual rate or the whole carrier.

## Remaining quantitative target

The theorem pays moving interval endpoints and retains substantially more
information in the explicit cost. A disjoint cover of every surviving core
geometry and a sufficiently small **total source-normalized cost** remain
open. Neither whole-carrier threshold, `-79/1000` nor `3/2`, is proved here.
There is no new zero exclusion or RH claim. Previously included companion
terms must not be added again as extra credit.

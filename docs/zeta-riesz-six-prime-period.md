# Signed six-prime cancellation in both whole bounds

Lean now proves a signed population estimate for an extremal negative
six-prime coefficient, and spends it in both existing whole `J+C`
comparisons. It requires no zero or simplicity hypothesis. The final
`-79/1000` floor and `3/2` ceiling remain open.

## The literal population

Write `n = p r q₁ q₂ q₃ q₄`, with distinct ordinary primes. The largest
prime is `p`; the four middle-prime logarithms and least-prime logarithm
satisfy

```math
\frac{14}{125}v<\log q_i\le\frac{27}{200}v,
\qquad 0<\log r\le\frac{v}{200}.
```

There is no lower cutoff on `r`. The largest prime runs over the entire
cofactor-dependent interval

```math
v-\frac\pi{|y|}<\log n\le v+\frac\pi{|y|},\qquad \cos(yv)=-1.
```

The interval lies inside the original `1.95N..2.03N` core. The literal
moving length eventually satisfies `0.67v <= L_N <= 0.72v`. Every prime
share is at most `9/16`, so all original physical, nondominant, count and
allocation masks are retained. Lean proves that this population is
nonempty in every sufficiently late period, already using `r=2`.

## Exact coefficient before any norm

At `D = log(n)-L`, all pairs of middle-prime logs lie below `D-log r`,
and every triple lies above `D`. The four-prime response is therefore
exactly affine with slope three at both cutoffs. Inserting the least
prime leaves `R_D(r q₁ q₂ q₃ q₄)=3 log r`. Reflection and the six-prime
parity give the original coefficient:

```math
c_L(n)=-3\frac{\log n}{L}\log r.
```

This is an extremal coefficient, rather than a nearly zero subfamily.
Its full factorial weight and cosine remain inside the largest-prime
sum. The signed period theorem is applied there before taking an
absolute value. Unique largest-prime ownership prevents duplicate
integer incidences.

The remaining positive cofactor mass is bounded using actual prime
counts. In particular, retaining the least-prime logarithm pays the
entire small-prime range. Overcounting the four middle-prime tuples is
used only for this positive mass after the signed period has been paid.
Lean proves, eventually,

```math
\sum_{a\in\mathcal A_v}\frac{\log\minFac(a)}a\le\frac v{25000},
\qquad
\left|\Re\sum_{n\in Z_v}c_L(n)K_N(n)\right|
\le\frac{m}{100000}Vh,
\qquad h=\frac\pi{4m|y|},
```

where

```math
0<V\le\frac{e^{-v/2}v^N}{N!}\le\frac{501}{500}V.
```

The retained allocation changes this bound only by the already-proved
geometrically decaying `allocationBound`. This is a relative local
payment; its source-normalized radial debit is **not** asserted to tend
to zero.

## The exact whole ledger

The new population `Z` is disjoint from every earlier paid population:
`P` (three/four/five-prime selections), `I` (positive-five interior),
`H` (five-prime small boundary), `Q` (the previous unbalanced triple
period), and `D` (the owner band). Both certified whole comparisons now
retain

```math
E_N=S\setminus(P\cup I\cup H\cup Q\cup Z\cup D),
\qquad M_N=\left(\frac1{16}\sqrt{N+1}-\frac18\right)G_N.
```

Both retain all previous favorable observations and the favorable real
part of the coupled `Z` sum. The vanishing error includes two geometric
allocation bounds, one for each paid period population. The previous
second-reflection six-prime costs still apply only to `E_N`.

The smaller rest must not be paired with the earlier `2/25` margin. The
floor and ceiling use alternative selections of `P`; their credits
cannot be added together. All finite-cover premises are discharged by
the previously checked assemblies; no exhaustive certificate enters
ordinary builds or CI.

## Checked endpoints and remaining task

- [Literal signed population, masks and whole comparison](../RiemannGaussian/ZetaRieszSixPrimePeriod.lean).
- [Concrete whole floor and ceiling](../scripts/CheckRieszSixPeriodJoint.lean).
- [Whole comparisons retaining second-reflection savings](../scripts/CheckRieszSixPeriodWhole.lean).
- [Machine-readable proof and cached-cover audit](riesz-central-capacity-audit.json).

The unpaid rest still contains other six-prime geometries, other prime
counts and other phase periods. No independent cofinal numerical floor
or ceiling for that rest has been proved. The next progress must bound
those signed populations jointly; another isolated coefficient
reformulation does not close the remaining arithmetic gap.

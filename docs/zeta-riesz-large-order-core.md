# Pay two outer strips at large order

[`exists_contracted_core_bounds`](../RiemannGaussian/ZetaRieszLargeOrderCore.lean)
pays the actual original-core contribution outside

```math
\boxed{\frac{1971}{1000}N<\log n\le\frac{2029}{1000}N}
```

with the explicit geometric rate

```math
\boxed{\|\text{source-normalized outer contribution}\|
\le C\exp(-N/10^6).}
```

There is one finite constant `C` for **every order, height, count cutoff
and radius `0<=u<=10001/20000`**. The constant is not numerically evaluated.
This is an independent arithmetic bound for the literal residual
coefficient, retaining its allocation, full phase, physical cutoffs and
all earlier masks. No zero hypothesis or prime-density approximation is
used. The [proof audit](riesz-large-order-core-audit.json) records the scope.

## The checked rate

Use the fixed summability tilt `sigma=1+1/10000000`. At both endpoints
`x=1971/1000` and `x=2029/1000`, Lean proves

```math
\log(Ux)+(\sigma-3/2+1/x)x<-10^{-6},
\qquad U=10001/20000.
```

Rational bounds for the logarithm and exponential prove these strict
inequalities. The existing full factorial deviation estimate then pays
both selected arithmetic tails with the same rate. The error tends to
zero even for moving heights, radii and count cutoffs.

## Effect on both original inequalities

Let `H2,C2,H3,C3` be the exact quadratic and cubic centers and costs on
the intersection of the original squarefree core with this window.
The original, unchanged core satisfies

```math
\max(H_2-C_2,H_3-C_3)-Ce^{-N/10^6}
\le u^{N+1}\operatorname{Re}(\mathrm{coreResponse}_N)
\le\min(H_2+C_2,H_3+C_3)+Ce^{-N/10^6}.
```

Both corrections remain signed, and `C3<=C2` is proved with the same
arithmetic constant. The original carrier is not redefined. Its outer
contribution is paid before the joint energy is charged to the remaining
population.

## The central obstruction remains

This theorem pays the outer strips of the previous `1.95N..2.03N`
core. It does **not** prove an eventual bound for the surviving central
cost. At `log n=2N`, the factorial/source growth still has positive
exponent `log(2u)` when `u>1/2`; a finite-order energy improvement alone
does not settle that rate.

The remaining target is the combined signed center and cost on the
contracted support. The independent whole `-79/1000` floor and `3/2`
ceiling remain open. No new zero exclusion or RH contradiction follows.

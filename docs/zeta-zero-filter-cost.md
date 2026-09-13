# The complete cost of the actual zero-isolating filter

[ZetaZeroFilterCost](../RiemannGaussian/ZetaZeroFilterCost.lean) bounds the
whole original pole-jet filter, its exact density primitive, and the error
between the finite prime band and its signed Chebyshev-error integral.
The coefficients are determined by the actual local zeta divisor. No
coefficient search or assumed normalization constant enters these bounds.
The independent signed arithmetic lower bound remains open.

## Scope and explicit coefficient bound

Let `rho=beta+i*t` be a nontrivial zero satisfying

```math
\beta>\tfrac12,\qquad |t|\ge10^6,\qquad
1-\beta\le\tfrac32d(t),\qquad
d(t)=\min\left\{\frac1{450000},\frac{32}{45\log(|t|+2)}\right\}.
```

The existing universal curve requires `1-beta>d(t)`: the additional
hypothesis selects a possible boundary layer, not the entire remaining
right half-strip. Set

```math
E=\Re\left(-\frac{\zeta'}{\zeta}(3/2)\right),\qquad
D(t)=\left\lceil4+2E+\log(3/2+|t|)\right\rceil_++1.
```

`E` is one fixed real Euler derivative value, independent of the zero;
no numerical enclosure is needed. The ceiling is Lean's natural-number
ceiling. `degreeAllowance_eq` proves the expression exactly.

For the actual `p_rho=zetaRightHalfPoleJetFilter rho h_rho`,
`actual_coefficient_bound` proves, for every real `R>=0`,

```math
\sum_k |[X^k]p_\rho|R^k
\le\left(\frac{2(1+R)}{d(t)}\right)^{D(t)}.
```

The filter retains its original normalization
`p_rho(1/(3/2-beta))=1`, cancels every other zero mode in its adaptive
local divisor, and has a double root at the pole mode `c=(1/2+i*t)^(-1)`.
Those properties are proved in
[ZetaMoebiusPoleJetFilter](../RiemannGaussian/ZetaMoebiusPoleJetFilter.lean).

## Exact product before the estimate

For nonzero local coordinates `i,j`, `inverse_factor_measure` proves

```math
M\!\left(\frac{X-(-j^{-1})}{-i^{-1}-(-j^{-1})}\right)
=\frac{|i|\max\{|j|,1\}}{|i-j|},
```

where `M` denotes Mahler measure. The extra denominators from inverted
coordinates cancel exactly. `inverse_basis_measure` retains the product
over every other node.

For the selected zero, `|i|<1`; every other local zero has `|j|<1`.
[Gaussian separation](zeta-gaussian-zero-separation.md) bounds each zero
factor by `2/d(t)`. Each of the two pole factors costs at most two, because
its large ordinate is kept in both numerator and denominator.

`unit_disc_card_bound` pays for all distinct local zeros using the actual
global xi Poisson mass. Each zero in the unit disc about `3/2+i*t`
contributes at least one half. The complete local count plus the extra
pole factor is therefore at most `D(t)` (`support_card_succ_le`).

Finally, `coefficientCost_le` uses the Mignotte coefficient estimate already
formalized in Mathlib's `Analysis/Polynomial/MahlerMeasure`:

```math
\sum_k |[X^k]p|R^k\le M(p)(1+R)^{\deg p}\quad(R\ge0).
```

There is no unknown factor count or spacing constant in the result. This
slice makes no historical novelty claim for that classical inequality.

## The same cost reaches the signed arithmetic carrier

Write `s=3/2+i*t` and `q=-c*p_rho/(X-c)`, with `c=(s-1)^(-1)`.
The polynomial quotient is exact. `primitive_measure_le` and
`primitive_degree_le` prove `M(X*q)<=M(p_rho)` and `deg(X*q)<=deg(p_rho)`
when `|c|<=1`, a condition discharged at these heights. Hence
`actual_primitive_coefficient_bound` gives the same weighted bound for
`X*q`. This is the shifted primitive evaluating the continuous-density
part of the original prime band.

Let `B_N=zetaOrdinaryPrimeBandFilter p_rho N t` and
`J_N=zetaPrimeBandChebyshevIntegral p_rho N t`. The latter retains the full
complex derivative kernel against `x-theta(x)` on the original band
`exp(N*log(2)/4)<x<=2^(32*N)`. Then
`actual_band_discrepancy_bound` proves

```math
|B_N-J_N|\le2^{-N}\,2(\log4+2)
\left(\frac{10}{d(t)}\right)^{D(t)}.
```

The prefactor is explicit in height and independent of `N`; it is not
uniformly bounded over unbounded heights. Both endpoints and the exact
density primitive are controlled. The signed bulk is retained.

For `u=3/2-beta`, `actual_centered_source_limit` proves

```math
u^{N+1}J_N\longrightarrow-1.
```

The [multiplicity theorem](zeta-gaussian-multiplicity-depth.md) discharges
simplicity in this layer. Proper prime powers, prime-band tails and the
band reduction error vanish independently. The negative limit itself
uses the hypothetical zero; it is not an independent arithmetic bound.

An independent `epsilon>0` and a cofinal lower bound
`Re(u^(N+1)*J_N)>=-1+epsilon` would contradict this limit. The
[absolute-envelope obstruction](zeta-prime-envelope-rate.md) still applies:
coefficient control does not turn a subexponential full-density error
envelope into the needed signed cancellation.

The [carrier information audit](signed-prime-carrier-information-audit-2026-09-12.md)
traces the exact signed chain and the correlations left unused by the
Gaussian, matrix and absolute-envelope estimates.

## Verification and navigation

The module is root-imported and its public declarations are in the
compiled status inventory. The explorer's **Filter cost** endpoint exposes
the coefficient bound, geometric discrepancy and negative source as three
separately scoped conclusions. The default remains the actual zero-free
curve. Source links and axiom audits are generated from Lean. This work
remains local under the commit hold.

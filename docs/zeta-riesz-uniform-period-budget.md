# One joint counting budget for the cutoff family

Lean now controls an entire signed family of logarithmically separated
Möbius cutoffs with a linear squarefree population budget. The estimate
has no factor counting the periods and no leftover integer-rounding error.
It also applies to the existing varying owner allocation and moving
interval endpoints. The actual prime-weight energy and complete
source-normalized cost remain open.

Write `M_R(n)=sum(d|n, d<=R) mu(d)`. For a finite family satisfying

\[
0<R_i,\qquad
h|i-j|\le |\log R_i-\log R_j|,\qquad h>0,
\]

one proved, unevaluated constant `E_h` gives

\[
\boxed{\displaystyle
\sum_{n\in S}\left(\sum_{i\in I}a_iM_{R_i}(n)\right)^2
\le E_h X\sum_{i\in I}a_i^2.}
\]

Here `S` is any squarefree nonunit selection in `(1,X]`. The budget uses
`X`, not `card(S)` or the length of a shorter interval. Both the cutoffs
and their signed coefficients are fixed across this population.

## Why the finite errors no longer accumulate

Below the square-root transition, the existing direct lcm cross quadratic
has inverse-square decay in logarithmic cutoff separation. Its actual
finite counting error `R_i R_j` has the same decay after division by `X`.

Above the transition, squarefree reflection gives the exact moving
cutoff `floor((n-1)/R_i)`. When both complementary cutoffs are nonzero,
Lean proves

\[
|\log R_i-\log R_j|
\le |\log\lfloor(n-1)/R_i\rfloor
       -\log\lfloor(n-1)/R_j\rfloor|+1.
\]

Zero complementary cutoffs contribute zero and are retained. Thus
reflection preserves the needed separation up to a fixed constant.
For each complementary divisor pair the exact integer interval is

\[
\max(R_i d,R_j e)<n\le X,\qquad\operatorname{lcm}(d,e)\mid n.
\]

There is only one rounding error per pair. Its total
`floor(X/R_i) floor(X/R_j)` also has summable decay in logarithmic
separation. A finite Schur estimate controls the complete signed family.
Splitting once at the square-root transition costs a fixed factor;
there is no separate estimate charged to every period.

## The original owner and moving endpoints

The earlier owner theorem proves total variation at most two for the
exact allocation weight. Combining its maximal estimate with the new
linear mean bounds every binary block, including its counting error.
For `2^b` periods and `N>=32`, Lean now proves

\[
\sum_{n\in S}
\left(\sum_{i\in[\ell(n),r(n))}
 \operatorname{ownerWeight}_N(x_{n,i})\,a_iM_{R_i}(n)\right)^2
\le 36(b+1)^2E_hX\sum_{i<2^b}a_i^2.
\]

The endpoints may depend on the cofactor, and the literal owner shares
`x(n,i)=log(n)/T(n,i)` are allowed when the positive radial lengths
increase along the retained interval. The original strict `cutoffSlope`
is identified using `R_i<exp(D_i)<=R_i+1`; neither endpoint rounding nor
the original owner allocation is removed.

Both signed inequalities `-K<=J<=K` hold after inserting arbitrary
common real weights `w(n)`, with

\[
K^2=\left(\sum_{n\in S}w(n)^2\right)
36(b+1)^2E_hX\sum_{i<2^b}a_i^2.
\]

The estimate now also retains any nonnegative decreasing factor `v(n,i)`
bounded by `D`, at just `D^2` times the same mean budget. There is no
additional factor counting periods or binary levels. Abel summation
selects the largest original signed owner prefix separately for each
cofactor; the existing moving-endpoint theorem bounds these prefixes
together.

In particular, keep the actual reciprocal-log expression
`1/(T(n,i)-log(n))`. If each cofactor has a positive lower bound
`delta(n)<=T(n,i)-log(n)`, the corresponding signed bound uses

\[
K^2=\left(\sum_{n\in S}\frac{w(n)^2}{\delta(n)^2}\right)
36(b+1)^2E_hX\sum_{i<2^b}a_i^2.
\]

Thus favorable cofactor geometry need not pay the worst lower bound
from another cofactor. This controls the reciprocal-log factor exactly;
it does not replace the literal prime moments by a smooth density or
bound their irregular signed error.

The weight energy is explicit and unpaid. The base coefficients `a_i`
and cutoffs `R_i` remain fixed across labels. Arbitrary `a_i(n)` and
cofactor-dependent holes within the retained interval are not covered.
The actual prime moments contain additional cofactor dependence, and
their signed cutoff correction must still be controlled jointly.
Previously paid sectors must remain disjoint. Neither the whole
`-79/1000` floor nor the `3/2` ceiling is proved; there is no new zero
exclusion or RH claim.

## Optional finite diagnostic

`scripts/probe_riesz_separated_mean.py` constructs literal Möbius prefixes
on squarefree nonunit labels, then computes the normalized Gram matrix
for doubling cutoffs. With the whole family retained, the largest
eigenvalues are approximately `1.4895`, `1.4969`, and `1.5000` for
populations `32768`, `131072`, and `524288` and respectively 16, 18, and
20 cutoffs. This supports testing a bound independent of family size;
it does not certify the theorem's constant. Eigenvalues use floating
arithmetic, the prime phase is absent, and the probe is outside ordinary CI.

Sources:
[joint separated means](../RiemannGaussian/ZetaRieszSquarefreeSeparatedMean.lean),
[literal owner estimates](../RiemannGaussian/ZetaRieszOwnerUniformMean.lean).
The [correlated density bounds](../RiemannGaussian/ZetaRieszOwnerDensity.lean)
retain cofactor-dependent reciprocal logarithms.
Audit: [riesz-uniform-period-audit.json](riesz-uniform-period-audit.json).

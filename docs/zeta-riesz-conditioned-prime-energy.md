# Deduct the known arithmetic correlation from both bounds

[`exists_core_conditioned_bounds`](../RiemannGaussian/ZetaRieszConditionedPrimeEnergy.lean)
further narrows the enclosure for the **entire original source-scaled
core**. It preserves the preceding signed center and reduces its error
cost. The [proof audit](riesz-conditioned-prime-energy-audit.json) records
the checked scope and optional numerical diagnostics.

## Exact saving

Start with the [quadratic profile correction](zeta-riesz-quadratic-prime-energy.md).
In one common prime coordinate let `w(n)` be the full original signed
weight and `f` its divisor profile. Put

```math
M=\sum_n w(n)M_2(n),\qquad
V=Q_X^\circ(\log^2),\qquad
Q=Q_X^{(2)}(f),\qquad
A=EX\sum_n w(n)^2.
```

`M2(n)` is the exact second logarithmic divisor moment. It vanishes on
all squarefree cofactors with at least three primes and equals
`2 log(q) log(r)` on a two-prime cofactor. The signed center from the
preceding theorem remains unchanged.

The residual profile is orthogonal to `log²` in the centered energy.
The existing arithmetic mean bound therefore controls every linear
combination of these two profiles with the **same** `E`. Applying it to
all such combinations gives the stronger bound

```math
\left|\sum_n w(n)D_n\bigl(f-\alpha_X(f)\log^2\bigr)\right|^2
\le \left(A-\frac{M^2}{V}\right)Q.
```

Nonnegativity of the remaining allowance is proved. The case `V=0` is
handled separately and uses Lean's zero-division convention consistently;
no singular case is dropped. `squaredAllowance_saving` proves that the
exact deduction from the previous squared allowance is

```math
AQ-\left(A-\frac{M^2}{V}\right)Q=\frac{M^2Q}{V}\ge0.
```

`squaredAllowance_strict` proves a strict saving when `M` is nonzero and
both profile energies are positive. Its sign does not need to be favorable:
the deduction uses the square of an already retained arithmetic correlation.

## Whole original carrier

Summing the coordinate costs gives `conditionedCost`. Lean proves

```math
K_{\mathrm{conditioned}}\le K_{\mathrm{quadratic}}\le B_0,
\qquad
\max(-B_0,H-K_{\mathrm{conditioned}})\le J
\le\min(B_0,H+K_{\mathrm{conditioned}}).
```

These comparisons use the **same arithmetic constant, signed center,
coordinates and original weights**. Both endpoints can only improve.
`exists_literal_conditioned_bounds`, `exists_whole_conditioned_bounds`
and `exists_core_conditioned_bounds` transfer the estimate through the
actual masks and exact canonical ownership. All original prime counts,
factorial orders including zero and one, physical cutoffs, allocation,
prime-row holes and product phase remain together. There is no zero
hypothesis, count split, extra companion credit or prime-density replacement.

The source-scale numerical size is still open. This theorem does not
evaluate `E`, pay the signed triple center, or establish either final
whole-sum threshold.

## Optional quantitative check

Run:

```sh
OPENBLAS_NUM_THREADS=4 ../.venv/bin/python \
  scripts/probe_riesz_quadratic_prime_energy.py \
  --expand-population --conditioned-constant 1
```

The last argument is an **assumed diagnostic constant**, not a proved
arithmetic constant. The program records this explicitly. The new cost
depends nonlinearly on `E`; do not multiply its displayed value by
`sqrt(E)` and call that the general bound. Floating calculations are not
certificates and remain outside ordinary CI.

At nominal `E=1`, `u=10001/20000` and `y=54`, the enlarged order-eight
test changes the quadratic cost from approximately `0.00336144` to
`0.00335904`. On the subset whose cofactor primes all exceed `N²`, it
changes `0.000575931` to `0.000574239`. These are modest finite gains.
The populations do not reproduce every earlier nested core deletion,
and no eventual rate or numerical threshold follows.

## Remaining target

Bound the **combined signed endpoint**, using the unchanged triple
correction and the smaller residual cost. The independent
`-79/1000-o(1)` floor and `3/2+o(1)` ceiling remain open. Neither a new
zero exclusion nor an RH contradiction is claimed.

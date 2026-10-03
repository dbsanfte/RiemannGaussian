# A signed cubic correction retaining count three

The independent whole-carrier floor remains **open**. This local pass proves
a further exact correction and transfers its credit to `joinedPhysical`
with the same `nativeError`. Its finite numerical gain is small; this is
not a cofinal arithmetic estimate or a zero exclusion.

Proof: [ZetaRieszTangentCubicCredit.lean](../RiemannGaussian/ZetaRieszTangentCubicCredit.lean).
Receipts: [audit](riesz-tangent-cubic-credit-audit.json).

## Keep the cubic defect instead of deleting the triples

For the original squarefree support `S`, complex weight `W`, finite endpoint
`X` and order `N`, let

```math
f_3(d)=\frac{(\log d)^3}{(N+1)^2}
```

with the existing exact endpoint centering, and let

```math
M_3=\sum_{n\in S}W(n)\sum_{d\mid n}\mu(d)f_3(d).
```

The cubic divisor moment vanishes when the prime count is at least four.
For three distinct primes it is exactly

```math
\sum_{d\mid pqr}\mu(d)(\log d)^3
=-6\log p\log q\log r.
```

The new checked `cubicMoment_eq_three` therefore retains **exactly** the
original count-three moment, with its full phase and allocation. It does
not assume that this moment vanishes or has the selected-zero phase.

For the complete complex cutoff prefix
`Phi_k = sum_n W(n) sharp k n`, take the real increment

```math
V_k=\frac{\operatorname{Im}M_3\operatorname{Re}\Phi_k
          -\operatorname{Re}M_3\operatorname{Im}\Phi_k}{|M_3|}
       \bigl(f_3(k)-f_3(k+1)\bigr).
```

At `M_3=0` this defined direction is zero. The exact finite Abel identity
gives `sum_k V_k=0` without a prime-phase approximation. Count three is
present throughout. No subset is assumed to have zero imaginary part.
`sum_tangentIncrement_zero` proves the same principle for any real finite
profile with its endpoint retained.

## The whole-carrier inequality and its funding

Join this direction with the former six corrections **before** pricing
complete cutoff periods. `tangentCost` retains all early, late, zero and
crossed groups. `tangentCredit` takes the larger of the former credit and
the new exact saving against their **one common baseline cost**. It does
not add separately funded credits.

The checked comparison is

```text
oldJointCredit <= tangentCredit <= baselineCost.
```

The previous credit is recovered exactly at zero new coefficient. The
terminal unconditional inequality is

```text
Re(u^(N_j+1) * joinedPhysical_j)
  >= -nativeCost_j + nativeTangentCredit_j - nativeError_j.
```

All count, radial, owner, physical and allocation masks are unchanged.
There is no new imaginary tilt or analytic error. The conditional theorem
`false_of_cofinal_tangent_credit` still requires the **unproved** cofinal
bound `nativeCost-nativeTangentCredit <= 399/5000`. It is not a closed
floor theorem.

## Why the early cutoff is not free

At cutoff one, every label has the same divisor prefix. Its phase channel
is the common complex moment `M_0 = sum_n W(n)`, while the whole cubic
defect has phase channel `M_3`.

The new `no_free_unit_cutoff_direction` proves a precise restriction. If
the first profile difference is nonzero and `M_0,M_3` are noncollinear,
the only single complex-profile direction that both has zero whole defect
**and** vanishes at the first cutoff is the zero direction. Every nonzero
choice must retain/pay that boundary, or cancel it with other joined
directions. The determinant condition is explicit; no cofinal native
noncollinearity is asserted. This is not an impossibility theorem for
joined corrections or the arithmetic floor.

## Quantitative gate

The optional [probe](../scripts/probe_riesz_tangent_cubic.py) retains the
same two constructed prime pools, original finite masks and all cutoff
groups as the previous six-direction experiment. It checks 500 exact
rational cubic finite differences and 500 perpendicular-moment identities.
These regressions use rational model logs, not certified prime logarithms.

At seed 317, orders 256/640 and heights 54/65/100, adding the seventh
direction gives these **additional fractions of the remaining finite
rescaled price**:

| Order | Height 54 | Height 65 | Height 100 |
| --- | ---: | ---: | ---: |
| 256 | 0.00493% | 0.01199% | 0.06067% |
| 640 | 0.00311% | 0.00181% | 0.00198% |

The common coefficient box is four, and the original imaginary tilt is
fixed. The rational primal/dual replay also tests unrestricted real
coefficients **on the floating input matrices only**. It does not verify
the underlying primes, phases, logarithms or population coverage.
All six replayed duals have exactly zero directional correlations. Their
lower bounds retain at least `99939/100000` (99.939%) of the previous
six-direction finite price; the relative primal/dual gap is below
`1.94e-8`. Thus merely removing the coefficient box does not rescue these
six matrices. This is a finite-matrix gate, not a native or asymptotic
impossibility theorem.

These sparse inventories are not density samples or cofinal native
populations. They keep the early original count ceiling rather than the
eventual count crop. The common amplitude scale is not the native floor
budget. Earlier phase-control findings remain in force; no finite saving
percentage here is evidence of a special native arithmetic rate.

A preliminary order-1536 seven-direction floating solve returned an
unknown/infeasible solver status. It is an unsuccessful numerical solve,
not an arithmetic counterexample or a certified optimum. No order-1536
conclusion is used. The frozen successful report covers only 256/640.

The small gains and exact dual gate do not justify more coefficient
hunting as a route to the global floor. The useful result is a valid
count-three correction plus its explicit boundary restriction. The
actual joined signed cutoff correlations still need an independent
source-scale bound.

```bash
../.venv/bin/python scripts/probe_riesz_tangent_cubic.py --cost-audit
```

The probe is outside builds/CI. Strict target Lean/build, root-import
namespace lint and transitive axiom checks are recorded separately.
No commit, public endpoint, README/explorer change or wider gate is part
of this local slice.

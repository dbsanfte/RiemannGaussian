# Joint prime-profile bounds for the whole literal core

[`exists_core_joint_bounds`](../RiemannGaussian/ZetaRieszJointPrimeEnergy.lean)
proves both signed bounds for the **entire original `coreResponse`**.
The earlier interval-cover obligation is discharged for this estimate:
canonical largest-prime ownership counts every squarefree label exactly
once, and nonsquarefree coefficients vanish exactly. The numerical size of
the resulting cost is still open. See the
[proof and probe audit](riesz-joint-prime-energy-audit.json).

The [quadratic correction](zeta-riesz-quadratic-prime-energy.md) now gives
a provably no larger residual width for this same cost, retaining its
exact signed triple-prime correction and improving both enclosures by
intersection. The final whole-sum thresholds remain open.

## The bound keeps the full weights together

For a squarefree composite cofactor `n` and a prime `p` not dividing `n`, set

```math
f_p(d)=(L-\log d)_+-(L-\log p-\log d)_+,\qquad
D_n(f)=\sum_{d\mid n}\mu(d)f(d).
```

Let `T=log p+log n`, and retain the original assigned fraction `theta_N(pn)`.
Lean's `atom_eq` proves the actual residual coefficient times prime kernel
has real part `W(n,p) D_n(f_p)`, with

```math
W(n,p)=-\frac{(1-\theta_N(pn))e^{-T/2}T^{N+1}\cos(yT)}{L N!\,np}.
```

Thus **all factorial orders are already summed**. Neither an orderwise
triangle inequality nor separate prime/cofactor phase norms enter.
For each cofactor, the selected prime set `Q(n)` is arbitrary; multiply
`W(n,p)` by its exact indicator and the desired source scale. Holes,
moving endpoints and all original finite masks remain inside this weight.

Choose a finite real coordinate matrix `O` with

```math
\sum_a O_{ap}O_{aq}=\mathbf1_{p=q}.
```

Identity coordinates always satisfy this premise; it is finite algebra,
not a conjectural cancellation hypothesis. Put

```math
\widehat W_a(n)=\sum_pO_{ap}W(n,p),\qquad
\widehat f_a(d)=\sum_pO_{ap}f_p(d).
```

The signed pairing is unchanged. Using the already proved
[centered divisor energy](zeta-riesz-centered-prime-energy.md), one
unconditional constant `E>0` gives

```math
-\mathcal C\le J\le\mathcal C,\qquad
\mathcal C=\sum_a
\sqrt{EX\left(\sum_{n\in S}\widehat W_a(n)^2\right)
Q_X^\circ(\widehat f_a)}.
```

Cross terms are retained in **both** the cofactor weights and the prime
profiles. There is no binary maximal factor, separate factorial-order
sum, new count ceiling, prime-density replacement or zero hypothesis.
The arithmetic constant remains unevaluated. Cauchy–Schwarz still loses
correlation between a transformed weight and its actual divisor response;
the theorem does not assert that this loss is small at source scale.

## Literal coverage

`owner_labels_eq` proves that the rows obtained by deleting each label's
largest prime exhaust any finite squarefree support of count at least
three. `exists_whole_bounds` applies the inequality to that exact support.
`exists_partition_bounds` permits disjoint shells or count groups, adding
their own costs with the same `E` and no extra cardinality multiplier.

For `B=coreBand.filter Squarefree`, `core_eq_squarefree` is exact, and
`exists_core_joint_bounds` proves

```math
-\mathcal C_N\le u^{N+1}\operatorname{Re}(\mathrm{coreResponse}_N)
\le\mathcal C_N.
```

Every original core mask, its existing prime-count cutoff, all allocation
orders including zero and one, the physical length and the full phase are
retained. No row is completed and no companion credit is added again.
The cost can be evaluated with any admissible coordinates; choosing them
well is an optimization of a proved bound, not an assumption about zeta.

## Optional finite diagnostic

Run `OPENBLAS_NUM_THREADS=4 ../.venv/bin/python scripts/probe_riesz_joint_prime_energy.py`.
This is outside ordinary CI and is not a certificate. It uses actual
primes and squarefree cofactors, unique largest-prime ownership,
`N^2<p<exp(L)`, the `1.95N..2.03N` window, the nondominant `.65` mask,
original allocation and full product phase. As in the previous diagnostic,
these are finite test populations, not an enumeration of every nested
deletion defining the actual core.

The coordinate matrix diagonalizes the numerical centered-profile Gram
matrix. **Every column is retained**, including near-zero directions.
The energy is recomputed as a sum of squares, including the logarithmic
projection beyond the hinge support; no negative-eigenvalue truncation is
used to lower the cost. The script checks orthogonality and the direct
original-atom identity. Floating results are not proof certificates.

At `u=10001/20000`, `y=54`, on the same populations as the previous probe:

| N | Cofactor cap | Labels | Previous centered interval cost | Joint cost |
|---|---:|---:|---:|---:|
| 6 | 4,096 | 2,130 | 0.109178 | 0.00445451 |
| 8 | 65,536 | 285,908 | 0.107339 | 0.00270967 |
| 10 | 1,048,576 | 30,510,285 | 0.140558 | 0.00237545 |

All displayed costs are **before `sqrt(E)`**. The new separate-prime
identity-coordinate costs are `0.0151893`, `0.0254185`, `0.0375861`;
the common coordinate change accounts for a further substantial saving.
Requiring every cofactor prime to exceed `N^2` gives joint costs
`0.000658206`, `0.000704802`, `0.000586959` on smaller populations.

These comparisons do not prove that the new cost is uniformly smaller
than the old cost. Nor does the decrease at three finite orders prove an
eventual bound: the cofactor populations are truncated differently at
each order, and neither the omitted population nor `E` has been evaluated
numerically. There is no new numerical zero bound.

The `--expand-population` option increases the cap to
`floor(exp(2.03N)/(N^2+1))`, covering the full possible cofactor range for
the probe's owner primes above `N^2`. It still does not reproduce every
earlier arithmetic deletion defining the literal core. The enlarged tests
give:

| N | Expanded cofactor cap | Labels | Joint cost before `sqrt(E)` |
|---|---:|---:|---:|
| 6 | 5,266 | 2,198 | 0.00515549 |
| 8 | 173,791 | 306,148 | 0.00389738 |
| 10 | 6,484,203 | 32,709,252 | 0.00406861 |

The expanded order-ten cost **exceeds** order eight. Requiring every
cofactor prime to exceed `N^2` gives `0.000658206`, `0.000704802`,
`0.000707935`, respectively. These wider tests reinforce the need for an
actual large-order estimate; they establish neither decay nor a no-go.

## Remaining quantitative target

Coverage is now proved for the new joint cost. Its **total source-normalized
size** still needs an estimate exploiting the actual prime, cofactor and
radial correlations. Both final independent bounds, the
`-79/1000-o(1)` floor and the `3/2+o(1)` ceiling, remain open. Previous
central-sector growth audits remain relevant; uniformity over arbitrary
finite masks does not imply smallness for the actual carrier.

# A signed quadratic correction improves both whole-core bounds

[`exists_core_quadratic_bounds`](../RiemannGaussian/ZetaRieszQuadraticPrimeEnergy.lean)
proves a sharper enclosure for the **entire original source-scaled core**:

```math
\max(-B_0,H-K)\le J\le\min(B_0,H+K),\qquad K\le B_0.
```

Here `B0` is the [previous joint prime-profile cost](zeta-riesz-joint-prime-energy.md),
`H` is an exact signed arithmetic correction, and `K` is the smaller residual
cost. The comparison uses the **same** arithmetic constant, finite support,
coordinates and original weights. Consequently neither bound can worsen.
The eventual sizes needed for the final floor and ceiling remain open.
See the [proof and numerical audit](riesz-quadratic-prime-energy-audit.json).

The [known-moment refinement](zeta-riesz-conditioned-prime-energy.md)
further reduces the residual cost with this **same signed center**. It
deducts the known moment's squared correlation before taking the square
root, so both bounds can only improve again.

## The arithmetic identity that pays the correction

For a squarefree composite cofactor define

```math
M_2(n)=\sum_{d\mid n}\mu(d)(\log d)^2.
```

Lean proves `secondMoment_two_primes` and `secondMoment_eq_zero_of_count`:

```math
M_2(qr)=2\log q\log r\quad(q,r\text{ distinct primes}),\qquad
M_2(n)=0\quad(\omega(n)\ge3).
```

Thus every cofactor with at least three primes annihilates the quadratic
logarithmic profile, independently of its geometry, radial period, masks
and phase. The corresponding original labels have at least four primes.
The remaining two-prime cofactors are retained explicitly. They are not
discarded or assigned an unproved favorable sign.

## Keep every count together

Use the previous full signed weight `W(n,p)`, hinge `f_p`, and exact common
coordinates. Let `f_a` and `w_a` denote the resulting coordinate profiles
and weights. Write `Q_X` for the previous centered energy and `B_X` for
its associated bilinear form. Set

```math
g(d)=(\log d)^2,\qquad
\alpha_X(f)=\frac{B_X(f,g)}{Q_X(g)},\qquad
Q_X^{(2)}(f)=Q_X(f-\alpha_X(f)g).
```

The zero denominator case is included in the proof. The energy identity is

```math
Q_X^{(2)}(f)=Q_X(f)-\frac{B_X(f,g)^2}{Q_X(g)},\qquad
0\le Q_X^{(2)}(f)\le Q_X(f).
```

The exact divisor response and the resulting correction are

```math
D_n(f)=D_n(f-\alpha_X(f)g)+\alpha_X(f)M_2(n),
\qquad
H=\sum_a\alpha_X(f_a)\sum_n w_a(n)M_2(n).
```

Only two-prime cofactors contribute to `H`; after marking the owner prime,
these are triple-prime labels. The full count population remains together
in the residual cost

```math
K=\sum_a\sqrt{EX\left(\sum_n w_a(n)^2\right)Q_X^{(2)}(f_a)}.
```

`exists_joint_quadratic_bounds` obtains both `H-K <= J <= H+K` and the
previous `-B0 <= J <= B0` from one proved, **unevaluated** `E>0`.
Intersecting these intervals pays the signed correction honestly.
`exists_higher_count_bounds` gives `-K <= J <= K` automatically for
every population with at least three cofactor primes, with `K <= B0`.
There is no additional count ceiling or partition by prime count.

## Transfer to the original whole core

`exists_literal_quadratic_bounds` retains arbitrary cofactor-dependent
prime rows, including holes, the original allocation, full product phase,
both Riesz cutoffs and every factorial order, including zero and one.
`exists_whole_quadratic_bounds` uses canonical largest-prime ownership.
`exists_core_quadratic_bounds` applies it to the entire original core,
whose nonsquarefree coefficients vanish exactly.

This is an independent arithmetic inequality: it assumes no zeta zero,
simple source, prime-density approximation or completion estimate.
No previous companion credit is spent again. The old whole-core cover
obligation is discharged for this cost, but its total source-normalized
size still needs proof.

## Optional numerical diagnostic

Run `OPENBLAS_NUM_THREADS=4 ../.venv/bin/python scripts/probe_riesz_quadratic_prime_energy.py`.
Add `--expand-population` for the enlarged cofactor range. The calculation
uses the same actual-prime test populations and masks as the previous
joint-energy diagnostic, not every nested deletion defining the core.
It checks the original atom identity, the second divisor moment and
orthogonality, retaining **all** coordinate columns. Exterior projection
cross terms remain in the residual energy. These floating calculations
are optional and never run as a CI certificate.

At `u=10001/20000`, `y=54`, on the earlier truncated populations:

| N | Labels | Previous width | Quadratic width | Signed center H |
|---|---:|---:|---:|---:|
| 6 | 2,130 | 0.00445451 | 0.00335172 | +0.0000415995 |
| 8 | 285,908 | 0.00270967 | 0.00225175 | +0.0000574266 |
| 10 | 30,510,285 | 0.00237545 | 0.00216003 | -0.0000540593 |

Widths are **before `sqrt(E)`**; `H` is the actual signed center on the
test population. Its sign changes. The observed width reductions of
approximately 25%, 17% and 9% do not establish an eventual rate. Unlike
the preceding numerical comparison between different methods, the
no-larger-width comparison here is a Lean theorem for every valid finite
population with the same coordinates and `E`.

Expanding the cofactor cap to `floor(exp(2.03N)/(N^2+1))` gives:

| N | Labels | Previous width | Quadratic width |
|---|---:|---:|---:|
| 6 | 2,198 | 0.00515549 | 0.00393978 |
| 8 | 306,148 | 0.00389738 | 0.00336144 |
| 10 | 32,709,252 | 0.00406861 | 0.00381798 |

The signed centers are unchanged in these three enlarged tests. The
order-ten width exceeds order eight, even after the correction. Requiring
every cofactor prime to exceed `N^2` gives smaller widths `0.000492847`,
`0.000575931`, `0.000643942`; those too do not demonstrate decay. These
are finite diagnostics, not a proof of growth or an asymptotic obstruction.

## Remaining joint estimate

The target is the combined floor or ceiling, not separate norm decay of
every term. It suffices to control the appropriate endpoint of the
intersected enclosure. Neither the signed triple correction nor the
remaining total cost has the required eventual bound. The final
`-79/1000-o(1)` floor and `3/2+o(1)` ceiling remain open; no new zero
exclusion or RH conclusion follows from this slice.

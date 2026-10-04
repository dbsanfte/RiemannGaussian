# Positive-density test of the retained factorial quadratic

Positivity, a common phase, and adjacent factorial-order coupling do not
prohibit the negative unit moment source. This slice proves that statement
for an explicit continuous density and independently replays its full
four-term quadratic. It supplies **no arithmetic floor saving**. The
independent cofinal `399/5000` bound on the actual ordinary-prime carrier
remains open, as does the multiple-zero ceiling.

The local leaf is
[`ZetaRieszPositiveDensityAudit.lean`](../RiemannGaussian/ZetaRieszPositiveDensityAudit.lean).
It is a negative audit of a proposed generic moment method. The density is
not the ordinary-prime measure, and no transport from it to primes is used.

## The exact continuous model

At `u=10001/20000`, put `beta=3/2-u=99995/100000`. On `T>=20000`, use

```math
\nu(T)=\frac{e^T-2e^{\beta T}\cos(yT)}T.
```

`density_ceiling_pos` proves this density strictly positive, for every
height. `relative_density_abs_le` proves

```math
\left|\frac{T\nu(T)}{e^T}-1\right|
\le 2e^{-T/20000}.
```

The same full phase `exp(-(3/2+i*y)*T)` is used on every factorial leg.
For logged order `n=k-1`, including `n=0`, define

```math
B_k=\frac{u^k}{(k-1)!}
     \int_{20000}^\infty T^k e^{-(3/2+iy)T}\nu(T)\,dT.
```

`density_phase_eq` and `densityMoment_eq_channels` prove the exact identity

```math
B_k=W_k(1/2+iy)-W_k(u)-W_k(u+2iy),\qquad
W_k(z)=\frac{u^k}{(k-1)!}\int_{20000}^\infty T^{k-1}e^{-zT}\,dT.
```

All integrals are proved integrable. `tailLeg_eq_complete_sub_head`
retains the threshold exactly. The removed finite-log head has the bound

```math
\left|u^{n+1}\int_0^B\frac{T^n}{n!}e^{-zT}\,dT\right|
\le uB\frac{(uB)^n}{n!}\longrightarrow0
\quad (\Re z\ge0).
```

Consequently `density_ceiling_moment_tendsto` proves `B_k -> -1` for
every fixed `abs(y)>=1`. No exposed zero, independent-leg substitution,
low-order deletion, or hard share projection enters this theorem.

This is the precise formal conclusion: these generic density/moment
properties allow the obstructive unit source. A cofinal counterexample
for the quadratic itself is **not** formalized by this leaf.

## Full signed numerical test

[`probe_riesz_pair_positive_density.py`](../scripts/probe_riesz_pair_positive_density.py)
evaluates the same density through its exact incomplete-Gamma recurrence:

```math
W_{k+1}(z)=\frac uz\left(W_k(z)
             +e^{-zB}\frac{(uB)^k}{k!}\right).
```

It retains the central band, successor band, logged prefix and complete
Selberg trace together, with their original signs. It does not substitute
`B_k=-1` at finite orders. All reported orders exceed 65536. The model
heights `55,101,10000` are regression parameters, not claimed zero
ordinates or evidence about the currently unresolved height range.

The moving length is kept in the literal enclosure

```math
L_0=-2N\log u-2\log(N+1),\qquad
L_0\le L_N\le L_0+4(N+1)u^N.
```

For orders through 425984 this is also checked against the exact integer
floor defining `L_N`. At larger orders the enclosure avoids constructing
huge integers. The displayed coefficient values use `L_0`; their
negligible enclosure width is reported separately. This is numerical
replay, not an interval certificate.

Representative real values at height 55 are:

| Native order N | Source-scaled model quadratic |
| ---: | ---: |
| 90112 | 0.0274005467 |
| 1966080 | 0.0770411718 |
| 83886080 | 0.0798049399 |
| 176160768 | 0.0798399498 |

The first sampled crossing of `0.0798` is `N=83886080`. The pure selected
formula approaches `0.079871797...`; the positive-density model is
numerically consistent with that same limit. This delayed crossing warns
against extrapolating finite-order success. Neither value is an observed
actual-prime sum or a measured remaining error.

The sparse replay keeps every low-order perturbation up to 30003. Its
omitted L1 tail includes both new Poisson forcing **and the homogeneous
memory of the two complex recurrences**. The worst logged tail bound is
less than `-1090`, not the much smaller forcing-only bound. A loose
`100*(N+2)^3` propagation leaves the model tail negligible. These numerical
tail bounds do not pay any arithmetic carrier sector.

[`check_riesz_pair_positive_density.py`](../scripts/check_riesz_pair_positive_density.py)
imports no producer and uses an independent 110-digit recurrence and
four-component reconstruction. Across 33 cases the maximum replay
difference is below `2.2e-17`; full-array binary64 regressions through
425984 differ from the sparse replay by less than `3.2e-16`.

## Consequence for the next attack

The genuine joined-square payment from the preceding slice remains valid.
This audit adds no floor credit to it. An argument using only positivity,
small relative density errors and factorial coupling is insufficient to
exclude this model's coherent source. The next signed estimate must use
additional constraints of the actual ordinary-prime measure, with their
quantitative strength proved for the full quadratic. No claim is made
that discreteness alone supplies those constraints.

Focused build, namespace lint, complete leaf axiom audit and independent
replay are pinned in
[`riesz-positive-density-audit.json`](riesz-positive-density-audit.json).
All work remains local; the optional probes are outside ordinary CI.
There is no root registration, broader gate, commit or push.

# Cofactor phase cancellation in the whole signed bound

The [Lean theorem](../RiemannGaussian/ZetaRieszCofactorPhaseEnergy.lean)
improves the point at which the original phase information is squared.
It gives **both signed bounds for the literal whole core**, without an
unevaluated arithmetic multiplier in the new cost. The
[proof audit](riesz-cofactor-phase-energy-audit.json) records validation.

## The inequality

Keep the existing common prime coordinates. In coordinate `a`, let `w_a(n)`
be the original source-normalized cofactor weight, including the product
cosine, every prime-row hole and the full factorial allocation. Let `f_a(d)`
be the combined prime-hinge profile, optionally centered by the existing
exact affine-log null moment. Define

```math
T_a(k)=\sum_{n\in S}w_a(n)
              \sum_{\substack{d\mid n\\d\le k}}\mu(d),
\qquad
Q_a=\sum_{\substack{1\le k\le X\\\Delta f_a(k)\ne0}}
                   \frac{T_a(k)^2}{k},
\qquad
V_a=\sum_{k=1}^{X}k\,\Delta f_a(k)^2.
```

Finite summation by parts followed by weighted Cauchy–Schwarz proves

```math
-\sum_a\sqrt{Q_aV_a}
\ \le\ u^{N+1}\operatorname{Re}(\mathrm{coreResponse})
\ \le\ \sum_a\sqrt{Q_aV_a}.
```

The cofactor sum in `T_a(k)` is **signed before squaring**. Previously the
cofactor allowance was `E X sum_n w_a(n)^2`; that bound removed its
cross-cofactor phase information. Finite duality now proves

```math
Q_a\le E X\sum_{n\in S}w_a(n)^2
```

for one universal mean constant. Thus the new centered cost cannot exceed
the earlier joint cost with that same budget. The new cost itself does not
contain `E`. Its finite correlations still require numerical certification
or analytic estimation; removing `E` does not evaluate them.

All original labels, counts, physical cutoffs, allocation and factorial
orders remain. The finite cutoff endpoint and the affine-log correction
are discharged exactly. The partition theorem also permits the original
disjoint cofactor shells. The final theorem intersects this enclosure with
the preceding large-order radial bound, paying its outer error only on
that radial branch. No prime-density substitution or completion is used.

## Numerical test and its limits

The optional [probe](../scripts/probe_riesz_cofactor_phase_energy.py) keeps
actual primes and squarefree cofactors in the contracted `1.971..2.029`
window. The [recorded results](riesz-cofactor-phase-energy-probe.json), at
`u=0.50005` and `y=54`, are:

| Order | Previous cost before `sqrt(E)` | New cost, shells separate | New cost, shells joined |
| ---: | ---: | ---: | ---: |
| 6 | 0.00424988 | 0.000289527 | 0.000188646 |
| 8 | 0.00307535 | 0.0000865465 | 0.0000483281 |
| 10 | 0.00340097 | 0.000346940 | 0.0000298383 |

The last column sums every cofactor shell into the SAME cutoff correlation
before squaring, using one common complete coordinate basis. The whole-support
theorem already permits this. At order 10 the signed sum is unchanged,
approximately `0.0000101248`, while joining the shells removes substantial
additional cost. This is direct evidence of cross-shell phase cancellation
in the finite test population, not a new representation of the carrier.

Every coordinate is retained. The new diagnostic conservatively includes
all cutoffs up to the last possible profile change. Its new cost needs no
mean multiplier. These are floating diagnostics, **not certificates**.

The test populations omit earlier nested core deletions. Cancellation in an
enlarged signed population does **not** bound an arbitrarily masked subset;
the theorem, unlike these exploratory populations, retains all masks.
In fact the entire tested window at orders 6, 8 and 10 is above the original
physical annulus `n < X_N^2`. Its upper logarithmic endpoints divided by `N`
are approximately `1.59860`, `1.70060` and `1.81732`, all below the test's
lower endpoint `1.971`. These probes therefore give **no numerical bound on
a nonempty literal core**. They diagnose which finite summations lose phase
information; their small costs cannot be used as endgame margins.
The joined costs decrease at the tested orders; the separate-shell costs
do not. Neither observation proves an asymptotic rate. The moving Riesz
length at these small orders is also far from its limiting slope. There is
no evaluated eventual starting order or new zero exclusion.

The remaining target is a large-order bound on the literal signed
`T_a(k)` correlations, strong enough for the `-79/1000` floor and `3/2`
ceiling. Neither threshold is closed. The previous exponential-growth,
prime-density-transfer and completion audits remain in force.

To reproduce the optional diagnostic (excluded from ordinary CI):

```sh
OPENBLAS_NUM_THREADS=1 ../.venv/bin/python scripts/probe_riesz_cofactor_phase_energy.py --max-order 10 --heights 54 --join-cofactor-shells
```

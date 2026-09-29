# A cubic divisor cancellation lowers the joint arithmetic cost

[`exists_core_cubic_bounds`](../RiemannGaussian/ZetaRieszCubicPrimeEnergy.lean)
proves both signed inequalities for the entire original core, using a
further reduced energy and retaining its exact signed correction. See the
[compiled-scope audit](riesz-cubic-prime-energy-audit.json).

Put `M3(n)=sum_{d|n} mu(d) log(d)^3`. For a prime `p` coprime to a
squarefree composite `n`, Lean proves the exact insertion formula

```math
M_3(pn)=-3\log(p)M_2(n).
```

Thus every squarefree cofactor with at least four primes has `M3=0`.
Every such cofactor also has `M2=0`. This applies to **all** original
labels of count at least five, regardless of prime shares, phase or period;
there is no maximum count.

After the preceding quadratic projection, let `g3` be the residual
`log³` direction, and project the full prime profile onto it. Lean proves

```math
Q_3(f)=Q_2(f)-\frac{\langle f_2,g_3\rangle^2}{Q(g_3)}
\le Q_2(f).
```

All zero-energy cases are included. The exact arithmetic correction is

```math
D_n(g_3)=M_3(n)-\alpha_X(\log^3)M_2(n).
```

It stays inside the signed center `H3`, together with the previous center
`H2`. Only original triple and quadruple labels can contribute to that
center. They are not discarded or replaced by favorable signs.

With all original weights, phases, masks, allocation and factorial orders
retained, the entire core satisfies

```math
\max(H_2-C_2,H_3-C_3)\le J\le\min(H_2+C_2,H_3+C_3),
\qquad C_3\le C_2.
```

The same unevaluated arithmetic constant `E` appears in both costs.
The width comparison concerns the quadratic cost; it does not assert
automatic dominance over the separate conditioned cost. All previously
proved bounds remain available.

On the same enlarged order-ten population of **32,709,252 labels**, the
optional cubic probe gives:

| Profile and coordinates | Cost before `sqrt(E)` | Signed center |
|---|---:|---:|
| Quadratic, previous basis | 0.003817977 | -0.0000540593 |
| Cubic, same basis | 0.003005275 | +0.0001130173 |
| Cubic, rational recipe from identity | 0.002602547 | +0.0001130173 |

Both the width and the center must be used when comparing endpoints.
These are floating diagnostics, not certificates. Every coordinate and
the full exterior profile energy are retained. The test omits earlier
nested core deletions and does not evaluate `E`.

Reproduce outside CI:

```sh
OPENBLAS_NUM_THREADS=4 ../.venv/bin/python \
  scripts/probe_riesz_cubic_prime_energy.py \
  --output /tmp/riesz-cubic-coordinate-audit.json
```

The [large-order edge payment](zeta-riesz-large-order-core.md) independently
removes two further radial strips. The central signed correction and
remaining cost still need an eventual estimate. Neither the whole
`-79/1000` floor, the `3/2` ceiling, nor a new zero exclusion is proved.

# Reflected large primes sharpen the literal signed costs

The [Lean proof](../RiemannGaussian/ZetaRieszReflectedPrimeBounds.lean)
uses the actual reflected cutoff to improve both coefficient signs on the
unpaid interior. It retains the original integer label, complex phase,
factorial kernel, allocation fraction and every core mask. No signed
supply is spent, no prime-density model is used, and no zero hypothesis
enters the estimates.

Write `T=log n`, `D=T-L`, `k=omega(n)`, and let `o` be the number of prime
factors satisfying **`log p>=D`**, including equality. These are reflected
large primes, not the separate physical threshold `p>N^2`.

In units `(T/L)*log(minFac n)`, the following intervals are proved:

| Prime count | Previous interval | One reflected large prime | Two reflected large primes |
| ---: | ---: | ---: | ---: |
| 7 | [-5,10] | **[-4,6]** | **[-3,3]** |
| 8 | [-15,13] | **[-10,10]** | **[-6,4]** |
| 9 | [-35,27] | **[-20,15]** | **[-10,10]** |
| 10 | [-49,56] | **[-35,35]** | **[-15,20]** |

The count-dependent theorem covers every higher count, not just these
four rows. `activeCapacity_table` checks the displayed integers. The new
allowance is intersected with the previous even/odd interval, so neither
signed charge increases. Counts below seven remain unchanged in the
terminal comparison, preserving their stronger earlier estimates.

There is also an exact deletion: on the literal core, **every label with
at least five prime factors and three reflected large primes has zero
coefficient**. This is cancellation within the original divisor sum,
not decay or an allowance paid by another population.

## Why the active count is smaller

Factor the squarefree label as `n=b*a`, where `b` contains the prime factors
with `log p>=D`, and `a` contains all remaining prime factors. The existing
exact prime-insertion identity gives

\[
R_D(n)=R_D(a).
\]

Any divisor involving a prime of `b` has zero truncated hinge, including
the cutoff endpoint. Reflection then gives the original coefficient

\[
c_L(n)=-\frac TL(-1)^k R_D(a).
\]

The parity here is **the original count `k`**, not the active count `k-o`.
The ordinary prime factors in `b` still belong to `n`, its phase and its
allocation. The proof does not complete or average a prime incidence.

Let `E_j,O_j` be the previously proved largest even/odd binomial-layer
capacities. When `a` has at least two prime factors, the signed divisor
bound applied to this actual cofactor is

\[
-O_{k-o-2}\log p_{\min}\le R_D(a)
\le E_{k-o-2}\log p_{\min}.
\]

`activePart_minFac` proves that the least prime is unchanged. Therefore
the coefficient capacities are `(E,O)` for even `k` and `(O,E)` for odd
`k`, at the smaller index `k-o-2`. This accounts for both signs in the table.

The core supplies `D>7T/25>T/4`, with the moving `L_N` retained. Four
reflected large primes cannot fit in the logarithmic budget. Thus `o<=3`
and, for `k>=5`, the active cofactor has at least two prime factors.
If `o=3`,

\[
\log a\le T-3D<D.
\]

The active composite is fully saturated. Its complete Möbius mass and
first logarithmic moment both cancel, so `R_D(a)=0` exactly.

## Connection to the same signed carrier

`core_sum_eq_outer_filter` removes this zero sector from **any subset**
of the original core, preserving its full complex sum. In particular,
`nonzero_core_outer_le_two` applies to any unpaid high-count label in an
earlier ledger. This does not require a new carrier definition.

`eventually_core_subset_bounds` transfers the improved coefficient interval
to both source-normalized signed comparisons. It keeps the observed
cosine, the original nonnegative factorial/allocation weight, every
favorable selected observation, and all other counts exactly. The theorem
holds for every selected core subset, all heights and count ceilings, on
`1/2<u<=10001/20000`. The quarter-cutoff deletion itself holds from `N>=2`;
the complementary one-third condition used with earlier bounds is eventual.

The earlier [seven-prime head payment](zeta-riesz-seven-prime-head.md),
[count-tail payment](zeta-riesz-log-count-tail.md), all signed credits and
their spending restrictions remain available. These pointwise savings are
not additional additive credits.

The independently required whole-sum bounds remain open: the
[multiplicity-aware endgame](zeta-riesz-joint-floor.md) requires a cofinal
`-79/1000-o(1)` floor for simple zeros and a cofinal `3/2+o(1)` ceiling for
multiple zeros. Neither follows from the coefficient table. In particular,
terms with zero, one or two reflected large primes still need joint signed
control, and none of the percentage coefficient savings is a certified
percentage reduction of the whole carrier.

## Optional quantitative regression

The [probe](../scripts/probe_riesz_reflected_primes.py) and its
[recorded output](riesz-reflected-primes-probe.json) use exact rational
weights modeling prime logarithms. They verify the removal identity and
display the resulting intervals on deterministic samples. These are not
actual prime labels, certified extrema, prime densities or source bounds.
The probe stays outside ordinary CI.

```sh
../.venv/bin/python scripts/probe_riesz_reflected_primes.py
```

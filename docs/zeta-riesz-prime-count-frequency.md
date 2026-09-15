# Prime-count savings on the natural frequency scale

Lean now pays the full arithmetic cost of a growing-prime-count part of the
retained signed sum on its natural `1/N` frequency window. The earlier
[all-count estimate](zeta-riesz-frequency-decay.md) required an additional
geometric contraction of that window. The new estimate keeps the natural
window and selects integers with sufficiently many distinct prime factors.
**The complete signed lower bound and a zero-free theorem from this path
remain open.**

The independent endpoint is
[`tendsto_manyPrimeLowResponse_dyadic_moving`](../RiemannGaussian/ZetaRieszPrimeCountFrequency.lean).
The [supporting explorer](https://dbsanfte.github.io/RiemannGaussian/rh-proof/?endpoint=prime-count-frequency-decay)
links its compiled dependencies and axiom audit after publication.

A [stronger continuation](zeta-riesz-whole-prime-count-decay.md) now pays
the complete many-prime integer class, including its other frequencies,
and retains separate bounds for enlarged frequency prefixes. The joint
lower-count contribution and tapered wing remain open.

## What prime-count information saves

Use the original signed products `Q_n` and `P_n` from the
[frequency identity](zeta-riesz-signed-frequency.md). For squarefree `n`
with `k` distinct prime factors, their logarithms sum exactly to `log n`.
The arithmetic-geometric mean inequality therefore gives

```math
\prod_{p\mid n}\log p\le\left(\frac{\log n}{k}\right)^k,
\qquad
|Q_n(\xi)|\le\left(\frac{|\xi|\log n}{k}\right)^k.
```

Keeping every denominator, Lean proves for `k >= 4`

```math
\left|\frac{P_n(L,\xi)}{\xi^2}\right|
 \le\frac{2|\xi|^2(\log n)^4}{k^k},
 \qquad |\xi|\log n\le1.
```

The full prime count was absent from the earlier bound. This estimate uses
the vanishing divisor factors before bounding the remaining complex
observations. It does not establish cancellation between different
integers. AM-GM is standard mathematics; no historical novelty is claimed.

A separate count-sensitive estimate gives
`2 |xi|^2 (log(n)/k)^4` throughout `|xi| log(n) <= k`. On the actual
higher-prime support this allows four times the earlier frequency window
and improves the cubic allowance's coefficient by at least `4^4 = 256`.
That coefficient comparison alone does not pay the growing arithmetic cost.

## The complete arithmetic bound

Let `F_{>=K,N}` be `manyPrimeFrequency`: the original `centralUnpairedBand`
restricted to `k >= K`, with the original squarefree, nonunit and nonprime
filters, common physical length, height phase and polynomial factorial
filter. Write

```math
\delta_N=\frac{3}{8(N+1)},\qquad
E_{N,K}=\frac{u^{N+1}}{2\pi}
       \int_0^{\delta_N}F_{\ge K,N}(\xi)\,d\xi.
```

For **every** `K >= 4`, `0 <= u <= U`, `0 < q < 1/2`, height `y` and
fixed polynomial `P`, `norm_manyPrimeLowResponse_le` proves

```math
|E_{N,K}|\le
\frac{18U}{\pi}\,\mathrm{frequencyTiltMass}(P,q)
 \frac{(N+1)^2(U/q)^N}{K^K}.
```

The constant includes the whole factorial filter and genuinely summable
positive integer envelope at exponent `3/2-q > 1`. It is independent of
the height, order and tested radius in `[0,U]`. No arithmetic premise is
left inside this bound.

For the explicit sequences

```math
K_j=2^{j+3},\qquad N_j=8(j+4)K_j,
\qquad K_j^{K_j}\ge\left(\frac{17}{16}\right)^{N_j},
```

Lean proves `N_j` tends to infinity and obtains

```math
|E_{N_j,K_j}|\le
\frac{18U}{\pi}\,\mathrm{frequencyTiltMass}(P,q)
(N_j+1)^2\left(\frac{16U}{17q}\right)^{N_j}.
```

Every `0 < U < 17/32` admits `16U/17 < q < 1/2`, so the bound tends to
zero. The theorem allows arbitrary moving heights `y_j` and arbitrary
moving radii `u_j` in `[0,U]`. The frequency window is genuinely the
natural `3/(8(N_j+1))`, without geometric contraction. The count threshold
grows with the order; this does not pay the fixed three-prime class or all
of the higher-prime class. No proportion of the original carrier has been
certified, and this schedule is not claimed optimal.

## Exactly what remains

`nonlinearFrequency_eq_few_add_many` partitions the original frequency
carrier without losing signs. After deleting `E_{N,K}`, the nonlinear
response is exactly the sum of

```math
\frac{u^{N+1}}{2\pi}
\left(\int_0^\infty F_{3\le k<K,N}(\xi)\,d\xi
      +\int_{\delta_N}^\infty F_{k\ge K,N}(\xi)\,d\xi\right).
```

All integrals have genuine integrability proofs. No endpoint term is
omitted. Adding the original tapered wing gives three explicit unpaid
pieces:

| Component | Remaining obligation |
| --- | --- |
| Integers with `3 <= k < K_j` | Their full signed frequency integral |
| Integers with `k >= K_j` | Their coupled frequencies above `delta_(N_j)` |
| Tapered wing `V_(N_j)` | Its signed contribution and correlations with the two integrals |

`tendsto_count_reduced_source` proves that their sum, with the original
normalization, still tends to `-m + m^2 c(u)` under the original exposed
right-half-zero hypotheses and `u < exp(-2/3)`. Here `m` is the full
analytic multiplicity and `c(u)` is the existing paid harmonic cost.
Lean checks `exp(-2/3) < 17/32`, so the new component decay covers that
entire original source range. It does **not** widen the source range or
give a zero-free strip with boundary derived from `17/32`.

The previous all-count shrinking-sector deletion and this count-selected
deletion overlap. Both theorems remain valid, but their errors cannot be
added as though they deleted disjoint pieces. A combined reduction requires
its own exact partition and estimate.

## Validation

The module belongs to the ordinary root. Warning-as-error compilation,
ordinary-root declaration lint and complete transitive axiom audits check
all 35 declarations. Only `propext`, `Classical.choice` and `Quot.sound`
are permitted. The optional exhaustive numerical certificate is not run.
The default whole-carrier endpoint, proved zero-free region and numerical
certificate are unchanged.

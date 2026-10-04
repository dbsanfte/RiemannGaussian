# Joined central-order saving for the ceiling

The ceiling **42/25 = 1.68 remains open**. This local slice proves a global
upper inequality for the existing `joinedPhysical`, with an **81.8 percent
reduction in the central coefficient price**. That percentage concerns the
two central factorial sums, not the whole ceiling gap. It supplies no new
zero exclusion or bound on the still-signed outer aggregate.

The proof is in
[ZetaRieszCeilingOrderCancellation.lean](../RiemannGaussian/ZetaRieszCeilingOrderCancellation.lean).
It uses the old independently paid mask, period, count, diagonal and physical
bridges. No new arithmetic carrier, prime-density transport or factorial
allocation restriction is introduced.

## Keep the Selberg trace joined at every multiplicity

Write

```math
a_k=u^{k+1}\sum_p\frac{(\log p)^{k+1}}{k!}p^{-3/2-iy},\quad
K=\lfloor13N/32\rfloor,\quad \lambda_N=\frac{N+1}{uL_N}.
```

The complete Selberg term is `-a_N` minus the full convolution trace,
plus its one prime-square diagonal. The trace cancels **exactly** against
the trace in the already joined prime-pair expression. This works at every
analytic multiplicity; it does not assert that the Selberg term tends to
zero at a multiple zero.

After the existing geometric payments, the upper target is therefore

```math
\operatorname{Re}\left[
a_N-\sum_{k=K+1}^{N-K}\frac{a_{k-1}a_{N-k}}{N+1-k}
 +\lambda_N\sum_{k=1}^{N+1-K}\frac{a_{k-1}a_{N+1-k}}{N+2-k}
\right].
```

The ordinary-prime term is signed. The lower orders and the last endpoint
are retained. No simple-zero assumption enters this reduction.

## Join adjacent orders before pricing the central sum

For a common central order, put `d=N+1-k`. The exact identity is

```math
-\frac{a_{k-1}a_{N-k}}d
 +\lambda_N\frac{a_{k-1}a_{N+1-k}}{d+1}
=\left(\frac{\lambda_N}{d+1}-\frac1d\right)a_{k-1}a_{N-k}
 +\frac{\lambda_N}{d+1}a_{k-1}(a_{N+1-k}-a_{N-k}).
```

The second term is essential: different factorial orders are not equated.
The remaining prefix orders are exactly
`{1,...,K} ∪ {N+1-K}`. In particular, logged order zero and the upper
endpoint remain in the signed exterior sum.

The literal moving-length estimates give `1≤lambda_N≤13/9` for
`N≥65536`, uniformly on `1/2≤u≤10001/20000`. Since `d≥3`, Lean proves

```math
\left|\frac{\lambda_N}{d+1}-\frac1d\right|
\le\frac2{11}\left(\frac{\lambda_N}{d+1}+\frac1d\right).
```

This is a coefficient inequality, not an assumed contraction of prime
phases. It applies to all central orders at once.

`central_adjacent_signed_upper` gives the stronger version retaining the
real part of the combined central sum itself. The optional `2/11` price is
used by `eventually_joinedPhysical_ceiling`:

```math
\begin{aligned}
\operatorname{Re}[u^{N+1}\operatorname{joinedPhysical}_N]
\le{}&\operatorname{Re}a_N+\frac2{11}\mathsf P_N
 +\lambda_N\operatorname{Re}
   \sum_{k\in\mathsf X_N}\frac{a_{k-1}a_{N+1-k}}{N+2-k}
 +\lambda_N\mathsf D_N+\varepsilon_N,\\
\mathsf P_N={}&\sum_{k=K+1}^{N-K}
 \left(\frac{\lambda_N}{N+2-k}+\frac1{N+1-k}\right)
 |a_{k-1}a_{N-k}|,\\
\mathsf D_N={}&\sum_{k=K+1}^{N-K}
 \frac{|a_{k-1}|\,|a_{N+1-k}-a_{N-k}|}{N+2-k},\\
\mathsf X_N={}&\{1,\ldots,K\}\cup\{N+1-K\},\qquad \varepsilon_N\longrightarrow0.
\end{aligned}
```

The error limit is independent of a zero hypothesis and retains all the
original masks via their checked geometric bounds. For any convergent
array, `centralStepMass_tendsto` also proves `D_N→0`, with every low order
retained. This latter payment may use the exposed source convergence at
arbitrary multiplicity; it does not remove that source from the main sum.

## Quantitative regression and its limitation

The optional detector first checks exact rational coefficient identities,
then replays finite genuine-prime sums with their complete phases, swapped
incidences and one diagonal. An independent checker reconstructs the old
four-slot expression and its Selberg trace, rather than calling the producer.
The numerical replays are below the formal native threshold and do not
sample a complete carrier population.

For a **synthetic selected constant array** `a_k=-2`, at the radius ceiling
and `N=262144`, the separate central price is approximately `3.70813`,
while the exact joined price is approximately `0.672229`. Thus the exact
central collection removes approximately `3.03591` from that separate
price. These are model price comparisons, not measured arithmetic reserves.

The same regression prevents an overclaim: the exact source evaluation
still tends to approximately **1.680512812**, exceeding `1.68`. Perfect
adjacent-order cancellation alone cannot close the multiple-zero endpoint.
The `2/11` inequality is a real global central saving, but not a certified
fraction of progress on the final contradiction margin.

The next unpaid estimate is the **joint real contribution of the
ordinary-prime term, the combined central products and the exterior prefix**.
Those terms must stay signed; separately norming them reintroduces the
previous divergent allowance. No new credit is supplied by any already
vanishing boundary payment.

## Optional local validation

```sh
/home/dbsanfte/.elan/bin/lake env lean \
  -o .lake/build/lib/lean/RiemannGaussian/ZetaRieszCeilingOrderCancellation.olean \
  RiemannGaussian/ZetaRieszCeilingOrderCancellation.lean
/home/dbsanfte/.elan/bin/lake env lean scripts/CheckRieszCeilingOrderCancellation.lean
../.venv/bin/python scripts/probe_riesz_ceiling_order_cancellation.py \
  --output .lake/riesz-ceiling-order-cancellation/probe.json
../.venv/bin/python scripts/check_riesz_ceiling_order_cancellation.py \
  .lake/riesz-ceiling-order-cancellation/probe.json \
  --output .lake/riesz-ceiling-order-cancellation/validation.json
```

The scoped audit records the leaf build, 14 namespace linters, transitive
standard-axiom check, exact rational regressions and independent finite
replay. This work remains local; there is no root registration, commit,
push, wider gate or routine CI probe.

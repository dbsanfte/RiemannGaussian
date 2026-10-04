# Geometric payment after exact factorial cancellation

The [Lean module](../RiemannGaussian/ZetaRieszPairLowOrderPayment.lean) gives
an independent whole-population payment for an actual piece of the current
signed pair carrier. It uses the factorial indices exposed by
`ZetaRieszPairPrefixConvolution`, rather than a new completed prime sum.
The independent `0.0798` bound for the remaining signed main is **open**.

## Exact piece and support

Put `M=N+1`, `K=floor(13N/32)` and `H=floor(17N/64)+1`. The endpoint
cancellation leaves the logged factorial sum over `1<=k<=K`. For every
literal pair `n=pq`, the exact first `H` terms are

$$
-\frac{M}{L}\sum_{k=1}^{H} k\left[K_k(s,p)K_{N+2-k}(s,q)
+K_k(s,q)K_{N+2-k}(s,p)\right]
=b_N(\log p,\log q)K_N(s,pq),
$$

where, writing `T=x+z`,

$$
b_N(x,z)=-\frac{T}{L}\left[xF_{N+1,H-1}(x/T)
+zF_{N+1,H-1}(z/T)\right],\qquad
F_{M,h}(v)=\sum_{k=0}^{h}\binom Mk v^k(1-v)^{M-k}.
$$

`low_logged_atom_eq` proves this equality, including both swapped
incidences and the full complex phase. `lowOrders_subset` proves these are
existing logged orders for `N>=8`. No order-zero atom is discarded.

The payment includes exactly the original nonprime complete-period labels
for which `log(largestPrime n)<=L_N`, retaining all original flags on those
labels. This is a subpiece of the original carrier; its complementary
labels are not dropped. Pairs whose largest prime exceeds `L_N` remain explicit;
they are not completed, removed or priced by this theorem.

## Proved quantitative saving

On the original contracted core, `T>=1971N/1000`. The existing bound
`L_N<=139N/100` implies that both prime-log shares on the selected physical
pairs are at least `7/24`. The exact tilt `11/10` then proves

$$
F_{N+1,\lfloor17N/64\rfloor}(v)\le e^{-N/1000},
\qquad 7/24\le v\le1.
$$

Thus `|b_N|<=2T e^{-N/1000}`. Summing this independently small coefficient
with the existing integer factorial mass, without any prime-density or zero
hypothesis, gives

$$
\boxed{\|\mathrm{lowLoggedPacket}(u,y,N)\|
\le8e^2(N+1)e^{-N/1250}.}
$$

Here the packet already includes `u^(N+1)`, and the hypotheses are
`N>=65536`, `1/2<=u<=10001/20000`, `54<=|y|`. The source growth
`log(2u)<1/10000` is strictly smaller than the proved factorial saving.
The bound is about `6.59e-17` at `N=65536` and `2.62e-25` at native order
`N=90112`. These are costs of the removed piece, **not** bounds on the main.

This does not conflict with the earlier shrinking-share low-order no-go:
the present distinct-prime physical population has a fixed positive share
gap. No such gap was available for every factor at growing prime count.

## Original floor ledger

`eventually_native_sub_low_floor` spends this cost once in the existing
whole-core floor. Its still-unpaid term is exactly

```
prefixPairDefect u y N - lowLoggedPacket u y N
```

with the old Selberg and owner-mask budgets retained. Under the original
simple exposed-zero hypotheses, `exists_native_sub_low_payment_simple`
proves that all three budgets tend to zero. The target constant remains
`399/5000`; the selected source is not normed or paid away.

The remaining work includes the central factorial sums, logged orders
`H<k<=K` on the physical pairs, the entire logged contribution above the
moving largest-prime cutoff, and their correlated radial/Selberg terms.
No independent signed upper bound or zero exclusion is claimed.

## Focused validation

The strict leaf build, namespace lint and standard-axiom audit use
[`CheckRieszPairLowOrderPayment.lean`](../scripts/CheckRieszPairLowOrderPayment.lean).
Root registration and wider checks remain deferred.

```bash
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 ../.venv/bin/python scripts/probe_riesz_pair_low_orders.py
../.venv/bin/python scripts/check_riesz_pair_low_orders.py
```

The optional replay uses 50 cached actual-prime boxes and 48,256 incidences;
44,416 satisfy the physical filter. It retains the original complete-period
mask and phase at regression height 100. All sampled orders are below the
formal large-order threshold, and their common positive kernel normalization
is not the source scale. An independent 90-digit checker evaluates the
weighted factorial sum directly at order `N+2`, rather than importing the
producer's cumulative-binomial calculation. These regressions validate the
identity and masks; the Lean theorem supplies the cofinal payment.

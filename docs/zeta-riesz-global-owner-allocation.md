# One allocation payment across all counts and periods

The complete non-largest-prime allocation is now independently negligible
at source scale. The remaining largest-prime allocation has a uniform radial
variation bound on every cofactor share in `(0,1)`, without a prime-count
factor. These are bounds for components of both joint signed estimates;
the numerical whole floor and ceiling remain open.

## The arithmetic commonality

If `q` is any prime factor of `n` other than its largest prime `p`, then
`q*p` divides `n` and `q<=p`. Consequently `log q<=log n/2`, regardless of
the number of factors or their relative sizes. The existing unpaid-order
binomial estimate therefore applies to EVERY such incidence:

\[
\sum_{k\in\mathrm{unpaidOrders}(N)}
 \mathrm{mass}_{N+1,k}\left(1-\frac{\log q}{\log n}\right)
 \le e^{-N/64}.
\]

Lean retains the exact eligibility and prime-selection masks in
`boundedShare_owner_split`. The allocation at `n` is precisely its
largest-prime incidence plus the selection with that prime erased. The
corresponding residual difference is the **negative signed nonowner
companion**, not the original coefficient's absolute mass.

## The global source-scale bound

For arbitrary changing prime selections `A(n)`, any `D` in the literal
`7N/4<log n<=9N/4` window, any complex mask `|w(n)|<=1`, every positive
length and every real height, `nonowner_sum_bound` proves

\[
\left|u^{N+1}\sum_{n\in D} w(n)\,
 c^{\mathrm{assigned}}_{A(n)\setminus\{p_{\max}(n)\},L,N}(n)
 K_N(3/2+iy,n)\right|
 \le \frac{4(N+1)}3 r^N
 \frac{1509}{1000}\,M\!\left(\frac{2049}{2048}\right),
\]

\[
0\le u\le e^{-11/16},\qquad
r=\frac{503}{1000}\frac{2048}{1023}e^{-1/64}
 <\frac{124}{125}<1.
\]

Here `M` is the existing finite summable logarithmic divisor majorant mass.
The proof uses the actual count bound `omega(n)<=4N` in this window and
retains the full `e^{-N/64}` saving when summing the arithmetic moments.
There is no fixed count ceiling, no separate cost per radial period, and
no zero hypothesis. Overlaps must still be represented by one bounded
weight per label; this theorem does not license counting a label twice.

`signed_owner_bounds` gives BOTH `Re O-E_N<=Re S<=Re O+E_N` for the exact
masked residual sums, with this same `E_N->0`. The original core lies in
the proved window. `tendsto_core_sub_owner` and
`tendsto_joint_sub_owner` connect this payment to the literal core and to
the existing whole expression
`lowerThresholdPacket-shortOverflowPacket+LeastBoundary.rest`.
Its exposed-zero source and its two open endgame thresholds are unchanged.

## The remaining owner varies uniformly

After that payment there is just one binomial mass per owned label:

\[
\theta_{\mathrm{owner}}(T)
 =\sum_{k\in\mathrm{unpaidOrders}(N)}
     \mathrm{mass}_{N+1,k}(b/T),\qquad b=\log a,\quad T=\log(pa).
\]

`owner_radial_derivative_bound` proves for EVERY `0<b<T`

\[
|\theta'_{\mathrm{owner}}(T)|\le
 \frac{6\sqrt{N+1}}{T}.
\]

Binomial variance proves the bound up to cofactor share `3/4`. Above that
share, the exact degree-lowering identity removes the apparent `1/(1-x)`
singularity and the original unpaid-order tail bounds the derivative by
`(N+1)*exp(-N/64)/T`. That is at most the displayed square-root bound.
No orders or labels are discarded in this argument.

`owner_fibre_variation` applies directly to two primes in the original
physical selection, with unique-largest ownership and total logs in
`[v-delta,v+delta]`, `v>=100`, `delta<=1/16`:

\[
|\theta_{\mathrm{owner}}(pa)-\theta_{\mathrm{owner}}(qa)|
 \le\frac{12\sqrt{N+1}}{v}|\log p-\log q|.
\]

The old sum of incidence variations cost
`20*(omega(a)+1)*sqrt(N+1)/v` and required an upper cofactor-share cap.
This owner estimate needs neither. Original physical membership is checked
at both endpoints; the interpolation introduces no additional prime labels.

## What remains unpaid

Combine this allocation control with the
[global cutoff-crossing inequalities](zeta-riesz-global-crossing.md).
The remaining arithmetic tasks are still the two joint signed prime
moments (constant and first radial moment), their combined source-scale
crossing cost, and the literal clipped/exterior boundaries. A relative
prime-period estimate is not automatically source-scale decay. Existing
favorable phase payments cannot be counted again inside a completed period.

The cofinal `-79/1000-o(1)` floor and `3/2+o(1)` ceiling remain open for
`1/2<u<=10001/20000`. There is no new zero exclusion or RH claim.

## Diagnostics and verification

The optional `scripts/probe_riesz_owner_allocation.py --literal` uses the
original unpaid orders and actual small finite prime populations, retaining
the moving length, allocation, reflection identity and full cosine phase.
It is a floating-point diagnostic, not a certificate. The observed maximum
of `|T theta'(T)|/sqrt(N+1)` on the sampled share grid is about `0.33` at
large orders; the proved constant is the conservative `6`.

At `N=10`, the additional physical selection contains 493241 actual labels.
The normalized signed difference from retaining only the owner allocation
is about `-2.65e-10`; its absolute nonowner mass is about `6.36e-6`.
These small-order values do not establish any cofinal estimate. The Lean
bound above supplies that estimate independently.

Proof sources:
[ZetaRieszNonownerAllocation.lean](../RiemannGaussian/ZetaRieszNonownerAllocation.lean),
[ZetaRieszOwnerVariation.lean](../RiemannGaussian/ZetaRieszOwnerVariation.lean).
The source hashes, terminal theorem list and diagnostic data are in
[the audit](riesz-global-owner-audit.json).

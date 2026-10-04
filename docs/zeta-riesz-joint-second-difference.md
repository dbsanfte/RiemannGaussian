# Joint comparison and curvature, 2026-10-04

The comparison and its signed curvature are now one exact Peano operator
on the unchanged finite prime/order mask. After the factorial orders are
summed, its second derivative has an exact centered-binomial
summation-by-parts formula. The literal joined prefix/Selberg coefficient
has only five possible *order-weight curvature boundaries* across its two
factorial degrees. These are structural identities, not an independent
floor, ceiling or zero exclusion. No global floor credit is earned here.

The local checked leaf is
[ZetaRieszJointSecondDifference.lean](../RiemannGaussian/ZetaRieszJointSecondDifference.lean).
It imports the previous same-mask saddle experiment and adds no root
registration, completion or public frontier change.

## One joint operator before any bound

For every original tuple `(p,i,j,q)`, put

\[
\nu=\theta(i-j)-\delta(\log p-\log q),\qquad
F(t)=\sum_E w_E\cos(t\nu_E)K_i(s,p)K_j(s,q).
\]

The tuple set and the complex weights are arbitrary; they can retain the
literal prime masks and full complex phase. `responsePath_hasDerivAt` and
`firstSymbol_hasDerivAt` prove the actual derivatives. In particular,

\[
-F''(t)=\sum_E w_E\nu_E^2\cos(t\nu_E)K_i(s,p)K_j(s,q).
\]

`central_difference_eq` proves

\[
F(1)+F(-1)-2F(0)=-2\,\mathrm{curvature}.
\]

`original_eq_joint_Peano` proves the integrated version, with genuine
interval integrability and no absolute values:

\[
\boxed{\quad F(0)=F(1)-\int_0^1(1-t)F''(t)\,dt.\quad}
\]

The limitation is exact as well: `joint_multiplier_eq_one` proves

\[
\cos\nu+\int_0^1(1-t)\nu^2\cos(t\nu)\,dt=1
\]

for every frequency, including zero. This operator preserves the original
response. Its form alone cannot make the selected source small. Any saving
must use the signed prime/order aggregate, including its cross terms.

## Sum factorial orders before differentiating the weight

Write

\[
\mathbb E_M^a[f]=\sum_{i=0}^M\binom Mi a^i(1-a)^{M-i}f_i,
\quad \Delta f_i=f_{i+1}-f_i,
\quad \Delta^2 f_i=f_{i+2}-2f_{i+1}+f_i.
\]

These are algebraic finite sums with arbitrary complex weights, not
probabilistic assumptions about primes. For `M>=2`, the checked centered
second-moment identity reads

\[
\mathbb E_M^a[(i-Ma)^2f_i]
=Ma(1-a)\mathbb E_{M-1}^a[a f_i+(1-a)f_{i+1}]
+M(M-1)a^2(1-a)^2\mathbb E_{M-2}^a[\Delta^2f_i].
\]

`binomialSum_detuned_second` also retains a nonzero saddle detuning and
its first-difference term. `second_difference_product` proves the exact
product rule

\[
\Delta^2(cg)_i
=g_{i+1}\Delta^2c_i+c_{i+1}\Delta^2g_i
+\Delta c_{i+1}\Delta g_{i+1}+\Delta c_i\Delta g_i.
\]

Both cross terms are essential. Keeping only mask curvature or only phase
curvature would lose the correlation being investigated.

`weighted_pair_eq_binomialSum` connects this directly to the literal
factorial prime kernels:

\[
\sum_{i=0}^M f_iK_i(s,p)K_{M-i}(s,q)
=K_M(s,pq)\,\mathbb E_M^{\log p/\log(pq)}[f].
\]

It changes no prime or radial mask, keeps both boundary orders, and
retains the entire phase in `K_M(s,pq)`.

## Actual joined coefficient and five mask boundaries

Let `K=floor(13N/32)` and `I_{M,K}(i)=1` when `K<i` and `K<M-i`, zero
otherwise. Collect the central convolution, both logged prefixes, swapped
incidences and the Selberg trace *before* examining order curvature. The
two exact weights are

\[
c^{(1)}_i=\frac{2i(N+1-i)}N+(N+1)I_{N+1,K}(i),
\]

\[
c^{(2)}_i=-\frac{N+1}{L}
\begin{cases}
N+2,&I_{N+2,K}(i)=1,\\
\min(i,N+2-i),&I_{N+2,K}(i)=0.
\end{cases}
\]

For distinct actual primes, `literal_joined_atom_collected` identifies
the original `(prefixLogCoefficient-selbergCoefficient)*K_N` with the
sum of these weights against the two factorial degrees. The existing
distinct-pair condition is retained; no additional diagonal deletion occurs.

On the valid order range, away from

\[
\{K-1,K,N-K-1,N-K,N-K+1\},
\]

`joined_weights_second_difference_off` proves exactly
`Delta^2 c^(1)=-4/N` and `Delta^2 c^(2)=0`.
This confines the exceptional *weight curvature*, not the full response:
the centered variance, detuning, phase curvature and both cross terms
remain in the same signed expression. The two factorial degrees also
retain their different kernels. No separate norm allowance is attached
to any component.

## Finite numerical regression

The optional producer
[probe_riesz_joint_second_difference.py](../scripts/probe_riesz_joint_second_difference.py)
uses pinned actual prime integers, 360-bit balls, the exact moving length,
all factorial orders and both prefixes. It records 32 joined responses
and 192 signed second-symbol samples across eight prime pairs, two center
choices and two test heights. The samples split the second symbol into
detuning, first difference, variance, polynomial curvature, mask jumps,
phase curvature and both cross jumps, then verify their signed sum.

The separate
[replay_riesz_joint_second_difference.py](../scripts/replay_riesz_joint_second_difference.py)
imports no producer and rebuilds the uncollected central incidences,
both prefixes and trace using exact binomial integers at 420 bits.
It passed 4,960 ball comparisons and 4,288 relative-width checks.

All controls have `N=256`, below the native entry order `65536`. The
heights `55` and `142` are test heights, not asserted zero ordinates.
This validates the finite bookkeeping; it supplies no prime-population
estimate and is not an ordinary CI input or Lean proof dependency.

## Remaining arithmetic target

Bound the real part of the **whole** signed Peano aggregate on the original
native mask, with the variance, detuning, phase and cross terms still joined
to the five structured order boundaries. The comparison has not been
substituted freely for the original, and the curvature has not been paid
separately. No complete-leg limit is transported through a hard mask.
The independent `399/5000` floor, fixed ceiling, restricted contradiction
and RH remain open.

The local warning-as-error build, namespace linters, transitive axiom audit
and preservation pins are recorded in
[riesz-joint-second-difference-audit.json](riesz-joint-second-difference-audit.json).

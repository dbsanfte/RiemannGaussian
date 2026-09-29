# Signed prime tails pay the coupled Riesz crossings

The proved gain is a bound for the complete prime-period response, including
its moving Riesz cutoff crossings. It retains arbitrary cofactor phases and
all squarefree prime counts. The original factorial/allocation amplitude and
cofactor-dependent holes within those periods still need payment; the whole
floor and ceiling remain open.

Source: [`ZetaRieszPrimeTailEnergy.lean`](../RiemannGaussian/ZetaRieszPrimeTailEnergy.lean).
The [audit](riesz-prime-tail-energy-audit.json) lists the compiled endpoints,
scope and optional finite diagnostic. This extends the
[signed cutoff energy](zeta-riesz-signed-cutoff-energy.md), rather than
separately estimating the already-obstructed absolute crossing sum.

## The joint numerical cost

For $a\ge5000$, $54\le |y|$, write $h=2\pi/|y|$, and let $P$
be the actual ordinary primes in $e^a<p\le e^{a+h}$. Define

\[
f(k)=\sum_{p\in P}\frac{\cos(y(\log p+c))}{p}
 \left((L-\log k)_+-(L-\log p-\log k)_+\right).
\]

Lean proves, for every real $L$, every phase $c$, and every finite
divisor cutoff $R$,

\[
\sum_{k=1}^R k\,[f(k)-f(k+1)]^2\le Q(a,y),\qquad
Q(a,y)=\frac{16}{a^3}
 +\frac{2\pi}{|y|}\left(\frac{2}{|y|a}+\frac4{a^2}\right)^2,
\qquad \sqrt{Q(a,y)}\le\frac1{16a}.
\]

`cosine_profile_energy` and `sqrt_periodEnergy_le` contain these statements.
The existing quantitative Chebyshev theorem pays every prime-discrepancy
premise. The count of primes and the Riesz length do not enter the cost.
This is an inverse-logarithmic gain, not exponential source-scale decay.

The proof integrates the **signed** prime tail before squaring:

\[
T(t)=\sum_{p\in P}\frac{\cos(y(\log p+c))}{p}
 1_{(L-\log p,L]}(t),\qquad
 f(k)-f(k+1)=\int_{\log k}^{\log(k+1)}T(t)\,dt.
\]

On the long common strip, $T$ equals the full signed prime moment, whose
absolute value is at most $4/a^2$. Only a strip of width $h$ pays the
partial-prime tail, bounded by $2/(|y|a)+4/a^2$. Thus the full moment and
all cutoff transitions are controlled together. There is no separate
positive price for every divisor crossing. Endpoint conventions are exact.

## The actual signed squarefree sum

Let

\[
B_c(n)=\sum_{p\in P}\frac{\cos(y(\log p+c))}{p}
 \bigl(\mathcal R_L(n)-\mathcal R_{L-\log p}(n)\bigr),
\quad
\mathcal R_v(n)=\sum_{d\mid n}\mu(d)(v-\log d)_+.
\]

One proved but **unevaluated** absolute $E>0$ gives

\[
\sum_{n\in S} B_{c(n)}(n)^2\le E X Q(a,y)
\]

for every squarefree $S\subset(1,X]$ and arbitrary function $c(n)$.
In particular, $c(n)=\log n$ keeps the literal product phase
$\cos(y\log(pn))$. The proof uses the exact two-component sine/cosine
rotation; it neither freezes this phase nor assumes a zero hypothesis.

Arbitrary cofactor weights have both signed bounds with squared budget
$E X Q(a,y)\sum_{n\in S}w(n)^2$. On a shell
$M<n\le2M$, weights $|w(n)|\le W/n$ pay this weight energy fully.
For an arbitrary finite family of periods/shells the terminal
`exists_radial_log_bounds` proves

\[
-K\le\sum_j\sum_{n\in S_j}w_j(n)B^{(j)}_{c_j(n)}(n)\le K,
\qquad K=\frac{\sqrt E}{16}\sum_j\frac{W_j}{a_j}.
\]

The absolute constant may absorb fixed factors between statements; within
each theorem one constant works simultaneously for all its parameters.
There is no prime-count ceiling or additional multiplier for the number of
periods. The explicit sum of their costs must still be bounded.

## Exact scope and remaining work

Each family member has a common complete prime interval and common $L$
across its cofactor population. The cofactor subset, phase and weights can
be arbitrary subject to the stated squarefreeness and energy conditions.
Prime-dependent factorial and `boundedShare` weights are **not** included
in $w(n)$. Neither are ownership/coprimality/deletion masks that remove
different primes for different cofactors. The previous literal-profile
theorem retains these data, but this numerical period budget does not yet
pay their effect.

The next target is to bound those variations and holes using the same joint
signed tails, then sum their source-normalized costs with disjoint paid
sectors. Completing a masked set into a full period without paying its
difference, or adding already-spent credit again, would be invalid. The
independent whole floor $-79/1000-o(1)$ and ceiling $3/2+o(1)$ remain
open for the existing arbitrary-multiplicity endgame.

## Optional finite diagnostic

Run `../.venv/bin/python scripts/probe_riesz_prime_tail_energy.py`.
The floating calculation uses actual primes at log endpoints 8, 10, 12 and
14, height 54, and three Riesz lengths. These endpoints are **below** the
proved numerical theorem's threshold 5000; the experiment tests the exact
tail/energy identities, not that numerical constant or any asymptotic claim.

In these four examples the signed/unsigned integrated-tail energy ratios
range from about 0.00032 to 0.00338. All 12 finite cutoff-energy checks stay
below the corresponding integrated signed energy. Independent direct
divisor/prime evaluation confirms 128 cofactor phase-rotation samples to
floating precision. No value of $E$, whole-carrier floor, zero exclusion
or RH result is certified by this probe. It is not part of CI.

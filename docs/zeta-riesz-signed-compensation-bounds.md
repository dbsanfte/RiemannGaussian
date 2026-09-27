# Signed compensation in the existing Riesz coefficient

`ZetaRieszSignedCompensationBounds` adds inequalities, not a new carrier or
transform. The original coefficient, factorial weights, finite label masks
and complex observations are unchanged. The whole retained prime sum and
the complementary carrier's independent floor remain unbounded.

For a squarefree label `n=P*r*a*b`, take `P,r,a` prime, set
`D=L-log(P)`, and retain the existing two-prime tent

\[
T_{r,a}(t)=(t)_+-(t-\log r)_+-(t-\log a)_+
 +(t-\log r-\log a)_+.
\]

Assume the cofactor is saturated at `L`, and every pair of distinct prime
factors of `b` has logarithmic sum at least `D`. These are literal support
tests; they are not asserted for the full retained packet. Define, only as
notation in this explanation,

\[
g=\min\{\log r,(\log P+\log r+\log a-L)_+\}.
\]

`coefficient_le_gap_sub_prime_tents` proves the signed inequality

\[
\operatorname{Re}c_L(n)
\le \frac{\log n}{L}
 \left(g-\sum_{q\mid b,\ q\text{ prime}}T_{r,a}(D-\log q)\right).
\]

The existing exact prime-tent identity supplies the negative sum. Only its
positive unit tent is bounded. In particular, those opposing contributions
are retained even when the small-pair saturation condition is not assumed.
There is no absolute-value replacement of their sum.

For any complex observation `z` with `Re(z)<=0`,
`re_atom_ge_signed_compensation` consequently proves

\[
\operatorname{Re}(c_L(n)z)
\ge\frac{\log n}{L}
 \left(\sum_{q\mid b,\ q\text{ prime}}T_{r,a}(D-\log q)-g\right)
 (-\operatorname{Re}z).
\]

`re_sum_ge_signed_compensation` sums this inequality on an arbitrary finite
mask, with its full complex observation on each label. The observation can
include the original source normalization, rectangle/allocation weights and
prime kernel. The negative-real phase restriction remains explicit. No prime
density approximation, zero hypothesis or count completion is used.

The stronger `re_sum_ge_compensation_all_phases` removes that phase
restriction. Write `S_n` for the **existing** opposing prime-tent sum above
and `x_n=Re(z_n)`. The bound is

\[
\operatorname{Re}\sum_n c_L(n)z_n
\ge \sum_n\frac{\log n}{L}
 \left(g_n\min(x_n,0)-S_n x_n\right).
\]

The whole term `-S_n*x_n` retains its sign; it is not replaced by a cost
involving `abs(cos)`. Only the nonnegative unit tent is bounded by its
small-pair gap. Both phase directions, all chosen prime counts and every
original observation remain in this single finite-sum inequality. Its
right-hand side still needs a source-scale signed estimate.

The subsequent `re_sum_ge_compensation_keep_positive` is stronger. For
`r<=a`, set

\[
e_n=\bigl(\log r-\max(0,L-\log P)\bigr)_+.
\]

`primePairTent_gap_identity` proves the unit tent is **exactly** `g-e`.
The improved signed inequality is

\[
\operatorname{Re}\sum_n c_L(n)z_n
\ge \sum_n\frac{\log n}{L}
 \left((g_n-S_n)x_n-e_n\max(x_n,0)\right).
\]

`unit_phase_lower_improved` verifies that this never weakens the earlier
clipped comparison. It restores the actual positive unit credit; the
remaining difference from the exact observed coefficient is
`(log n/L)*e_n*max(-x_n,0)`, now proved explicitly by
`re_atom_sub_compensation_keep_positive`. When `log r<=L-log P`, the edge defect is
zero and this step loses no phase information. Pair separation is still
an explicit requirement; composite-divisor contributions outside that
support are not paid.

The [joint phase-credit audit](zeta-riesz-joint-phase-credit.md) proves
that positive observations of balanced actual triples cannot be discarded
at source scale. It also confines this rising-edge defect to counts at
most six after the current large-prime deletion and eventual literal
length bound. The [actual-prime edge audit](zeta-riesz-joint-edge-loss.md)
then proves this remaining loss diverges even at count three. Under the
existing exposed-zero source theorem, subtracting that loss drives the
lower comparison to minus infinity, so even a cofinal floor cannot be
obtained from this clipping step. The edge needs its signed observation
retained; the whole joint floor remains open.

For an actual five-prime label `n=P*r*a*b*c`, with `a<b<c`, the separate
`five_coefficient_bounds_core` uses the existing core geometry to discharge
saturation and the reflected midpoint. It proves

\[
-\frac{\log n}{L}\,2\log r
\le \operatorname{Re}c_L(n)
\le \frac{\log n}{L}\,g.
\]

Thus the possible positive coefficient costs the exact small-pair excess,
capped at one least-prime logarithm; it costs zero when
`log(P*r*a)<=L`. The negative coefficient is retained separately. The
underlying secant theorem improves its lower bound to minus one least-prime
logarithm before the largest cofactor prime threshold is reached.

These results sharpen local signed estimates. They do **not** bound the
source-normalized compensation sum or pay labels failing pair separation.
Keeping both phase directions in the last inequality does not estimate their
net sum. No cancellation between different integers is established. The
previously divergent absolute allowance is not reintroduced, and no new zero
exclusion or RH contradiction follows.

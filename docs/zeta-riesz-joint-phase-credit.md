# Retaining positive credit in the joint floor

The joint target needs cancellation between the actual positive and
negative observations. `ZetaRieszJointPhaseCredit` quantifies a loss in
comparisons that keep only nonpositive observations. No new carrier or
continuum prime measure is introduced.

Write `a_N(n)` for the **existing** complex atom

\[
a_N(n)=(1-\theta_N(n))c_{L_N}(n)K_N(3/2+iy,n),
\]

and `S_j=coreBand u N_j K_j` for the unchanged original cofinal support.
For every fixed real `y` and `1/2<u<=10001/20000`,
`eventually_positive_credit_growth` proves that some `k>0` satisfies

\[
u^{N_j+1}\sum_{n\in S_j}\max(\operatorname{Re}a_{N_j}(n),0)
\ge k\frac{(2u)^{N_j}}{(N_j+1)^4}
\quad\text{eventually}.
\]

The constant and starting index are existential and may depend on height.
`positive_credit_tendsto_atTop` proves this positive credit tends to
infinity. This concerns the **actual signed coefficients and actual
primes**, not the earlier absolute antichain allowance.

The proof uses three disjoint fixed-width logarithmic prime intervals
near `2N/3`. A bounded translation puts their product phases in
`cos(y log n)>=1/2`. The existing PNT interval theorem counts actual
distinct prime triples; no thin cells or continuum transport are used.
Every product survives the physical, count, nondominant and smaller core
masks, and retains at least half its allocation weight eventually.
The exact pair-cutoff coefficient is `log(n)*(log(n)-L)/L`.
`box_coefficient_lower` compares it to at least three quarters of the
previous triple allowance; `box_atom_lower` retains its positive real
phase. Thus positive credit is already supplied by balanced triples.

`clipping_loss_eq` gives the exact finite identity

\[
\operatorname{Re}\left(u^{N+1}\sum_{n\in S}a_N(n)\right)
-u^{N+1}\sum_{n\in S}\min(\operatorname{Re}a_N(n),0)
=u^{N+1}\sum_{n\in S}\max(\operatorname{Re}a_N(n),0).
\]

`clipping_loss_tendsto_atTop` therefore rules out paying this deletion
by a bounded or vanishing error on the original cofinal schedule.
It does not prove a net positive floor: the negative observations remain
inside the same core and may cancel this credit.

## A stronger signed comparison

The earlier all-phase compensation inequality retained the opposing
prime tents, but clipped the positive unit observation. On its balanced
three-prime specialization the opposing prime sum is empty, so that step
discards exactly the positive unit credit.

`ZetaRieszSignedCompensationBounds.re_sum_ge_compensation_keep_positive`
now retains it. In the notation of the
[signed compensation note](zeta-riesz-signed-compensation-bounds.md), its
lower bound is

\[
\sum_n\frac{\log n}{L}
\left((g_n-S_n)x_n-e_n\max(x_n,0)\right),
\qquad e_n=\bigl(\log r-\max(0,L-\log P)\bigr)_+.
\]

It preserves the full signed `g*x` and `S*x`. The only remaining loss
in the unit-tent step is the explicit rising-edge term against a negative
observation. Its support is `L-log P<log r`. No absolute cosine replaces
the joint sum.

## The rising edge is a low-count issue

For a squarefree label with at least seven prime factors, select any
prime `P` satisfying the newly proved remaining bound
`log P<=121 log(n)/200`. Let `r=minFac(n)`. The other six or more prime
logs give

\[
\log P+6\log r\le\log n.
\]

Combining the actual upper window `log n<=203N/100` with the eventual
literal bound `L_N>=137N/100`, `least_log_reflected_margin` proves

\[
\log r+\frac{\log n}{300}\le L_N-\log P.
\]

`rising_edge_zero_of_seven` therefore kills `e_n` exactly for these labels.
This is solely the unit-edge defect: the signed opposing prime sum and
labels failing pair separation still need control. It is not a prime-count
tail estimate or a bound on every higher-count contribution.

The low-count defect is not small. The follow-up
[actual-prime edge audit](zeta-riesz-joint-edge-loss.md) makes the earlier
scalar slopes `(0.42,0.46,1.12)*N` into three disjoint prime intervals.
`ZetaRieszJointEdgeLoss.eventually_edge_loss_growth` proves that, at every
fixed nonzero height, the normalized edge loss is at least
`k*(2u)^N/(N+1)^4` eventually for some `k>0`.
`edge_loss_tendsto_atTop` proves divergence. The original core and allocation
masks are retained. This rules out paying that clipping loss by a bounded
allowance; it does not rule out cancellation when the edge stays signed.

The full `-79/1000-o(1)` cofinal floor remains open. The conclusion of this
slice is to retain the positive unit observations in the joint estimate,
with a precise low-count edge obligation, rather than discard an
exponentially growing part of the cancellation.

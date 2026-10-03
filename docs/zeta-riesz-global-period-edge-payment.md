# Whole signed boundary: incomplete phase periods paid

`ZetaRieszGlobalPeriodEdgePayment` independently pays **every incomplete
phase period and exterior endpoint** of the retained signed completion
boundary. The bound applies at every count, not one sector at a time.
The complete interior periods remain assembled and still need the signed
cofinal estimate. No whole floor or zero exclusion is claimed.

## Exact period selection

At any height with `54 <= |y|`, let

\[
w_y=\frac{2\pi}{|y|},\qquad
\ell_y(n)=w_y\left\lfloor\frac{\log n}{w_y}\right\rfloor,
\qquad h_y(n)=\ell_y(n)+w_y.
\]

Lean proves `0 < w_y <= 1` and the exact bracket
`ell_y(n) <= log n < h_y(n)`. Retain a label precisely when its entire
period fits in the original central window:

\[
\frac{1971}{1000}N\le\ell_y(n),\qquad
h_y(n)\le\frac{2029}{1000}N.
\]

Every label whose logarithm is more than one unit inside both edges is
retained. This is a deterministic total-log selection; the actual
`exp(-iy log n)` phase stays unchanged. Prime/count/physical/sieve and
factorial masks stay in the input support.

## Geometric edge theorem

The old all-mask radial estimate is extended by a fixed additive
displacement in total logarithm. In the tilted moment bound this changes
the finite constant by `exp(D)` while leaving the exponential rate intact.
For every `N >= 64`, every finite support and every coefficient family
dominated by `zetaMoebiusLogMajorant`, the difference between its full sum
and its complete-period selection satisfies

\[
\boxed{
\left\|u^{N+1}
\left(\sum_{n\in S}a_n K_N(s_0,n)
-\sum_{n\in S_{\rm periods}}a_n K_N(s_0,n)\right)\right\|
\le C_{\rm periods}e^{-N/10^6}.
}
\]

The finite constant is common to all supports, counts, heights and radii
`0 <= u <= 10001/20000`; it is existential and is not numerically set to
one. No prime-density, PNT, zero, RH, or Type-II hypothesis is used.
Only omitted edges are norm-paid. No complete period is norm-paid,
phase-frozen, replaced by a density, or separately charged by prime count.

## Spent in the actual native floor

Apply the theorem to four families in the same pruned boundary:

1. Every central ordinary prime, using the restored original coefficient.
2. Every central squarefree semiprime, with its full coefficient.
3. Raw high owners at **every** count, with their original unallocated
   coefficient and no physical/count/deletion restriction added.
4. The **same full original head** on its unique product-label axis,
   with its original owner weight and sieve.

For the head, `N >= 65536` supplies the already-proved coefficient
majorant. `wholePeriodBoundary` is the single real sum of these four
literal selections. Its head phase is the real part of the original
complex head; this respects the pruned boundary's real-valued head
convention. No new source is completed or discarded.

Let `N_j` be the actual native dyadic moment order, `B_j` the original
pruned boundary, and `P_j = wholePeriodBoundary u y j`. Lean proves

\[
|\Re B_j-P_j|
\le 4C_{\rm periods}e^{-N_j/10^6}
=E_{{\rm periods},j}\longrightarrow0.
\]

The new payment is spent directly in the existing native ledger:

\[
\boxed{
|\Re(\text{nativeScaledCore}_j)+P_j|
\le\text{nativePrunedBudget}_j+E_{{\rm periods},j}
\longrightarrow0.
}
\]

Consequently

\[
\Re(\text{nativeScaledCore}_j)
\ge-P_j-\text{nativePrunedBudget}_j-E_{{\rm periods},j}.
\]

This is an alternative signed ledger to the semiprime/head atom price.
Do not add that price, its head credit, or its two radial transfers here.
All previous native payments remain once each. The new four edge payments
cover these four retained boundary families; they are not payments of the
whole head or any complete-period central population.

## Exact remaining problem

Prove, independently of a hypothetical zero and on a cofinal native
sequence,

\[
\boxed{P_j\le\frac{399}{5000}+o(1).}
\]

This still requires signed cancellation **among different labels and
counts inside complete periods**, or among complete periods themselves.
The new theorem removes the incomplete/end periods at source scale; it
does not supply any part of this remaining constant bound. The separate
price audit proves that charging the unmatched balanced semiprimes by a
fixed positive atom allowance cannot work.

The optional whole-boundary probe recorded with that audit retains all
endpoints and passes 45 frozen complex regressions at toy `N=6,7,8` and
heights `54,65,100`. Complete central periods are much smaller than its
boundary/exterior periods there. That is motivation, not a native/cofinal
estimate: the toy length, deletion masks and schedule differ, and no
eventual native theorem is applied at those small orders.

Focused strict-leaf/build, frozen-root 14-linter and all-declaration
standard-axiom checks are pinned in
`docs/riesz-global-period-edge-payment-audit.json`. No subagents, root
registration, public update, wider gates, commit or push were used.

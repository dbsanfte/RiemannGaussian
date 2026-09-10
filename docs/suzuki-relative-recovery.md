# Relative recovery and balanced-cell exponent transfer

For the literal signal `S = suzukiChebyshevLogAverageLaplaceSignal`, Lean
proves

\[
\forall K>1,\quad \forall a\text{ sufficiently large},\quad
\exists u\in[a,Ka],\qquad S(u)>0.
\]

This is
`eventually_exists_pos_suzukiSignal_between_arbitrary_time_multiples` in
[SuzukiRelativeRecovery.lean](../RiemannGaussian/SuzukiRelativeRecovery.lean).
It replaces the earlier fixed factor 4096. Time is logarithmic in the
physical prime cutoff. The threshold may depend on `K`; no uniform limit
as `K` tends to one, bounded additive recovery interval, or eventual
pointwise positivity is claimed.

The new independent estimate controls recovery times. It does not bound
negative excursion depths or exclude an additional zeta zero.

## Keeping the damping in the exact moment

Let `f_L` be the existing positive delay average of the causal extension
of `S`, and let `F_L` be its full complex Laplace response. For every real
`d > 1/2`, use the nonnegative kernel

\[
G_{d,n}(t)=d^2\frac{(dt)^n e^{-dt}}{n!}.
\]

[SuzukiDampedDelayMoments.lean](../RiemannGaussian/SuzukiDampedDelayMoments.lean)
proves genuine absolute integrability and the exact complex identity

\[
\int_{\mathbb R} f_L(t)G_{d,n}(t)\,dt
=d^{n+2}\frac{(-1)^n}{n!}F_L^{(n)}(d).
\]

Choose any delay list containing the complete genuine zero window through
height `T >= d+1/4`. The analytic numerator after delay cancellation is
regular on the disk centered at `d` with radius `d+1/4`. This disk contains
the central double pole. The full complex normalized moment has a bounded
error after its linear double-pole term is subtracted. For the real moment,

\[
\left|\int f_L(t)G_{d,n}(t)\,dt+c(n+1)\right|\le C,
\qquad c=\texttt{suzukiArchimedeanSlopeConstant}<0.
\]

The error constant can depend on damping and the delay list. The leading
coefficient remains exactly `-c`. The canonical finite zero-window list
discharges all covering conditions and makes these moments tend to
positive infinity, without RH or a depth-bound premise.

## Both tails in an arbitrary fixed relative window

Fix `0 < l < 1 < u`. In
[GammaWindowRecovery.lean](../RiemannGaussian/GammaWindowRecovery.lean),
Lean constructs `b > 0` such that

\[
q_l=l\exp(1-(1-b)l)<1,\qquad
q_u=u\exp(1-(1-b)u)<1,
\qquad 1/u<1-b.
\]

For any causal real `f` with the required genuine weighted integral,
nonpositivity throughout `[ln/d,un/d]` implies the independent bound

\[
\int f(t)G_{d,n}(t)\,dt
\le d^2(q_l^n+q_u^n)
       \int_{\mathbb R}|f(t)e^{-bdt}|\,dt.
\]

Each tail is bounded at its own endpoint using an exponential-series
inequality. The signed middle is retained until its proposed nonpositivity
is used. No pointwise growth envelope replaces the signal.

Take `d=1+1/b`, so `bd>1/2` and the actual Suzuki weighted integral
converges. The tail bound tends to zero, whereas the signed moments grow.
There is therefore a positive delayed value in each sufficiently late
relative window. Positivity of the delay weights recovers an original
positive value within their fixed backward span. For any `K>1`, choose
`u/l<K`; this strict slack absorbs the entire delay span and integer
rounding. The terminal recovery theorem has no auxiliary hypotheses.

## Consequence for the arithmetic floor

The exact Legendre signal is `J(t)=S(t)+c*t+C_0`. For each fixed `K>1`,
every sufficiently late value with `J(t)<c*K*t+C_0` has an actual local
minimum at some `t/K<r<K*t`, with `J(r)<=J(t)`. The existing local-minimum
theorem identifies its actual balanced cutoff and exact finite potential.

[SuzukiBalancedExponentTransfer.lean](../RiemannGaussian/SuzukiBalancedExponentTransfer.lean)
then proves the following conditional transfer. Suppose `delta>0` and

\[
B_N\ge -C N^\delta
\]

eventually on the original balanced cutoffs, where `B_N` is the unchanged
mass–moment potential and `N=count+2`. For **every** `epsilon>delta`,
there is a finite `D>=0` such that eventually

\[
J(t)\ge-D e^{\epsilon t}.
\]

The literal Laplace signal `S` has the same conclusion after the exact
affine correction is absorbed. These are the two
`...balanced_power_floor_arbitrarily_small_loss` terminal theorems.
The former transfer used the fixed exponent `4096*delta`.

The input `B_N>=-C*N^delta` is still unproved. The full RH route still
requires a one-sided allowance by every positive cutoff power on balanced
cells, as explained in the
[subpolynomial criterion](suzuki-balanced-subpolynomial.md). Better
recovery times do not supply that arithmetic depth bound. In particular,
the delay filter cancels selected zero modes for this recovery argument;
its averaged moment estimate is not a source-preserving RH contradiction.

All four modules are imported from the root library. Validation covers
direct warnings-as-errors elaboration, focused and full builds, whole-root
declaration lint, explicit public theorem axiom checks, source scans, and
deterministic status generation. This slice is local; no commit, push, or
remote CI run is part of this validation.

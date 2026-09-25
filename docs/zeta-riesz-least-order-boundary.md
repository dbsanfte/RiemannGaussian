# Joint least-prime boundary: arithmetic errors paid, signed target open

This slice proves two independent arithmetic error bounds. It does **not**
bound the retained signed prime sum, prove the `-3/40` floor, or exclude a
zeta zero. The whole-carrier source frontier is unchanged.

## The literal variation

[`ZetaRieszLeastVariation`](../RiemannGaussian/ZetaRieszLeastVariation.lean)
telescopes the original finite factorial rectangle in an auxiliary least-prime
slot. At the unit endpoint the logarithm is zero; `virtualWeight_one` proves
the weight exactly zero for `N>=101`. The actual marked prime must be distinct
from the least prime, so `allocation_variation_ledger` subtracts the virtual
coincident-slot contribution explicitly. It is not silently counted twice.

The same-prime correction satisfies

\[
0\le W_N^{\rm coincident}\le 2e^{-N/1600}.
\]

`coincidentPacket_bound` pays its entire literal finite arithmetic sum after
source normalization, uniformly in the phase height and all retained masks.
The resulting signed variation is still unbounded. The telescoping identity
alone is not a cancellation estimate between different integers.

## A joint owner/least/count estimate

[`ZetaRieszLeastOrderOverflow`](../RiemannGaussian/ZetaRieszLeastOrderOverflow.lean)
keeps the full multinomial allocation of base order `N+1`. The marked order
`j` still satisfies `21N<=40j<=23N`. `lowerAllocations` keeps the original
lower least-order condition `N<=100(h+1)` but temporarily removes its upper
condition `100(h+1)<=4N`. The added allocations form `overflowAllocations`.
`lower_upper_filter_eq` proves that restoring the upper condition recovers
the *exact* old selection, including `ownerOrders`.

For a squarefree label with at least fourteen prime factors and any marked
prime, the normalized shares obey

\[
x_p+13x_{\min}\le1.
\]

Tilting the two factorial coordinates by `126/125` and `138/125` gives

\[
\frac{19}{40}\log\frac{126}{125}
-\frac1{25}\log\frac{138}{125}\le-\frac1{6000}.
\]

Lean certifies this using exact rational powers. Consequently
`overflowWeight_bound` proves

\[
0\le W_N^{\rm overflow}(n,p)\le2e^{-N/6000}
\qquad(\omega(n)\ge14).
\]

Write `U=10001/20000`, `σ=1+1/262144`, and let `Cσ` be the existing finite
`zetaMoebiusLogMajorantMass σ`. Summing every marked incidence and every
retained label with `14<=ω<=55`, `overflowPacket_bound` proves

\[
\left\|u^{N+1}E_N^{14:55}\right\|
\le110U C_\sigma r_{\rm up}^{N},\qquad
r_{\rm up}=U\frac{262144}{131071}e^{-1/6000}<1.
\]

The rate is approximately `0.9999409595002607`. The theorem is uniform for
`0<=u<=U`, arbitrary height, order, and original count cutoff. No zero
hypothesis, prime-density approximation, or completed-leg phase transfer is
used. The constant is not evaluated; this is not an explicit small allowance
at a claimed finite order.

## Exactly what remains signed

On the original low-count support, let `A_N` denote `lowerThresholdPacket`
(counts 3–55) and `B_N` denote `shortOverflowPacket` (counts 3–13).
`jointLow_boundary_ledger` proves

\[
\mathrm{jointLowCountPacket}_N=A_N-B_N-E_N^{14:55}.
\]

The first two terms retain the same coefficient, full complex phase,
squarefreeness, physical primes, least-prime ordering, count, core window,
nondominant and share-interior masks. No individual low factorial order on
the other prime legs is deleted. They must be bounded **together**.

`fullPacket_sub_joint_boundary_bound` combines the new estimate with the
already-paid ownership/allocation, exterior and count-56 errors.
`tendsto_full_sub_joint_boundary` shows that the joined packet and `A_N-B_N`
have the same source asymptotics along arbitrary cofinal orders, even with
moving heights and count cutoffs. This comparison does not supply a bound
for `A_N-B_N` itself. In particular, counts 14–55 remain in `A_N`; only their
upper-order overflow has been paid. The complementary direct carrier also
still requires its independent signed floor.

## Optional numerical checks

Run `scripts/probe_riesz_least_order_boundary.py --output PATH` with the
plotting virtual environment. This is outside ordinary CI.
[`riesz-least-order-boundary-probe.json`](riesz-least-order-boundary-probe.json)
records a sparse finite actual-prime check with full product phase and exact
finite binomial weights evaluated in floating point. The allocation ledger
agrees to about `4e-15`; the signed sum ledger agrees to about `4.4e-14` after
one common scale is removed. Only counts six and seven occur in that tiny
prime universe. It is an identity regression, not evidence for a bound on the
full prime sum.
The [label-anatomy audit](zeta-riesz-label-anatomy.md) records its additional
Mersenne log-lattice bias and inspects separately certified examples across
counts three through seven. Those examples compare divisor signs at almost
the same total logarithm; they do not provide population estimates.

The rate exploration explains the cutoff fourteen: the best exponent in this
particular two-coordinate tilt is about `-2.38e-6` at count thirteen, too weak
to beat `log(2U)≈1e-4`; at count fourteen it is about `-1.727e-4`.
This is not an impossibility theorem for other estimates at count thirteen.
The larger synthetic renewal probes remain inconclusive where quadrature
refinement disagrees. No numerical cancellation or growth is certified here.

## Continuous numerical audit of the remaining joint response

The attempt to close the signed difference has **not** produced an arithmetic
bound. The new optional
[`probe_riesz_joint_continuous.py`](../scripts/probe_riesz_joint_continuous.py)
checks the synthetic renewal computation independently of its old lattice
discretization. It is outside ordinary CI and does not replace primes by a
proved density model.

For the synthetic shifts `0, 1/40000 +/- 0.006i`, with multiplicities
`1,3,3`, write `g(x)=sum m_j exp(xi_j*x)`. The solver rescales the modes by
`T*r` so the least cutoff is one. The inverse densities of
`exp(-integral g(x)/x)` and its reciprocal
are represented as `delta_0+a` and `delta_0+b`. Their continuous method-of-steps
equations are

\[
a(s)=-\frac1s\sum_jm_j e^{\xi_js}J^-_j(s),\qquad
b(s)=\frac1s\sum_jm_j e^{\xi_js}J^+_j(s),
\]

\[
(J^-_j)'(s)=e^{-\xi_j(s-1)}a(s-1),\qquad
(J^+_j)'(s)=e^{-\xi_j(s-1)}b(s-1).
\]

The densities vanish below one, and both `J` initial values are one on
`1<=s<=2`. On the strict core `0<d<s`, the full count response is

\[
F(s,d)=-d\,a(s)-
\int_{s-d}^{s-1}(v-(s-d))a(v)b(s-v)\,dv.
\]

The first term retains the empty-factor atom; it is not an error term.
An empty integration range contributes zero.
These equations describe the **numerical continuum model**. They have not
been imported as axioms or asserted to identify the literal prime sum.

At `N=262144`, `T=2N`, owner share `0.55` and least share `0.04`, independent
adaptive convolution quadrature gives approximately `-11.06754393`. The old
lattice calculation at grid 65536 differs by about `0.001`; at grid 2048 it
differs by about `0.95`. A continuous convolution with six-point interpolation
and a second-order trapezoid correction agrees with the adaptive calculation
to about `4e-9` at its finest tested step. That agreement is a numerical
cross-check, **not an interval enclosure**.

The joint calculation integrates the exact two beta-density faces of the
finite factorial rectangle. It retains the moving floor-defined length,
the radial core window, both least-order faces and the synthetic complex
phases. The corrected responses are about `-0.00557` at `N=65536` and
`+0.00011` at `N=262144`. Several grid/quadrature choices at the latter order
give `0.000096..0.000111`, so no digits or decay rate are certified. In
particular, the older values of order `0.1` at that order are not reliable
evidence for a growing counterexample. Conversely these smaller values do
not prove eventual smallness.

The report is
[`riesz-joint-continuous-probe.json`](riesz-joint-continuous-probe.json).
It includes a higher-order stress test and its limitations. The diagnostic
at `N=524288` has sampled intermediate values about `1.5e10`; its upper
factorial face changes from about `-0.618` to `+0.0292` when the convolution
step is halved and the ODE tolerance tightened. The second run evaluates
that upper face only. Neither value establishes growth or decay, and there
is no certified `1/1000` bound even for this model.

The diagnostic
omits the least-share integration-by-parts endpoints; the existing *arithmetic*
exterior bound must not be silently applied to these synthetic endpoints.
It sums every continuum count, rather than certifying the discrete counts
3--55. The actual zero divisor, pole/regular terms, distinct-prime measure
and masked arithmetic transfer are still unestimated.

Reproduce the point audit with

```sh
.lake/plot-venv/bin/python scripts/probe_riesz_joint_continuous.py \
  --point-audit --order 262144 --output /tmp/riesz-point.json
```

For the refined joint diagnostic, use `--order 262144 --rnodes 20 --tnodes 64
--pnodes 768 --step 0.00048828125 --tol 1e-11 --em2`, with an output path.
This investigation adds no Lean theorem, no independent signed allowance,
and no change to the source or zero-free frontier.

# Restricting the Suzuki floor to mass-balanced cells

[SuzukiBalancedCells.lean](../RiemannGaussian/SuzukiBalancedCells.lean)
proves that every hypothetical right-half zero forces arbitrarily low
potentials on a specific subset of the physical integer cells. On that
subset it independently bounds the nonlinear entropy correction by
`1/(N*sqrt(N))`. The signed arithmetic floor is still unproved. This is a
restriction and a correction estimate, not an RH proof or a new zero bound.

## The cells and the exact signal

Write `N=count+2`, and use the existing constants `c` and `C` for the
Archimedean slope and intercept. Set

\[
M_N=\sum_{d\le N}\frac{\Lambda(d)}{\sqrt d},\quad
P_N=\sum_{d\le N}\frac{\Lambda(d)\log d}{\sqrt d},\quad
m_N=M_N-c.
\]

The full signed hinge signal is

\[
J(t)=C+4e^{t/2}+ct-
  \sum_{d\le e^t}\frac{\Lambda(d)}{\sqrt d}(t-\log d),\qquad t\ge0.
\]

It retains the original Laplace signal plus exactly `ct+C`.
`continuous_suzukiLegendreSignal` proves continuity through every event
using local finiteness. Every frozen trial

\[
F_N(t)=C+4e^{t/2}+ct+P_N-tM_N
\]

majorizes `J` everywhere and agrees with it on its active cell. Thus a
local minimum of `J` is also a local minimum of its active smooth trial,
including when the point is an event boundary. The derivative vanishes:

\[
2e^{t/2}=m_N,\qquad
\log N\le t\le\log(N+1).
\]

`suzukiLegendreSignal_localMin_balanced` consequently proves

\[
\boxed{2\sqrt N\le m_N\le2\sqrt{N+1}.}
\]

This is the definition of `SuzukiMassBalancedCell`. At that minimum,
`J(t)` equals the existing exact potential

\[
B_N=P_N-2m_N\bigl(\log(m_N/2)-1\bigr)+C.
\]

## Why these cells suffice

The existing positive-Laplace proof now accepts any nonzero real multiple
of the actual signal. An affine one-sided floor for either orientation
would imply RH. The compensator has a genuinely convergent transform on
the positive half-plane and is subtracted before the zero-pole argument;
the nonzero scalar is divided out. No pole or multiplicity is discarded.

`suzukiLegendreSignal_frequently_scaled_below_of_right_half_zero` therefore
proves arbitrarily late excursions in both directions under any hypothetical
right-half zero. A low point between two higher points supplies a genuine
interior minimum by compactness. This addresses the possibility of a low
point lying on a stretch that continues decreasing.

The compiled terminal source theorem
`suzuki_balanced_potential_frequently_below_of_right_half_zero` states:
for every such zero and every real `B`, arbitrarily large balanced cells
have `B_N < B`. No unproved arithmetic estimate is used in this implication.

## The nonlinear correction is uniformly small there

Let `q_N=m_N/(2*sqrt(N))` and `H(q)=q*log(q)-q+1`.
`suzuki_balanced_massRatio_bounds` proves

\[
0\le q_N-1\le\frac1{2N}.
\]

Using `0 <= H(q) <= (q-1)^2`,
`suzuki_balanced_entropy_bounds` proves for every balanced cell

\[
\boxed{0\le4\sqrt N\,H(q_N)\le\frac1{N\sqrt N}.}
\]

`suzuki_balanced_entropy_uniformly_small` proves the corresponding
eventual bound by every positive epsilon, simultaneously over all balanced
cells. It requires no zero hypothesis and no chosen subsequence.

Define the existing logarithmic-average error

\[
A_N=\sum_{d\le N}\frac{\Lambda(d)}{\sqrt d}\log(N/d)-4\sqrt N.
\]

The exact endpoint identity and the new estimate give

\[
-A_N+c\log N+C-\frac1{N\sqrt N}
\le B_N\le -A_N+c\log N+C.
\]

Thus `riemannHypothesis_of_suzuki_balanced_endpoint_eventual_floor` reduces
RH to finding one finite real `B` such that, eventually on balanced cells,

\[
\boxed{A_N\le c\log N+C+B.}
\]

This last inequality is the open arithmetic premise. We have not proved
the balanced cells have any particular density, or obtained the signed
floor from the balance condition alone. The full finite Möbius quotient
weights remain available for that arithmetic attack. Bounding their two
coefficient sequences separately is not required by this reduction.

No claim of mathematical priority is made for these convexity, Laplace,
or local-minimum arguments.

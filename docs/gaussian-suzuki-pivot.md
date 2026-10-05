# Global Gaussian/Weil and Suzuki research

The [Riesz reduction](zeta-riesz-terminal.md) is frozen. The active research
uses the existing global Suzuki arithmetic signal and Gaussian/Weil
identities. This changes the architecture; it does not establish a new
positivity estimate or show that RH has become easier.

The first concrete arithmetic target is the literal signed signal

\[
S(t)=4e^{t/2}-\sum_{n\le e^t}
 \frac{\Lambda(n)}{\sqrt n}(t-\log n),\qquad t>0.
\]

The existing
[`riemannHypothesis_of_suzuki_signal_scaled_subexponential_lower_bound`](../RiemannGaussian/SuzukiLaplaceCompensator.lean)
proves RH if, for a fixed nonzero orientation `a`,

\[
\forall\epsilon>0\ \exists C_\epsilon\ge0\ \forall t>0,
\qquad aS(t)\ge-C_\epsilon e^{\epsilon t}.
\]

All Laplace convergence, continuation and arbitrary-multiplicity steps in
this conditional theorem are proved. The arithmetic estimate is **open**.
Its subexponential allowance concerns a canceled, global signed signal;
it must not be confused with the relative PNT error envelope audited as
insufficient for prime-moment non-coherence.

The adjacent
[`RiemannXiBoundaryGaussianGram`](../RiemannGaussian/RiemannXiBoundaryGaussianGram.lean)
identifies the complete reflected zero-pair heat correlation with a
Hilbert Gram norm. Its vanishing at positive heat time is equivalent to
RH, with all multiplicities and reflection pairs retained. Independent
arithmetic vanishing remains open. One-point Gaussian positivity or
automatic Gram nonnegativity does not establish it.

The next research pass should compare the actual Suzuki signal, its full
Archimedean correction and Gaussian transform before estimating their
signed difference. Probe growing cutoffs for joint mass/moment constraints
and cross-scale inequalities on actual `Lambda`, with continuous coherent
countermodels as rejection controls. Then attempt a concrete one-sided
arithmetic estimate for `S`, or an arithmetic identity controlling the
complete reflected Gaussian Gram. A conditional reformulation or finite
numerical agreement alone does not count as a new bound.

Preserve the earlier Suzuki transport/source obstructions. Do not revive
local Riesz cutoff searches, hard-share completions or source-preserving
saddle decompositions. The
[compensator notes](suzuki-subexponential-compensator.md) and
[Gaussian–Suzuki bridge](../RiemannGaussian/GaussianScrewBridge.lean)
give the existing interfaces. Published-region imports and finite-height
coverage remain separate from this all-height arithmetic task.

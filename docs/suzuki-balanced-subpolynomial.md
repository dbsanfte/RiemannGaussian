# The growing allowance now needs only balanced cells

[`SuzukiBalancedSubpolynomial.lean`](../RiemannGaussian/SuzukiBalancedSubpolynomial.lean)
proves the following criterion for the actual arithmetic quantities:

\[
\left(\forall\varepsilon>0\;\exists C_\varepsilon\;
\forall N\text{ sufficiently large and balanced},\quad
B_N\ge-C_\varepsilon N^\varepsilon\right)
\Longrightarrow\mathrm{RH}.
\]

Here `N=count+2`, `B_N=suzukiMassLegendrePotential count`, and balance means

\[
2\sqrt N\le M_N-c\le2\sqrt{N+1},
\]

with the literal weighted prime mass `M_N` and actual Archimedean slope
`c=suzukiArchimedeanSlopeConstant<0`. This is
`riemannHypothesis_of_suzuki_balanced_potential_eventually_subpolynomial_lower_bound`.
The lower bound in its premise remains unproved.

## The localization is unconditional

Write `J` for the complete signed Legendre signal and `C` for its retained
Archimedean intercept. At every sufficiently large `t`, if

\[
J(t)<4096ct+C,
\]

then there is an actual local minimum `r` satisfying

\[
t/4096<r<4096t,\qquad J(r)\le J(t).
\]

This is `eventually_suzukiLegendre_deep_value_has_controlled_localMin`.
The [controlled recovery theorem](suzuki-controlled-recovery.md) supplies
higher endpoints on both sides of `t`; the compact interval minimum lies
strictly between them. The original local-minimum theorem then identifies
`J(r)` exactly with `B_N` on a balanced cell and retains
`log N <= r <= log(N+1)`. The cutoff necessarily tends to infinity with `t`.

## The exponent and all auxiliary terms are accounted for

A balanced-cell floor with one fixed exponent `delta>0` gives an eventual
whole-signal floor of the form

\[
J(t)\ge-D\exp(4096\delta t).
\]

This is `suzukiLegendre_eventually_exp_lower_of_balanced_power_floor`.
At a deep value, the local minimum has `N^delta <= exp(4096*delta*t)`.
At all other values the recovery threshold is already a linear lower
bound, absorbed by the same exponential allowance.

For a desired exponent `epsilon`, choose `delta=epsilon/4096`. Continuity
controls the finite time head. The exact identity `J=S+c*t+C` transfers
the bound to the actual Suzuki Laplace signal, so the previously proved
general subexponential compensator applies. No recovery-time hypothesis,
finite-head bound, or omitted affine term remains to be supplied.

The companion theorem
`riemannHypothesis_of_suzuki_balanced_logAverage_eventually_subpolynomial_upper`
permits the single literal logarithmic-average error `A_N` as the target:

\[
\forall\varepsilon>0\;\exists C_\varepsilon\;
\forall N\text{ sufficiently large and balanced},\qquad
A_N\le C_\varepsilon N^\varepsilon.
\]

The exact relation is `B_N=-A_N+c*log N+C-entropy_N`. On balanced cells,
`0 <= entropy_N <= 1/(N*sqrt N)`. Its full contribution and the affine
centering are absorbed into the coefficient of each positive power.

## What is still missing

`suzuki_balanced_potential_power_excursions_of_right_half_zero` proves that
any hypothetical right-half zero forces some positive exponent `epsilon`
for which balanced-cell potentials fall below `-C*N^epsilon`, for every
constant `C`, at arbitrarily large balanced cutoffs.

Thus the adverse source cannot move to unbalanced cutoffs or evade the
argument through a very late recovery. The independent signed arithmetic
estimate on balanced cells is now the remaining task. The previously
proved `o(sqrt N)` bound does not establish the required subpolynomial
allowance. These theorems do not give a new unconditional zero exclusion.

The [independent complete-block estimate](suzuki-balanced-block-bounds.md)
now bounds `abs(B_(N+L)-B_N)` by `(L+1)^2/(N*sqrt(N))` whenever both
endpoints are balanced. This gives uniform local decay below the
three-quarter power length scale, but does not supply a global floor or
a sufficiently dense covering by balanced endpoints. Long blocks and
accumulated decreases remain part of the same arithmetic task.

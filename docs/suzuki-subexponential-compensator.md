# General subexponential compensation in the Suzuki--Landau argument

The checked analytic implication now accepts an arbitrary nonnegative
compensator whose Laplace integral converges at every positive damping.
Subexponential growth and local integrability suffice. The exact
mass--moment potential consequently needs only a one-sided subpolynomial
allowance over all sufficiently large cutoffs. This allowance is still
unproved. No new unconditional zero bound or mathematical-priority claim
is made.

## Analytic theorem

Write the genuine logarithmic-time signal as

\[
S(t)=4e^{t/2}-\sum_{d\le e^t}
  \frac{\Lambda(d)}{\sqrt d}(t-\log d),\qquad t>0.
\]

[SuzukiLaplaceCompensator.lean](../RiemannGaussian/SuzukiLaplaceCompensator.lean)
proves `riemannHypothesis_of_suzuki_signal_scaled_compensated_lower_bound`.
For any nonzero real `a` and measurable nonnegative `f`, the premises are

\[
aS(t)\ge-f(t)\quad(t>0),\qquad
\int_0^\infty f(t)e^{-\lambda t}\,dt<\infty
\quad\text{for every }\lambda>0.
\]

The integral premise means genuine Lebesgue integrability, not merely a
totalized integral value. The measure with density `aS+f` is positive.
Landau continuation forces its Laplace transform to converge throughout
the positive half-plane. The exact difference

\[
\frac1a\left(
  \int_0^\infty(aS(t)+f(t))e^{-zt}\,dt
  -\int_0^\infty f(t)e^{-zt}\,dt\right)
\]

then extends the original response. The compensator's literal complex
integral is analytic there by
`analyticOnNhd_positiveTimeLaplace_of_integrable_exp`.
It cannot remove a hypothetical right-half zero's nonzero pole residue.
The existing xi and eta argument supplies the contradiction, including
arbitrary analytic multiplicity and either nonzero orientation `a`.

`integrableOn_exp_weight_of_subexponential_growth` discharges the
integrability premise for any locally integrable real `f` on `[0,infinity)`
satisfying

\[
f(t)=O_\varepsilon(e^{\varepsilon t})
\quad\text{for every }\varepsilon>0.
\]

The local hypothesis controls the initial interval. In the tail, given
`lambda>0`, take `epsilon=lambda/2`; the damped function is dominated by
an integrable decaying exponential. No monotonicity or prescribed profile
of `f` is required.

`riemannHypothesis_of_suzuki_signal_scaled_subexponential_lower_bound`
also avoids selecting a compensator: it constructs
`f(t)=max(0,-aS(t))` from the one-sided estimates themselves. Constants
can depend on `epsilon`. The previous affine theorem now invokes the
general argument instead of duplicating its analytic proof.

## The exact arithmetic target

Keep the complete prime sums and exact Archimedean constants `c` and `C`:

\[
M_N=\sum_{d\le N}\frac{\Lambda(d)}{\sqrt d},\qquad
P_N=\sum_{d\le N}\frac{\Lambda(d)\log d}{\sqrt d},\qquad
m_N=M_N-c,
\]
\[
B_N=P_N-2m_N\bigl(\log(m_N/2)-1\bigr)+C.
\]

For physical `N=count+2`,
`riemannHypothesis_of_suzukiMassLegendrePotential_eventually_subpolynomial_lower_bound`
in [SuzukiSubexponentialWork.lean](../RiemannGaussian/SuzukiSubexponentialWork.lean)
proves that the following open arithmetic estimate implies RH:

\[
\boxed{\forall\varepsilon>0\ \exists C_\varepsilon,N_\varepsilon\quad
  N\ge N_\varepsilon\Longrightarrow B_N\ge-C_\varepsilon N^\varepsilon.}
\]

This is the existing attained optimum over **all** feasible divisor
minorants. No coefficient family or numerical optimizer is chosen.
The proof absorbs the finite initial segment and the entire already
bounded difference between `B_N` and the canonical gap. An increasing
power envelope transfers through the exact active event prefix; it
becomes `C_epsilon exp(epsilon t)` without an exponent loss.

There is also a direct version for the literal arithmetic error

\[
A_N=\sum_{d\le N}\frac{\Lambda(d)}{\sqrt d}\log(N/d)-4\sqrt N.
\]

`riemannHypothesis_of_suzuki_logAverage_eventually_subpolynomial_upper`
proves RH from `A_N <= C_epsilon N^epsilon` eventually for every positive
`epsilon`. Integer-to-real interpolation and finite heads are discharged.
This implication has no separate entropy assumption.

## What a hypothetical zero would require

`suzukiMassLegendrePotential_power_excursions_of_right_half_zero` proves
that every hypothetical right-half zero forces

\[
\exists\varepsilon>0\ \forall D\in\mathbb R\quad
 B_N<-DN^\varepsilon\quad\text{for arbitrarily large }N.
\]

Thus arbitrarily low values alone understate the required obstruction:
there must be negative excursions of some positive power size. The
theorem does not identify that exponent from the zero's real part.

The new sufficient bound is over **all sufficiently large cutoffs**.
The preceding [balanced-cell theorem](suzuki-balanced-cells.md) separately
allows a **constant** floor only on balanced cells. We have not combined
the balanced-cell restriction with a growing subpolynomial allowance;
the old unbounded-minimum argument alone does not justify that combination.

The existing unconditional `o(sqrt(N))` cancellation does not establish
the new premise. A fixed exponent below `1/2` would still not give the
displayed all-exponent RH criterion. The next arithmetic estimate must
bound the negative part of the full exact potential, or the positive part
of the literal logarithmic average, by every positive cutoff power while
retaining the complete signed sum.

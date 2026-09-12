# Positive cosine modulation of the complete Fermi budget

The verified result introduces a positive modulation of the Gaussian
window and transports it through the actual prime, zero, source and pole
identities. It preserves the complete outside allowance. The downstream
exact scalar estimates and complete height costs now prove the
[`24/125` zero-free region](gaussian-fermi-modulated-zero-free.md), with
an existential, unevaluated height threshold.

## Exact coupled modulation

For every real `delta`, define

\[
q_\delta(u)=\frac{1+\cos(\delta u)}2,\qquad
g_{B,\delta}(u)=e^{-Bu^2}q_\delta(u).
\]

The factor lies in `[0,1]` and equals one at zero. It preserves every
absolute exponential moment of the original window. For the original
Fermi transform `F_a[g](z)`, Lean proves

\[
F_a[gq_\delta](z)=\frac12F_a[g](z)
 +\frac14F_a[g](z+i\delta)+\frac14F_a[g](z-i\delta).
\]

The same positive combination acts on the complete reflected pair
`F_a[g](z)+F_a[g](a-conj(z))`. Each shift retains the same real part, so
the original closed-strip positivity transfers to the modulated pair.
This works for every window satisfying the stated integrability and
pair-positivity hypotheses. Every positive Gaussian width discharges
those hypotheses.

The general real partition also stays exact:

\[
\Re F_a[g](x)+\Re F_a[g](a+x)=\mathcal H_g(x),\qquad
\mathcal H_g(x)=\int_0^\infty g(u)e^{-xu}\,du.
\]

For a nonnegative window, real Laplace monotonicity gives both

\[
\mathcal H_g(x)\le\Re F_a[g](x)+\Re F_a[g](a-x)\quad(x\ge0)
\]

and

\[
\Re F_{2\sigma-1}[g](\sigma-1)+\Re F_{2\sigma-1}[g](\sigma)
 \le\mathcal H_g(\sigma-1)\quad(\sigma\le1).
\]

The exact signed source reserve is retained before its sign is used.
See [FermiCosineModulation.lean](../RiemannGaussian/FermiCosineModulation.lean).

## The original arithmetic and complete zero divisor

Write

\[
\mathcal M_\delta f(t)=\frac12f(t)+\frac14f(t+\delta)+\frac14f(t-\delta).
\]

The original convergent Fermi prime series, including every von Mangoldt
prime-power term, satisfies the literal identity

\[
\mathcal M_\delta\operatorname{primeSum}(t)
 =\sum_{n\ge1}q_\delta(\log n)\operatorname{primeSummand}(t,n).
\]

For every finite cosine family with nonnegative complete kernel, the
modulated full prime combination remains nonnegative. Individual
oscillatory summands are not assigned a sign. Their phases are combined
with the original common positive arithmetic amplitude first.

At a proved common band margin `m`, each original selected-zero budget
applies to all three evaluations. The sufficient height condition is

\[
2\bigl(|\omega_j t|+|\delta|\bigr)\le H.
\]

Since the three positive weights sum to one, their averaged error is
exactly the old allowance, rather than three times that allowance. The
actual signed prime term remains in a named upstream theorem before its
nonnegativity is used.

See `hasSum_prime_phase`, `prime_phase_nonneg`,
`selected_zero_phase_budget_with_prime`, and `selected_zero_phase_budget`
in [GaussianFermiModulatedBudget.lean](../RiemannGaussian/GaussianFermiModulatedBudget.lean).

## The source and constant pole use the same window

For an actual right-half zero `rho=beta+i*gamma`, its distinct horizontal
partner is selected as well. Their averaged contributions contain

\[
m_\rho\mathcal H_{g_{B,\delta}}(\sigma-\beta).
\]

The complete averaged constant pole is bounded above by
`H_(g_(B,delta))(sigma-1)`. The two comparisons retain the cosine factor
inside their real integrals. Bounding each shifted pole separately would
lose this window comparison.

The terminal theorem `resonant_pair_phase_bound` applies to every original
finite nonnegative coefficient family with nonnegative cosine kernel and
a selected unit frequency. It keeps the complete averaged pole/gamma
cost, the full analytic multiplicity and the same outside allowance.
All shifted frequencies must satisfy the displayed band condition.

See [GaussianFermiModulatedSource.lean](../RiemannGaussian/GaussianFermiModulatedSource.lean).

## Exact scalar estimates and the resulting region

The downstream theorem uses

\[
L=\log|\gamma|,\quad H=50|\gamma|,\quad
m=\frac{3}{16\log H},\quad B=\frac1{9L^2},\quad\delta=\frac1{2L}.
\]

After scaling the integration variable by `3L`, the unit window is
`g(u)=exp(-u^2)*(1+cos(3u/2))/2`. The verified comparison uses the
existing coefficient bounds `a0<=37/200`, `a1>=79/250`, `M<=61/100`;
no new base phase coefficients are fitted.

The target is `24/125`, with normalized input
`937/5000<=mu=L*m<=3/16`. Lean proves the rational Laplace enclosures

\[
\mathcal H_g(69/5000)\ge6911/10000,\qquad
\mathcal H_g(-9/16)\le2263/2500.
\]

They leave a proved unit-profile surplus of at least `1/20000` after
paying `M/12`. The exact dilation, shifted nonconstant pole and gamma
bounds, complete outside allowance and eventual thresholds are all
discharged in the [zero-free proof](../RiemannGaussian/GaussianFermiModulatedZeroFree.lean).

The source enclosure uses the zero-damping Gaussian cosine integral and
the improved first moment. The pole enclosure integrates a global
degree-twelve cosine majorant using the signed Gaussian moment
recurrence. The [exact integral enclosures](../RiemannGaussian/GaussianModulatedLaplaceEnclosure.lean)
use no quadrature or numerical oracle. See the
[proof ledger and scope](gaussian-fermi-modulated-zero-free.md).

## Route audit and limits

A direct transfer of the rational Stechkin subtraction to the Fermi pair
was tested numerically and failed its required pointwise sign. For a
critical-line point at displacement `2`, Gaussian width `0.1`, original
line `1`, comparison line `(1+sqrt(5))/2` and coefficient `1/sqrt(5)`,
quadrature produced a negative combined pair. This is an exploration
diagnostic, not a compiled counterexample. No such subtraction is used
in the proofs above.

The cosine modulation uses positive averaging instead. It does not
establish an independent lower bound for the separate factorial-moment
prime heat, or remove any of that source's accumulated correction terms.
The larger zero-free region does not supply the remaining global RH
bound. No historical novelty claim is made. RH remains open.

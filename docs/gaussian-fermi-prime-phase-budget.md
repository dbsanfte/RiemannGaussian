# Literal Fermi prime formula and general phase budget

The complete Gaussian Fermi zero sum now has a proved explicit formula
with its literal prime-power series, exact pole pair, constant term and
integrable digamma average. Every finite nonnegative cosine test gives the
entire prime series the favorable sign after the phases are combined.
The resulting bound retains any selected finite set of genuine zeros,
including their analytic multiplicities. It uses the existing zero-free
width. The [subsequent gamma bound](gaussian-fermi-gamma-bound.md) is now
explicit. The [resonant continuation](gaussian-fermi-resonant-budget.md)
also bounds the poles and target pair. The
[independent Gaussian comparison](gaussian-fermi-zero-free-region.md)
now proves the stronger eventual width `3/(20*log(abs(t)))`.

Four root-imported modules implement this continuation of the
[exact Gaussian mixture](gaussian-fermi-explicit-mixture.md):

- [GaussianFermiCosineAverage](../RiemannGaussian/GaussianFermiCosineAverage.lean):
  exact complex-character and shifted-cosine evaluations.
- [GaussianFermiPrimeFormula](../RiemannGaussian/GaussianFermiPrimeFormula.lean):
  the literal convergent prime series and the full prime/integral interchange.
- [GaussianFermiPoleFormula](../RiemannGaussian/GaussianFermiPoleFormula.lean):
  exact poles, constant normalization, gamma integrability and full formula.
- [GaussianFermiPhaseBudget](../RiemannGaussian/GaussianFermiPhaseBudget.lean):
  general phase positivity and the selected-zero budget.

These are proofs from the repository's existing analytic chain. No external
numerical zero-free theorem is assumed. In particular, the external `4.896`
region, the independent signed ordinary-prime-tail bound in the original
RH reduction, and RH remain unproved here.

## Evaluate the prime average without losing its phase

Retain the previous centered signal and probability density:

```text
h_(a,B)(u) = exp(-B*u^2-(a/2)*u)/(1+exp(-a*u)),
p_(a,c)(y) = Re(integral_R h_(a,c)(u)*exp(-i*y*u) du)/pi.
```

The earlier characteristic identity gives, for `a>=0`, `c>0`, and every
real frequency `x` and center `t`,

```text
integral_R p_(a,c)(y)*cos((t-y)*x) dy
  = 2*h_(a,c)(x)*cos(t*x).
```

`integral_density_shifted_phase` proves the full complex version before
`integral_density_cosine` takes its real part. Both integrands are absolutely
integrable. The exact identity

```text
exp(-b*u^2)*h_(a,c)(u) = h_(a,b+c)(u)
```

recombines the Gaussian scales. With `B=b+c`, `epsilon=1/(4*b)` and `b,c>0`,
the original literal prime series is

```text
P_(a,B)(t) = sum_n Lambda(n)/sqrt(n) * h_(a,B)(log(n))*cos(t*log(n)).
```

Here `Lambda` is the actual von Mangoldt function, so prime powers retain
their original arithmetic weights. `summable_primeSummand` proves absolute
convergence for every `B>0`, `a>=0` and real `t`.

`summable_integral_norm_density_primeSummand` uses the existing Gaussian
prime series at center zero as a uniform majorant. The counting-measure
product argument also proves integrability of the full averaged prime
function. Thus `hasSum_primeSummand_average` and `normalized_prime_average`
justify the complete exchange and its exact coefficient:

```text
sqrt(pi/b)/8 * integral_R p_(a,c)(y)*
  gaussianPrimeContribution(epsilon,t-y) dy = P_(a,B)(t).
```

No interchange relies on formal manipulation of a divergent series.

## Explicit poles and gamma term

Use `sigma>=1/2`, `a=2*sigma-1` and the same `B=b+c`. Define

```text
F_(a,B)(z) = integral_(u>0)
  exp(-B*u^2)/(1+exp(-a*u))*exp(-z*u) du,

Pole_(B,sigma)(t)
  = Re F_(a,B)(sigma+i*t) + Re F_(a,B)(sigma-1+i*t),

D_(a;b,c)(t)
  = sqrt(pi/b)/8 * integral_R p_(a,c)(y)*
      gaussianDigammaIntegral(1/(4*b),t-y) dy.
```

`normalized_pole_average` evaluates the elementary Gaussian pole term to
`Pole`. `polePair_eq_physical` proves this physical display by conjugation;
it does not incorrectly identify the analytic and physical complex pairs.
`normalized_constant_average` fixes the constant term to `-log(pi)/4`.
`integrable_density_digamma` proves absolute integrability of the explicit
gamma average, with no unproved analytic hypothesis.

For the original reflected contribution

```text
Q_(B,sigma,t)(rho) = multiplicity(rho)/2 * Re(
  F_(a,B)(sigma+i*t-rho) +
  F_(a,B)(sigma+i*t-(1-conj(rho)))),
```

`zero_side_eq_poles_digamma_sub_prime` proves

```text
sum_rho Q_(B,sigma,t)(rho)
  = Pole_(B,sigma)(t) - log(pi)/4 + D_(a;b,c)(t) - P_(a,B)(t).
```

All zero multiplicities and normalization factors survive. The original
zero series has the upstream `HasSum` proof; the new prime series and each
integrated term have their own convergence proofs.

`digammaAverage_eq_of_add_eq` further proves that `D` depends only on the
total scale `b+c`: every positive split gives the same value. The split may
therefore be chosen for a later estimate without changing the gamma term.

## General phase tests and retained zeros

Let `J` be any finite index set, `w_j>=0` its weights, and `omega_j` any
real frequencies. Suppose the actual cosine test satisfies

```text
T(x) = sum_(j in J) w_j*cos(omega_j*x) >= 0    for every real x.
```

No frequency count or coefficient family is selected. The exact identity
`hasSum_prime_phase` keeps the shared positive amplitude until combination:

```text
sum_j w_j*P_(a,B)(omega_j*t)
  = sum_n Lambda(n)/sqrt(n)*h_(a,B)(log(n))*T(t*log(n)) >= 0.
```

`prime_phase_nonneg` proves the inequality. The repository's mathematically
defined contact family is already one checked instance, through
`exact_contact_prime_phase_nonneg`; no coefficient search is needed.

Set `sigma=1-m(H)` using the
[proved zero-free margin](zeta-pole-reserve-bootstrap.md). Let `S` be any
finite set of actual zeros with `abs(Im(rho))<=H`. Assume `H>=1`,
`b,c>0`, `m(H)^2<=B=b+c`, and `2*abs(omega_j*t)<=H` for every selected
frequency. With `E(B,H)` the previously proved full outside-zero allowance,
`selected_zero_phase_budget` gives

```text
sum_j w_j * sum_(rho in S) Q_(B,sigma,omega_j*t)(rho)
  <= sum_j w_j*(Pole_(B,sigma)(omega_j*t) - log(pi)/4
                  + D_(a;b,c)(omega_j*t))
       + (sum_j w_j)*E(B,H).
```

The finite/infinite zero partition remains an exact theorem upstream.
Every unselected zero in the height band is nonnegative, while the entire
outside divisor is paid for. The prime term is removed only after its
phases have been combined and its sign proved.

For `B<=1`, the existing allowance theorem gives
`E(B,H)<=K*log(H+2)/sqrt(H)`, uniformly over all admissible scales. The phase
budget pays this allowance multiplied by `sum_j w_j`. Thus the allowance
vanishes for bounded total phase weight; growing families must account for
both their total weight and their largest evaluation ordinate. No free
passage to an infinite phase family is claimed.

## Remaining obstruction and scope

This is an actual zero-budget theorem, with the arithmetic prime sign
discharged for every admissible finite test. The
[subsequent gamma continuation](gaussian-fermi-gamma-bound.md) proves
`D(t) <= log(5/4+abs(t))/4 + 7/(8*(5/4+abs(t)))`, uniformly over
`0<a<=1`, `b,c>0` and `b+c<=1`, and inserts it into the selected-zero budget.
Its exact second spectral moment prevents an inverse-scale loss.

The [resonant continuation](gaussian-fermi-resonant-budget.md) now bounds
the actual poles at both constant and nonzero frequencies and the full
distinct target pair from below. The
[subsequent independent Gaussian comparison](gaussian-fermi-zero-free-region.md)
proves the stronger eventual width `3/(20*log(abs(t)))` with every tail
condition discharged. Its finite threshold is proved to exist and has
not been numerically evaluated.

The existing edge margin `m(t)` is unchanged. This phase budget is a
different smoothed expression from the ordinary-prime tail in the original
RH contradiction; its favorable prime sign does not close that separate
gap. No historical novelty or best-published-region claim is made.

## Local verification

All local gates passed: strict direct elaboration of all four modules,
focused builds, the full warning-as-error build (10,127 jobs), all 14
declaration linters, 22 terminal axiom audits, whole-project declaration
lint, the compiled-environment soundness generator, source-placeholder
scan, and whitespace checks. The inventory contains 1,280 modules and
28,327 compiled project declarations, with zero project axioms and zero
placeholder dependencies. Every audited theorem uses only `propext`,
`Classical.choice` and `Quot.sound`. README links and tables pass, and its
Current Direction is one paragraph of 446 characters. These are local validation results; remote CI is checked separately on the exact commit.

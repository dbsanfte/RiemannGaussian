# Exact arithmetic average for the Gaussian Fermi zero side

The original Gaussian Fermi zero sum is now identified with an absolutely
convergent spectral average of the repository's unconditional Gaussian
arithmetic explicit formula. The existing vanishing allowance transfers
to that arithmetic average. The subsequent
[literal-prime formula and general phase budget](gaussian-fermi-prime-phase-budget.md)
evaluate the prime, pole and constant terms. The
[gamma continuation](gaussian-fermi-gamma-bound.md) now gives an explicit
quarter-logarithm upper bound, uniform over shrinking Gaussian scales.
The [resonant continuation](gaussian-fermi-resonant-budget.md) also proves
Gaussian pole and target-pair bounds. The
[independent Gaussian comparison](gaussian-fermi-zero-free-region.md)
now proves a stronger eventual exclusion, with exact coefficient `3/20`
and an existential height threshold.

Four root-imported modules implement the connection:

- [GaussianFermiSpectralWeight](../RiemannGaussian/GaussianFermiSpectralWeight.lean)
  proves positivity, integrability, exact unit mass and Fourier inversion.
- [GaussianFermiGaussianMixture](../RiemannGaussian/GaussianFermiGaussianMixture.lean)
  reconstructs the original complex pair by a Gaussian average.
- [GaussianFermiZeroInterchange](../RiemannGaussian/GaussianFermiZeroInterchange.lean)
  proves the full multiplicity-aware integral/sum interchange.
- [GaussianFermiZeroMixture](../RiemannGaussian/GaussianFermiZeroMixture.lean)
  identifies the actual arithmetic average and transports the lower bound.

This continues the [ideal Fermi reflection method](fermi-reflection-zero-free-plan.md)
inspired by Bellotti--Trudgian--Yang. It uses the repository's own Gaussian
and divisor theorems; no external Lean proof has been copied or assumed.
The external numerical `4.896` region and RH remain unproved here.

## An exact positive averaging operator

For `a>0`, `c>0`, define the centered original signal and its angular Fourier
transform by

```text
h_(a,c)(u) = exp(-c*u^2-(a/2)*u)/(1+exp(-a*u)),
K_(a,c)(y) = integral_R h_(a,c)(u)*exp(-i*y*u) du,
p_(a,c)(y) = Re(K_(a,c)(y))/pi.
```

`kernel_im` proves that `K` is real: its two centered analytic partners are
conjugates. `density_nonneg` then uses the proved reflection-strip theorem
to show `p(y)>=0` at every frequency. The two-derivative bound gives a finite
constant `D` with `abs(p(y))<=D/(1+y^2)`, including zero frequency. Thus `p`
is genuinely integrable.

Fourier inversion proves the exact characteristic function

```text
integral_R p_(a,c)(y)*exp(i*y*u) dy = 2*h_(a,c)(u).
```

Since `h_(a,c)(0)=1/2`, `integral_density` proves `integral_R p(y) dy = 1`.
This is a positive averaging density with exact normalization, valid for
every positive pair of parameters. The complex Fourier identity is retained
alongside positivity and the inverse-square estimate.

## Reconstruction at every complex argument

Split the total time-Gaussian scale as `B=b+c`, with `b,c>0`. Write

```text
F_(a,B)(z) = integral_(u>0)
  exp(-B*u^2)/(1+exp(-a*u)) * exp(-z*u) du,
G_b(q) = sqrt(pi/b)*exp(q^2/(4*b)).
```

`pair_eq_gaussian_average` proves

```text
F_(a,B)(z)+F_(a,B)(a-z)
  = (1/2)*integral_R p_(a,c)(y)*G_b(z-a/2-i*y) dy.
```

The identity holds at every complex `z`. `split_timeAtom` retains the exact
pointwise time identity; a product-integrability proof discharges the
interchange with the Gaussian integral. The Gaussian norm is also retained
in its localized form, before its coarser uniform bound is used.

For a physical reflected zero pair, the real parts of the analytic and
physical pairs agree. Their full complex values are not identified.

## Why localization makes the infinite interchange work

For fixed positive scales and an evaluation ordinate `t`, each distinct
zero contributes the complex integrand

```text
p(y)*multiplicity(rho)*
  exp(-epsilon*(spectralCoordinate(rho)-(t-y))^2).
```

The proved strip geometry bounds the off-axis Gaussian amplification by
`exp(epsilon/4)`. The Gaussian remains centered near the zero's own ordinate
while its integral is estimated. The elementary localization inequality

```text
1/(1+y^2)
  <= 4*(1+t^2)*(1+(gamma-t+y)^2)/(1+gamma^2)
```

and the finite Gaussian second moment give one constant `C` such that

```text
integral_R norm(zeroIntegrand(rho,y)) dy
  <= C*multiplicity(rho)/(1+gamma^2).
```

The existing actual divisor theorem makes the full right-hand side
summable. `summable_integral_norm_zeroIntegrand` pays for every zero and
every analytic multiplicity. The counting-measure product proof also
establishes absolute integrability of the entire averaged zero function.
`hasSum_integral_zeroIntegrand` records both convergence and the exact
canonical Gaussian average.

## The actual arithmetic identity and its normalization

Let `sigma>=1/2`, `a=2*sigma-1`, `B=b+c` and `epsilon=1/(4*b)`. The original
physical contribution is

```text
Q(rho)=multiplicity(rho)/2 * Re(
  F_(a,B)(sigma+i*t-rho) +
  F_(a,B)(sigma+i*t-(1-conj(rho)))).
```

Let `A_epsilon(t)` denote the literal
[`gaussianArithmeticExplicitFormula`](../RiemannGaussian/GaussianExplicitFormula.lean),
whose equality with the canonical symmetric zero sum is already proved in
[`gaussianArithmeticExplicitFormula_eq_canonical`](../RiemannGaussian/GaussianXiLogDerivativeGrowth.lean).
The new terminal theorem `hasSum_contribution_arithmetic_average` proves

```text
sum_rho Q(rho)
  = sqrt(pi/b)/8 * integral_R p_(a,c)(y)*A_epsilon(t-y) dy.
```

The average is absolutely integrable and the original zero contributions
form a convergent series. These facts are part of the checked chain. The
factor `1/8` accounts for the half-normalized kernel mixture, the original
paired contribution and the factor two in the canonical symmetric Gaussian
normalization. `gaussianAtom_zero_eq` proves the exact cancellation of the
evaluation abscissa inside the complex Gaussian argument.

This identity and convergence hold for every positive scale split and every
`sigma>=1/2`. They require no lower bound on `B` in terms of `1-sigma`.
Positivity of the density is established for `sigma>1/2`.

## The previous allowance now bounds an arithmetic expression

On `sigma_H=1-m(H)`, the existing
[uniform zero-side allowance](gaussian-fermi-zero-tail.md) gives

```text
-K*log(H+2)/sqrt(H)
  <= sqrt(pi/b)/8 * integral_R p_(2*sigma_H-1,c)(y)*A_epsilon(t-y) dy,
```

for `H>=1`, `b,c>0`, `m(H)^2<=b+c<=1` and `2*abs(t)<=H`.
`exists_uniform_arithmetic_average_lower_bound` proves this with one
constant independent of height, ordinate and the positive scale split.
Its left-hand allowance tends to zero by the previous checked rate theorem.

This is positivity up to a vanishing allowance for a specified smoothed
arithmetic expression. It does not prove pointwise positivity of every
Gaussian test, the RH-equivalent condition, or exclude a further zero.

## Subsequent evaluation and remaining obligations

The identification and the infinite zero-side interchange are closed
in this averaged form. The subsequent
[prime and phase continuation](gaussian-fermi-prime-phase-budget.md)
now evaluates the prime average term by term using the exact characteristic
function. Its literal prime term is

```text
sum_n vonMangoldt(n)/sqrt(n) * h_(a,B)(log(n))*cos(t*log(n)).
```

Its exchange with the averaging integral, convergence and normalization
are proved in `GaussianFermiPrimeFormula`. The Gaussian scales recombine
exactly into `B=b+c`. `GaussianFermiPoleFormula` evaluates the pole and
constant terms and proves gamma-average integrability and independence
from the auxiliary positive split. `GaussianFermiPhaseBudget` uses the
favorable prime sign for every admissible finite cosine test while
retaining a selected finite set of zeros and paying for the full tail.

The [gamma continuation](gaussian-fermi-gamma-bound.md) bounds the actual
digamma average explicitly using the exact second spectral moment. It
inserts a quarter-logarithm upper bound, uniform over admissible shrinking
scales, into the general selected-zero budget. The
[resonant continuation](gaussian-fermi-resonant-budget.md) proves a
Gaussian lower bound for the distinct target pair and an upper envelope
for every pole frequency. The
[independent Gaussian comparison](gaussian-fermi-zero-free-region.md)
now rules out the eventual edge width `3/(20*log(abs(t)))`, with every
height cost discharged. The finite threshold has not been numerically
evaluated.
The external numerical region, the independent signed ordinary-prime-tail
bound in the original RH reduction, and RH remain open.

## Local verification of the mixture checkpoint

All local gates passed: strict direct elaboration of all four modules,
focused builds, the full warning-as-error build (10,123 jobs), all 14
declaration linters, 19 terminal axiom audits, the whole-project declaration
lint, the compiled-environment soundness generator, and source/whitespace
checks. The inventory contains 1,276 modules, zero project axioms and zero
declarations depending on placeholders. All audited theorems use only
`propext`, `Classical.choice` and `Quot.sound`. README links, table formatting
and the 500-character direction limit also pass. These are local validation results; remote CI is checked separately on the exact commit.

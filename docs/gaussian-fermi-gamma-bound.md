# Explicit gamma bounds for the general Fermi phase budget

The gamma term in the [general selected-zero budget](gaussian-fermi-prime-phase-budget.md)
now has an unconditional explicit upper bound. Its logarithmic coefficient
is `1/4`, and its remaining upper allowance decreases with the evaluation
ordinate, uniformly as the Gaussian scale shrinks. The phase-budget theorem
uses this bound directly; it no longer contains an unevaluated gamma term.

Three root-imported modules implement the result:

- [GaussianFermiSpectralMoment](../RiemannGaussian/GaussianFermiSpectralMoment.lean)
  proves the exact second spectral moment and the first absolute-moment bound.
- [GaussianDigammaLogEnvelope](../RiemannGaussian/GaussianDigammaLogEnvelope.lean)
  proves the actual digamma logarithmic tangent and integrates it against
  each translated Gaussian with exact mass and first moment.
- [GaussianFermiGammaBound](../RiemannGaussian/GaussianFermiGammaBound.lean)
  proves the normalized gamma bounds and inserts them into the actual
  finite-phase selected-zero theorem.

At this gamma checkpoint the numerical region was unchanged. The
[subsequent resonant comparison](gaussian-fermi-resonant-budget.md) now
gives a Gaussian lower bound for the target pair and an upper envelope
for the poles. The [independent Gaussian comparison](gaussian-fermi-zero-free-region.md)
then proves the stronger eventual width `3/(20*log(abs(t)))`, with all
height costs discharged. Its threshold is existential, not numerically
evaluated. The external `4.896` theorem,
the independent ordinary-prime-tail bound in the original RH reduction,
and RH remain unproved here.

## Positivity converts characteristic curvature into a spectral moment

The original centered signal and spectral density are

```text
h_(a,c)(u) = exp(-c*u^2-(a/2)*u)/(1+exp(-a*u)),
p_(a,c)(y) = Re(integral_R h_(a,c)(u)*exp(-i*y*u) du)/pi.
```

For `a,c>0`, the previous chain proves `p>=0`, `integral p=1` and

```text
integral_R p(y)*exp(i*y*u) dy = 2*h_(a,c)(u).
```

The new time-side computation gives

```text
h(0)=1/2, h'(0)=0, h''(0)=-c-a^2/8,
(1-2*h(u))/u^2 -> c+a^2/8 as u -> 0, u != 0.
```

`tendsto_characteristic_deficit` proves the quadratic limit using the
already proved actual time derivatives and L'Hopital's rule. It does not
differentiate a Fourier integral under an assumed moment hypothesis.

Instead, use positive squared-sinc approximants:

```text
M_x(y) = p(y)*y^2*sinc(y*x/2)^2,
integral_R M_x(y) dy = 2*(1-2*h(x))/x^2   (x != 0).
```

The sinc identity evaluates each approximant by the exact characteristic
function. Each is integrable; each is nonnegative; and as `x -> 0` they
converge pointwise to `p(y)*y^2`. Fatou first proves that this true second
moment is finite. Only then does dominated convergence, using `abs(sinc)<=1`,
recover the exact value:

```text
integral_R y^2*p_(a,c)(y) dy = 2*c+a^2/4.
```

`integral_density_secondMoment` proves this for every positive `a,c`.
`integral_density_abs_le_sqrt` combines it with unit mass to prove

```text
integral_R abs(y)*p_(a,c)(y) dy <= sqrt(2*c+a^2/4).
```

This is the useful consequence of retaining spectral positivity. The
averaging spread stays bounded as `c` decreases to zero, without the
inverse-scale loss of a coarse absolute Fourier estimate. The theorem
states a second moment; a separate mean or variance theorem is not claimed.

## Keep the comparison center through the logarithmic estimate

Let the actual Archimedean density be

```text
psi_R(r) = Re digamma(1/4+i*r/2).
```

The existing horizontal completion comparison gives

```text
psi_R(r) <= log(5/4+abs(r)).
```

`archimedeanDensity_le_log` proves this with the positive reciprocal term
and its sign accounted for. Conjugation also proves that this real density
is even, so `gaussianDigammaIntegral_eq_full` identifies the original
half-line symmetric expression with one full translated Gaussian integral:

```text
gaussianDigammaIntegral(epsilon,v)
  = (1/pi)*integral_R exp(-epsilon*(r-v)^2)*psi_R(r) dr.
```

Set `A=5/4+abs(t)`. Keep the comparison ordinate `t` while the Gaussian is
centered at `v=t-y`. The logarithm tangent and triangle inequality give

```text
psi_R(r) <= log(A) + (abs(r-(t-y))+abs(y))/A.
```

This preserves the two displacements until their respective averages are
taken. The Gaussian has exact full mass `sqrt(pi/epsilon)` and exact
absolute first moment `1/epsilon`. Both integrability and evaluation are
proved, so integration gives

```text
gaussianDigammaIntegral(epsilon,t-y)
  <= (log(A)+abs(y)/A)/sqrt(pi*epsilon) + 1/(pi*epsilon*A).
```

All bounds are on the actual real digamma expression. No unproved
asymptotic expansion or gamma-growth constant is supplied as a hypothesis.

## Normalize and average using the actual spectral moment

For `b,c>0`, retain the original gamma average

```text
D_(a;b,c)(t) = sqrt(pi/b)/8 * integral_R p_(a,c)(y)*
                gaussianDigammaIntegral(1/(4*b),t-y) dy.
```

The full average is already proved integrable. Its exact normalization and
the spectral moment yield `digammaAverage_le_quarter_log`:

```text
D_(a;b,c)(t)
  <= log(A)/4
       + (sqrt(2*c+a^2/4)/4 + 1/(4*sqrt(pi/(4*b))))/A.
```

The preceding `digammaAverage_le_moment` retains the actual first absolute
moment before replacing it by the square-root estimate. Both explicit
positive scales remain available in the sharper bound.

For every `0<a<=1` and `b,c>0` with `b+c<=1`, the simpler uniform theorem is

```text
D_(a;b,c)(t) <= log(5/4+abs(t))/4 + 7/(8*(5/4+abs(t))).
```

At `t!=0`, `digammaAverage_le_log_abs` also gives

```text
D_(a;b,c)(t) <= log(abs(t))/4 + 19/(16*abs(t)).
```

These are upper bounds. They do not assert a two-sided asymptotic equality
between `D(t)` and `log(abs(t))/4`. Their errors remain uniform over all
positive admissible splits, including moving total scales tending to zero.

## The actual selected-zero budget now contains explicit gamma costs

Use `sigma=1-m(H)` from the [proved zero-free margin](zeta-pole-reserve-bootstrap.md),
`B=b+c`, and the previous reflected contribution `Q_(B,sigma,t)(rho)` and
pole pair `Pole_(B,sigma)(t)`. For any finite phase family with nonnegative
weights and a nonnegative cosine test, and any finite set `S` of genuine
zeros in the height band, `selected_zero_phase_log_budget` proves

```text
sum_j w_j * sum_(rho in S) Q_(B,sigma,omega_j*t)(rho)
  <= sum_j w_j * [Pole_(B,sigma)(omega_j*t)
                  + (log(5/4+abs(omega_j*t))-log(pi))/4
                  + 7/(8*(5/4+abs(omega_j*t)))]
       + (sum_j w_j)*E(B,H).
```

The hypotheses are `H>=1`, `b,c>0`, `m(H)^2<=B<=1`,
`2*abs(omega_j*t)<=H`, and `abs(Im(rho))<=H` for each retained zero.
Every analytic multiplicity remains in `Q`. The entire prime series has
the favorable sign by the previous exact phase theorem. The whole omitted
outside divisor is paid for by the existing allowance
`E(B,H)<=K*log(H+2)/sqrt(H)`.

The former gamma-estimation obligation is discharged in this budget.
The [subsequent resonant comparison](gaussian-fermi-resonant-budget.md)
now supplies Gaussian target-pair and pole bounds with their exact signed
remainders retained upstream. The resulting necessary inequality for
every genuine right-half zero has no unevaluated Fermi or gamma term.
The [independent Gaussian surplus](gaussian-fermi-zero-free-region.md)
now proves this inequality impossible in a wider eventual edge region,
with exact coefficient `3/20`. The height threshold is not numerically
evaluated.

## Local verification of the gamma checkpoint

All local gates passed: strict direct elaboration of the three new modules,
the focused build (4,617 jobs), the full warning-as-error build (10,130
jobs), all 14 declaration linters, 20 terminal axiom audits, the
whole-project declaration lint and the compiled-environment soundness
generator. That checkpoint's inventory contains 1,283 modules and 24,809 theorems, with
zero project axioms and zero placeholder-dependent declarations. The
audited theorems use only `propext`, `Classical.choice` and `Quot.sound`.
Source, whitespace, README links and table formatting pass; Current
Direction is one paragraph of 415 characters. These are local validation results; remote CI is checked separately on the exact commit.

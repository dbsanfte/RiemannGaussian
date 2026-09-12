# Coupled prime phases in the actual vertical zeta boundary

The terminal theorem
[`ZetaSechPhaseFamily.right_boundary_integral_le_exact`](../RiemannGaussian/ZetaSechPhaseFamily.lean)
controls the **entire common right-boundary integral**, for every eligible
summable phase family. It retains the phase cancellation before estimating
individual logarithms. This is an actual zeta theorem with all convergence
and integration hypotheses discharged on `sigma>1`.

Put

```text
w(u) = 1/(2*cosh(u)^2),
M(sigma,t,b) = integral_Real w(u)*log(norm(zeta(sigma+i*(t+b*u)))) du,
K(x) = sum_n a_n*cos(omega_n*x).
```

Assume `a_n>=0`, `sum_n a_n` converges, `K(x)>=0` for every real `x`,
and `omega_0=0`. For every `sigma>1` and arbitrary real `t,b`, Lean proves

```text
-integral_Real w(u)*sum_(n!=0) a_n*
    log(norm(zeta(sigma+i*(omega_n*t+b*u)))) du
  <= a_0*M(sigma,0,b)
  <= a_0*log(norm(zeta(sigma))).
```

The first bound keeps the exact positive averaged constant-phase mass.
The second is `right_boundary_integral_le`. The theorem works with finite
or infinite support and arbitrary real frequencies. It requires neither
a frequency lower bound nor a summable logarithmic frequency cost; those
are additional requirements in other parts of the zero detector.

This formalizes the classical coupled right-boundary mechanism used in
[Yang, section 4, equation (4.64)](https://arxiv.org/html/2301.03165v2).
It does not formalize that paper's whole zero-free theorem or certify
historical novelty. The countable-family theorem and exact averaged mass
are retained as reusable interfaces.

## Exact complex Fourier transform

[SechVerticalFourier](../RiemannGaussian/SechVerticalFourier.lean)
uses the original logistic survival coordinate
`S(u)=exp(-2*u)/(1+exp(-2*u))`. Its derivative is `-w(u)`, and it is
injective with image exactly `(0,1)`. The change of variables gives

```text
integral_Real w(u)*exp(i*v*u) du
  = beta(1-i*v/2,1+i*v/2)
  = norm(Gamma(1+i*v/2))^2.
```

The full complex integral is absolutely integrable. The beta--gamma
identity and gamma conjugation prove the norm-square expression; the
nonvanishing of gamma on positive real part proves strict positivity.
Define this real multiplier as `A(v)`. Then Lean proves

```text
0 < A(v) <= 1,
integral_Real w(u)*sin(v*u) du = 0,
integral_Real w(u)*cos(x+v*u) du = A(v)*cos(x).
```

Thus the odd part cancels exactly and the original cosine phase remains.
No absolute-value replacement is made before this cancellation.

## Actual logarithmic Euler expansion

[ZetaLogPrimeSeries](../RiemannGaussian/ZetaLogPrimeSeries.lean) retains
Mathlib's exact exponential of the complete complex Euler logarithm,
then takes its real part to recover `log(norm(zeta(s)))`. This avoids
choosing a branch of the complex logarithm. For `sigma>1`, set

```text
c_n = Lambda(n)/log(n),
q_n(sigma) = c_n*exp(-sigma*log(n)).
```

The zero and unit coefficients are zero. Lean proves `0<=c_n<=1`,
absolute summability and the genuine sum identities

```text
log(norm(zeta(sigma+i*t))) = sum_n q_n(sigma)*cos(t*log(n)),
log(norm(zeta(sigma))) = sum_n q_n(sigma),
abs(log(norm(zeta(sigma+i*t)))) <= log(norm(zeta(sigma))).
```

All prime-power amplitudes and their original phases remain explicit.

## Keep the common vertical variable through both sums

[ZetaSechPrimeBoundary](../RiemannGaussian/ZetaSechPrimeBoundary.lean)
proves that the full signed mean is genuinely absolutely integrable and
exchanges its integral with the Euler series by dominated convergence:

```text
d_n(sigma,b) = q_n(sigma)*A(b*log(n)),
M(sigma,t,b) = sum_n d_n(sigma,b)*cos(t*log(n)),
0 <= d_n(sigma,b) <= q_n(sigma).
```

The multiplier depends on the prime power and common averaging scale,
not on the phase-channel index. Consequently the exact double-sum theorem
[`hasSum_arithmetic`](../RiemannGaussian/ZetaSechPhaseFamily.lean) gives

```text
sum_j a_j*M(sigma,omega_j*t,b)
  = sum_n d_n(sigma,b)*K(t*log(n))
  >= 0.
```

Joint absolute summability is proved before commuting the two series.
The entire countable logarithm is also proved absolutely integrable, and
`integral_sum_eq` identifies its actual common integral with the channel
sum. Removing the constant channel from this nonnegative total gives
the terminal inequality. `integrable_nonconstant` and
`integral_nonconstant_eq` establish the same obligations for the literal
nonconstant integral used there.

## What remains before a larger zero-free region

The [signed left-window bound](zeta-sech-euler-bound.md) and this complete
right-boundary comparison are now available. The
[complete finite strip identity](zeta-strip-cotangent-source.md) now also
retains every actual zero multiplicity and rational pole correction. Its
selected term has a proved cotangent limit, and the signed projection
has a uniform upper envelope through both infinite strip ends. The
[actual boundary constraint](zeta-strip-boundary-constraint.md) now proves
the needed radial limit and complete physical integral inequality. The
right logarithm remains fully signed, and arbitrary finite negative depth
is retained on the left. The
[complete strip family budget](zeta-strip-phase-budget.md) now applies the
sharp arithmetic estimates and rational normalization correction. It
preserves the constant-channel right prime cost, proves an elementary
upper bound, and derives actual finite-height closed-edge nonvanishing
from a strict explicit surplus. Global integrability of the unclipped
left negative part is not assumed or asserted.

These boundary theorems alone do not enlarge the
[current proved region](zeta-log-log-zero-free.md). Its thresholds remain
coefficient-dependent and unevaluated. A world-best comparison requires
explicit matching height ranges against the applicable published regions.
The independent ordinary-prime lower bound and RH remain open.

## Previous coupled-boundary checkpoint

The four new modules provide 48 public theorems. All 31 affected modules
pass direct elaboration with warnings treated as errors. The focused build
passes 4,975 jobs and the full build passes 10,303 jobs. Root verbose lint
reports zero errors across 19,319 declarations and 11,444 generated
declarations, with all 14 linters; the whole-project linter also passes.
All 220 public theorems in the affected modules have explicit transitive
axiom audits using only `propext`, `Classical.choice` and `Quot.sound`.

The compiled inventory contains 1,456 project modules, 30,798 declarations
and 27,010 theorems, with no project axioms or placeholder dependencies.
`rhImplied` remains false. These counts record the preceding coupled-boundary slice;
the subsequent [strip-source slice](zeta-strip-cotangent-source.md) adds
the actual finite divisor, cotangent source and boundary domination.

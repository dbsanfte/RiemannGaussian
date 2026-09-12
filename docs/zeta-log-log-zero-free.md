# The current proved log-log zero-free region

For every fixed `0<A<22*pi/(1525*log(2))`, Lean proves a finite threshold
`T(A)>=2` such that every actual nontrivial zeta zero `rho=beta+i*t` with
`abs(t)>=T(A)` satisfies

```text
A*log(log(abs(t)))/log(abs(t)) < beta
  < 1-A*log(log(abs(t)))/log(abs(t)).
```

[ZetaLogLogZeroFree.exists_eventual_strip](../RiemannGaussian/ZetaLogLogZeroFree.lean#L62)
proves both edges. The module also proves literal zeta nonvanishing on
the closed right edge and a common margin for the complete divisor below
every sufficiently large height. All analytic and arithmetic premises
are discharged. **The threshold depends on the coefficient and has not
been numerically evaluated.** The coefficient is a proved sufficient
range, with no claim of optimality or a world-best region.

## The complete general phase-family contradiction

The [general countable-family theorem](zeta-angular-phase-family.md)
retains the actual selected source, multiplicity, full radius, radial
correction and every frequency. Write

```text
H(t)=abs(t)+2, L(t)=log(H(t)), ell(t)=log(L(t)),
k(t)=floor(ell(t)/b), b>log(2),
alpha_k=1/(2^(k+2)-2), delta_k=(k+2)*alpha_k,
u(t)=C*ell(t)/L(t), x(t)=r*u(t).
```

For every eligible family, with `W=sum_(n!=0) a_n`, the complete cost tends
to `2*W*C*b/pi`. A zero within margin `u` forces that cost to be at least
`Gamma(r)=a_1/(r+1)-a_0/r`. The logarithmic frequency moment and exact
radial correction vanish on the same moving-order schedule. The exact
optimal center shift at fixed weights is also proved symbolically.

The [existing exact contact family](../RiemannGaussian/ZetaExactPhaseAngularExclusion.lean)
has `W<=61/100` and `Gamma(13/4)>=11/625`. Thus
`1525*C*log(2)<22*pi` supplies a fixed `b>log(2)` for which the complete
cost is eventually below its source. All geometry holds eventually on
the same schedule, giving a contradiction. No new coefficient search or
assumed prime bound enters this zero-free theorem.

The moving-order argument uses the proved bounds

```text
p=log(2)/b<1,
1/delta_(k(t)) <= 4*L(t)^p,
ell(t)/(k(t)+2) -> b,
ell(t)^n/(L(t)*delta_(k(t))) -> 0  for every fixed natural n.
```

See [LogLogDerivativeSchedule](../RiemannGaussian/LogLogDerivativeSchedule.lean),
[the complete family limit](../RiemannGaussian/ZetaAngularPhaseLimit.lean)
and [actual general exclusion](../RiemannGaussian/ZetaAngularPhaseExclusion.lean).
Historical three-channel formulas and their earlier coefficient range
remain in [the signed-angular slice](zeta-signed-angular-zero-free.md).

## Ordinary heights and complete bands

For any `A<C`, the ordinary width is eventually bounded by the smoothed
width for `C`. Choose `A<C<22*pi/(1525*log(2))` to retain the full open
coefficient range. Reflection gives the other strip edge.

The ordinary width is positive and antitone for `H>=exp(exp(1))`, and
tends to zero. That elementary monotonicity height is not the zero-exclusion
threshold. The [complete-band theorem](zero-free-region-transport.md)
combines the eventual result with the actual finite lower divisor to
cover every zero below each sufficiently large height. For fixed `A>0`,
the width eventually exceeds every fixed `B/log(H)`; this does not assert
one common threshold for all `B`.

## Arithmetic consequence and the remaining prime bound

For `H=2*abs(y)+3`, every eligible coefficient gives the actual quotient
`zeta(s)/zeta(2*s)` the closed analytic disc centered at `3/2+i*y` of radius

```text
R_A(y)=1+A*log(log(H))/(2*log(H)).
```

Both poles and all doubled-denominator zeros are excluded first.
[ZetaSquarefreeLogLogRadius](../RiemannGaussian/ZetaSquarefreeLogLogRadius.lean)
proves actual Cauchy bounds for every fixed valid squarefree mark, finite
excluded prime set, complex polynomial and moment order, keeping the
signed first and doubled prime harmonics in the phase envelope. For fixed
`0<=A<B<22*pi/(1525*log(2))`, sufficiently large `abs(y)` gives
`R_A(y)<R_B(y)` and decay of the full marked response multiplied by
`R_A(y)^N` as the moment order grows.

Constants and the phase envelope may grow with radius. No uniform estimate
for growing prime sets is asserted. The separate ordinary-prime source
still needs an independent cofinal lower bound above `-1` by a fixed
positive gap. Stronger fixed-mark squarefree decay does not prove that
bound, and the remaining interior strip is unresolved. RH remains open.

## Current analytic improvement

The [exact Gaussian correction](zeta-angular-phase-family.md) now saves
at least twelve logarithmic units per nonconstant channel in the actual
finite-height family budget. The [direct Euler truncation](zeta-direct-euler-truncation.md)
has a proved height-uniform remainder without the eta denominator. It now
propagates through the existing ordinary Dirichlet block bound, the actual
Gaussian disc and every eligible phase family. The exact additional budget
saving is `2*W*log(4/delta_k)/(pi*delta_k)`.

The [signed vertical detector](zeta-sech-euler-bound.md) now also uses its
exact mass and first moment, with a controlled pole correction. The
[coupled right boundary](zeta-sech-phase-boundary.md) now preserves the
complete prime kernel for every eligible summable phase family and charges
only the constant channel. The [complete finite strip divisor](zeta-strip-cotangent-source.md)
now preserves every actual multiplicity and pole correction; its selected
cotangent source has a proved limit. A uniform signed envelope controls
the infinite ends. The [actual boundary-limit inequality](zeta-strip-boundary-constraint.md)
is now proved, retaining arbitrary left negative depth and the full right
sign. The [complete strip phase-family budget](zeta-strip-phase-budget.md)
now applies the sharp arithmetic profiles and rational correction, and
proves an elementary finite-height zero-exclusion criterion. A strict
cost surplus on explicit height ranges remains to be established.
These improvements have not yet changed the region stated here.

The higher-derivative and Littlewood strategy is classical. The
[published-region survey](zero-free-region-transport.md) records external
benchmarks. Reproducing a published analytic argument in Lean is a way
to strengthen the inputs, not permission to assume its final region.
All world-best comparisons must use explicit matching height ranges.

## Original schedule-slice validation

All eight modules pass direct elaboration with warnings treated as
errors. The focused build passes 4,893 jobs and the full library passes
10,262 jobs. Whole-project declaration lint and verbose lint of the
eight modules pass. All 52 new public theorems have explicit axiom
audits using only `propext`, `Classical.choice` and `Quot.sound`.

The strict inventory contains 1,415 compiled project modules and 26,528
project theorems, with no project axioms or placeholder-dependent
declarations. It continues to report `rhImplied = false`. The source
scan covers 1,558 Lean files. The README and related documentation pass
673 local-link checks; Current Direction remains one 419-character
paragraph at that checkpoint.

Those counts record the original eight-module schedule slice. The
subsequent sharp derivative improvement and revalidation of the complete
chain are recorded in the [full-radius slice](zeta-full-radius-zero-free.md) and the subsequent
[signed angular slice](zeta-signed-angular-zero-free.md).

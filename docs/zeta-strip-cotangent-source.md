# Complete strip divisor, selected cotangent source and signed domination

The actual zeta source now has a proved strip-coordinate construction.
The terminal finite inequality is
[`ZetaStripCotangentSource.normalized_selected_constraint`](../RiemannGaussian/ZetaStripCotangentSource.lean).
Its selected term has an exact positive cotangent limit, and the signed
boundary integrand has a uniform upper envelope through both infinite
strip ends. The subsequent
[actual boundary-limit inequality](zeta-strip-boundary-constraint.md)
is now proved with arbitrary left negative depth and the full right sign.
These results have not yet enlarged the displayed zero-free region.

## The entire strip, with multiplicities preserved

For a complex center `c` and half-width `eta>0`, define

```text
phi(w) = c + (4*eta/pi)*arctan(w),
a(z) = tan(pi*(z-c)/(4*eta)).
```

[AnalyticStripMap](../RiemannGaussian/AnalyticStripMap.lean) proves that
`phi` maps the entire open unit disc bijectively onto
`abs(Re(z)-Re(c))<eta`. Both inverse identities, the full image, branch
domain, analyticity and derivative are proved:

```text
phi'(w) = (4*eta/pi)/(1+w^2) != 0,
analyticOrderAt(f composed with phi,w) = analyticOrderAt(f,phi(w)).
```

The map preserves the side of the center:
`Re(phi(w))<Re(c)` exactly when `Re(w)<0`. Its Cayley coordinate has
positive real part inside the disc, so the logarithm never meets its
branch cut there. A trigonometric norm-square identity proves that the
inverse stays inside the disc even at arbitrarily large physical heights:

```text
normSq(cos(z))-normSq(sin(z)) = cos(2*Re(z)).
```

[AnalyticStripDisc](../RiemannGaussian/AnalyticStripDisc.lean) transfers
the existing complete finite divisor identity to every radius `0<r<1`.
It constructs zero-free circles approaching one using only analyticity
on the open disc. The singular ends `w=+i,-i` are not treated as regular
points. Every fixed physical strip point enters the finite windows
eventually.

## Exact identity for actual zeta

For `Re(c)>1`, `0<eta<Re(c)`, use the actual carrier

```text
g(s) = zeta_1(s)/(s+1),
     = (s-1)*zeta(s)/(s+1)  away from s=1,
F(w) = g(phi(w)).
```

The filled value at `s=1` is nonzero, so pole clearing introduces no
spurious zero. Let `D_r(w)` be the complete divisor of `F` on `abs(w)<r`,
and retain the coupled complex kernel

```text
K_r(w) = -1/w + conjugate(w)/r^2.
```

The [actual complex identity](../RiemannGaussian/ZetaStripDisc.lean)
states, on every eligible zero-free boundary circle,

```text
(4*eta/pi)*(zeta'/zeta(c)+1/(c-1)-1/(c+1))
  = M_r(F) + sum_w D_r(w)*K_r(w),
```

where `M_r` is the existing full complex first boundary moment of
`log(norm(F))`. Every sum here is the complete finite divisor, with
genuine analytic hypotheses proved for actual zeta.

For every enclosed nontrivial zero `rho`, its coordinate `a(rho)` has
divisor weight exactly `m_rho`, the original analytic multiplicity.
Every nonzero divisor term lies strictly left of the coordinate center.
Consequently

```text
Re(D_r(w)*K_r(w)) >= 0
```

for every term. The exact complex sum remains available alongside this
projection. Selecting any zero gives the literal finite inequality

```text
-Re(zeta'/zeta(c)) + m_rho*pi/(4*eta)*Re(K_r(a(rho)))
  <= pi/(4*eta)*Re(-M_r(F)) + Re(1/(c-1)-1/(c+1)).
```

The rational correction is retained exactly.

## Exact selected source limit

[ZetaStripCotangentSource](../RiemannGaussian/ZetaStripCotangentSource.lean)
proves the complex double-angle identity with its zero denominator
excluded, then the exact real projection

```text
Re(K_1(tan(q))) = Re(-2*cot(2*q)).
```

For an actual zero `rho=beta+i*t` in the strip and `Im(c)=t`, set
`d=Re(c)-beta`. Then `0<d<eta`, and along every `r_n -> 1`,

```text
m_rho*pi/(4*eta)*Re(K_(r_n)(a(rho)))
  -> m_rho*pi/(2*eta)*cot(pi*d/(2*eta)) > 0.
```

The full analytic multiplicity and the scale factor are proved. This
passes **only the selected term** to the limit. Since all other finite
terms are nonnegative, selected-zero exclusion can use a boundary upper
inequality without first interchanging the limit with the whole divisor
sum. No such infinite-divisor interchange is asserted here.

## The real projection controls the infinite ends

The imaginary part of `arctan(w)` grows without bound as `w` approaches
either infinite strip end. The original real projection supplies the
needed vanishing factor. [AnalyticStripGrowth](../RiemannGaussian/AnalyticStripGrowth.lean)
proves, throughout `abs(w)<1`,

```text
Im(arctan(w)) = -log(norm((1+i*w)/(1-i*w)))/2,
abs(Re(w))*abs(Im(arctan(w))) <= 1,
abs(Re(w))*abs(Im(phi(w))-Im(c)) <= 4*eta/pi.
```

The proof retains numerator and denominator distance information in the
Cayley logarithm. Both are bounded below by `abs(Re(w))`, giving the
coupled estimate even arbitrarily close to the singular ends.

[ZetaStripBoundaryEnvelope](../RiemannGaussian/ZetaStripBoundaryEnvelope.lean)
combines this with actual zeta growth and the full reciprocal Euler
series. Assume also

```text
1/2 <= Re(c)-eta,  Re(c)+eta <= 3/2.
```

Then the entire signed projection, including interior zero points, obeys

```text
-Re(w)*log(norm(F(w))) <= max(C_left,C_right),
C_left  = 52 + 2*abs(Im(c)) + 8*eta/pi,
C_right = (1+1/(Re(c)-1))*(1+2/(Re(c)-1)).
```

This is a **one-sided domination theorem**. Negative logarithmic
excursions on the left remain favorable. The finite exact identities use
zero-free circles, and no singular logarithmic derivative is evaluated
at an actual zero. The coarse envelope is for proving a limit inequality;
it is not substituted as the final sharp zero-exclusion allowance.

## The proved boundary limit and remaining estimates

The subsequent [boundary constraint](zeta-strip-boundary-constraint.md)
proves the exact vertical parametrization, Jacobian and actual dominated
radial limit. It retains arbitrary negative depth on the left and the
entire signed right logarithm. The uniform envelope above supplies the
domination input. The subsequent
[complete phase-family budget](zeta-strip-phase-budget.md) now applies the
sharp Euler profile and coupled prime estimate with the exact scale and
rational correction. Its elementary source bound and finite-height
nonvanishing criterion are proved for every eligible countable family.

Global negative-part integrability of the unclipped left logarithm inside
the zero strip has not been proved. The boundary constraint establishes
the needed one-sided inequality at every finite clipping depth. Full
unclipped boundary convergence is not asserted or needed by the new budget.
A strict surplus on explicit height ranges sufficient to improve the
displayed region remains to be proved.

The strip and cotangent mechanisms are classical. These modules give a
bottom-up formalization using the repository's complete disc formula;
they do not establish historical novelty or reproduce optimized published
constants. The [current zero-free region](zeta-log-log-zero-free.md) is
unchanged, with unevaluated coefficient-dependent thresholds. A world-best
comparison needs explicit matching height ranges. The independent
ordinary-prime lower bound and RH remain open.

## Validation at the original six-module checkpoint

The six new modules provide 71 public theorems. All 37 affected modules
pass direct elaboration with warnings treated as errors. The focused build
passes 4,982 jobs and the full build passes 10,309 jobs. Root verbose lint
reports zero errors across 19,397 declarations and 11,477 generated
declarations, with all 14 linters. The whole-project linter passes.
All 291 public theorems in the affected modules have explicit transitive
axiom audits using only `propext`, `Classical.choice` and `Quot.sound`.

The compiled inventory contains 1,462 project modules, 30,909 declarations
and 27,114 theorems, with no project axioms or placeholder dependencies.
`rhImplied` remains false. These counts record the original six-module
checkpoint.

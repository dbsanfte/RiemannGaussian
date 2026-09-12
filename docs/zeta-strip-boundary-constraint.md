# Actual strip zero constraint with complete vertical boundaries

[`ZetaStripBoundaryConstraint.selected_zero_constraint_density`](../RiemannGaussian/ZetaStripBoundaryConstraint.lean)
proves the boundary-limit inequality for the actual zeta carrier. The
selected zero keeps its full multiplicity and positive cotangent source.
The two physical boundary integrals have their exact density, signs and
normalization. Their integrability and all radial limit exchanges are
proved. This closes the analytic limit obligation left by the
[complete finite strip construction](zeta-strip-cotangent-source.md).

The [complete phase-family budget](zeta-strip-phase-budget.md) now applies
the sharp Euler profile and coupled prime comparison to these actual
integrals, including the rational normalization correction. Its elementary
finite-height nonvanishing criterion is proved; the displayed region is
unchanged pending a strict surplus on larger explicit height ranges.

## The actual theorem

Let `rho=beta+i*t` be a nontrivial zeta zero of analytic multiplicity `m`.
Take a safe center `c` and a strip half-width `eta` satisfying

```text
1 < Re(c),       eta > 0,
1/2 <= Re(c)-eta,       Re(c)+eta <= 3/2,
abs(beta-Re(c)) < eta,  Im(c)=t.
```

Set

```text
g(s) = ((s-1)/(s+1))*zeta(s), continued at s=1,
w(u) = 1/(2*cosh(u)^2),
b = 2*eta/pi,
L_M(z) = log(max(norm(z),exp(-M))),    M >= 0,
d = Re(c)-beta,                     0 < d < eta.
```

For **every** finite depth `M>=0`, Lean proves

```text
-Re(zeta'/zeta(c)) + m*pi/(2*eta)*cot(pi*d/(2*eta))
 <= (1/(2*eta)) * (
      integral_R w(u)*L_M(g(c-eta+i*b*u)) du
      - integral_R w(u)*log(norm(g(c+eta+i*b*u))) du)
    + Re(1/(c-1)-1/(c+1)).
```

The cotangent term is strictly positive by the upstream
[`selected_source_pos`](../RiemannGaussian/ZetaStripCotangentSource.lean).
Both integrals are genuinely integrable:
[`integrable_left_density`](../RiemannGaussian/ZetaStripBoundaryConstraint.lean)
and [`integrable_right_density`](../RiemannGaussian/ZetaStripBoundaryConstraint.lean).
No hypothesis assumes the missing arithmetic bound or a boundary limit.

[`logDeriv_le_boundary`](../RiemannGaussian/ZetaStripBoundaryConstraint.lean)
proves the same inequality without the selected cotangent term for every
eligible center, without assuming a zero at that ordinate. These are the
unmarked phase channels needed beside the selected-zero channel in a
full-family argument. Their complete finite divisors also have favorable
sign; no zero is invented at a rescaled frequency.

## Exact boundary geometry and Jacobian

[`AnalyticStripBoundary`](../RiemannGaussian/AnalyticStripBoundary.lean)
defines the original complex boundary points

```text
w_plus(u)  =  sech(u) + i*tanh(u),
w_minus(u) = -sech(u) + i*tanh(u).
```

Their norms equal one. Their Cayley coordinates are exactly
`i*exp(-u)` and `-i*exp(-u)`, respectively, so the principal logarithm
has the correct branch at every finite `u`. Consequently

```text
phi(w_plus(u))  = c+eta+i*b*u,
phi(w_minus(u)) = c-eta+i*b*u.
```

The right angle is `theta(u)=arctan(sinh(u))`; it increases bijectively
from `-pi/2` to `pi/2` and has derivative `sech(u)`. The left angle is
`pi-theta(u)`, with the opposite orientation. The complete integral
change of variables is proved in
[`AnalyticStripBoundaryIntegral`](../RiemannGaussian/AnalyticStripBoundaryIntegral.lean),
including integrability transport for each arc separately and the exact
identity `integral_R sech(u) du=pi`.

Multiplying the angular Jacobian by the original real projection gives
`sech(u)^2`. Combining it with the disc moment normalization and the
physical derivative scale gives exactly the `1/(2*eta)` factor against
the mass-one density `w` above.

## Retain negative depth while crossing boundary zeros

[`ClippedLogNorm`](../RiemannGaussian/ClippedLogNorm.lean) proves that
`L_M` is continuous through zero, bounded below by `-M`, and agrees with
the original signed logarithm wherever `norm(z)>=exp(-M)`. Away from
zeros it majorizes the original logarithm. Any nonnegative upper profile
for the original logarithm also bounds `L_M`.

Increasing `M` retains more negative information. The actual full
integral theorem
[`boundary_antitone_depth`](../RiemannGaussian/ZetaStripBoundaryConstraint.lean)
proves that the resulting boundary allowance can only decrease. Thus
clipping is an explicitly controlled downstream estimate; the full
complex finite divisor identity remains available upstream. There is no
claim that the negative logarithm is absent or unhelpful.

The right logarithm is never clipped. The entire right semicircle stays
in the nonzero Euler half-plane. This preserves the sign needed by the
[full phase-family prime comparison](zeta-sech-phase-boundary.md).

## Genuine domination at the infinite ends

For radial points `r*w_plus(u)` and `r*w_minus(u)`, `0<=r<1`, the
original signed projection is retained before multiplication by the
angular Jacobian. The upstream growth and reciprocal-Euler estimates
give the absolute dominator

```text
(C_left+C_right+M)*sech(u),
C_left  = 52+2*abs(Im(c))+8*eta/pi,
C_right = (1+1/(Re(c)-1))*(1+2/(Re(c)-1)).
```

It is genuinely integrable on the full real line. The original
projection controls the diverging physical height at both infinite ends;
no finite-height cutoff is introduced.

[`ZetaStripBoundaryLimit`](../RiemannGaussian/ZetaStripBoundaryLimit.lean)
proves pointwise radial convergence at every finite `u`, ordinary
dominated convergence for both full integrals, and integrability of the
limiting functions. These coarse constants are used only to justify the
per-channel limit. They are not the sharp arithmetic allowance, and
they are not summed over arbitrary phase frequencies; doing so could
introduce an unavailable first-frequency-moment assumption.

## Only the necessary zero-source limit

Every finite canonical zero term other than the selected one is already
nonnegative. The proof therefore keeps the complete finite identity,
uses that favorable order, and passes only the selected term to its
proved cotangent limit. A full infinite-divisor interchange is not needed
for this inequality.

The finite inequality
[`finite_boundary_le`](../RiemannGaussian/ZetaStripBoundaryConstraint.lean)
uses genuinely zero-free circles, so it never applies logarithmic
monotonicity to a totalized zero logarithm. The final boundary theorem
allows zeros on the left physical line through the continuous clipping.
Global integrability of the *unclipped* left negative part and convergence
of the *unclipped* complete boundary moment are not asserted.

## Subsequent arithmetic budget and remaining scope

The now-proved actual geometric schedule is

```text
Re(c)=1+x,   eta=delta_k+x,
left edge=1-delta_k,
right edge=1+delta_k+2*x.
```

The [complete phase-family budget](zeta-strip-phase-budget.md) now substitutes
the sharp Euler profile on the left and splits the right logarithm exactly
before using the coupled prime phases. It proves the center correction
nonpositive and the complete rational mass quadratically plus exponentially
bounded. Every eligible countable family has a proved elementary source
bound and an actual finite-height zero-exclusion criterion. The signed
budget improves as more left negative depth is retained.

Discharging the strict cost inequality on explicit height intervals and
comparing published regions at matching heights remain. This formalizes
classical analytic mechanisms; it is not a historical novelty claim,
an optimized published-constant reproduction, a world-best region, or
an RH proof. The independent ordinary-prime lower bound remains open.

## Previous boundary-constraint checkpoint

The five new modules provide 62 public theorems. All 42 affected modules
pass direct elaboration with warnings treated as errors. The focused
build passes 4,815 jobs and the full build passes 10,314 jobs. Root verbose
lint reports zero errors in 19,480 declarations plus 11,521 generated
declarations, with all 14 linters; the whole-project linter also passes.
All 353 public theorems in the affected modules have explicit transitive
axiom audits using only `propext`, `Classical.choice` and `Quot.sound`.

The compiled inventory contains 1,467 project modules, 31,036 declarations
and 27,233 theorems, with no project axioms or placeholder dependencies.
`rhImplied` remains false. These counts record the boundary-constraint
checkpoint.

# The complete phase-family strip budget and explicit zero exclusion

The actual cotangent source now reaches a proved arithmetic upper bound for
every eligible finite or countably infinite phase family. The terminal
[`nonvanishing_of_elementaryBudget`](../RiemannGaussian/ZetaStripPhaseExclusion.lean)
proves literal zeta nonvanishing on a proposed closed right edge whenever
one explicit inequality holds. Its allowance contains no unknown zeta value,
integral, boundary-limit premise, or negative-part integrability assumption.

This closes the arithmetic-profile interface left by the
[actual strip boundary theorem](zeta-strip-boundary-constraint.md).
It does **not** yet establish a larger displayed region or an explicit
height interval beating published benchmarks. Those require proving that
the explicit cost is small enough on the claimed height range.

## The actual strip and complete families

For an order `k>=2`, set

```text
alpha = 1/(2^(k+2)-2),       delta = (k+2)*alpha,
0 < x <= delta/4,           eta = delta+x,
sigma_minus = 1-delta,      sigma_plus = 1+delta+2*x,
b = 2*eta/pi,               density(v) = 1/(2*cosh(v)^2).
```

[`ZetaStripEulerConstraint`](../RiemannGaussian/ZetaStripEulerConstraint.lean)
proves that these are the exact physical boundary coordinates. It discharges
all geometry assumptions of the actual strip theorem. A selected zero
`rho=beta+i*t` above `sigma_minus` lies in the whole strip.

The family assumptions are the existing general ones:

```text
a_n >= 0,                     sum a_n < infinity,
omega_0=0,                    omega_1=1,
omega_n>=1 for n!=0,
K(v)=sum a_n*cos(omega_n*v) >= 0 for every real v,
W=sum_(n!=0) a_n,             F=sum_(n!=0) a_n*log(omega_n) < infinity.
```

No finite support, first-frequency moment, optimum over families, or new
coefficient search is assumed. The kernel is the original prime-power kernel.

## The signed budget before elementary estimates

Let `g(s)=(s-1)*zeta(s)/(s+1)`, filled analytically at the pole, and let
`L_M(z)=log(max(norm(z),exp(-M)))` for any `M>=0`. Define the genuine means

```text
L_n = integral_R density(v)*L_M(g(sigma_minus+i*(omega_n*t+b*v))) dv,
Z_0 = integral_R density(v)*log|zeta(sigma_plus+i*b*v)| dv,
c_sigma(y) = log(1+4*sigma/((sigma-1)^2+y^2))/2,
R_n = integral_R density(v)*c_sigma_plus(omega_n*t+b*v) dv.
```

For `abs(t)>=2` and `log(abs(t)+2)>=1`,
[`source_le_exactBudget`](../RiemannGaussian/ZetaStripPhaseFamily.lean)
proves, with the actual full analytic multiplicity `m_rho`,

```text
a_1*m_rho*pi/(2*eta)*cot(pi*(1+x-beta)/(2*eta))
  <= a_0/x + B_exact,

B_exact = 448*a_0*log(22)
  + (sum_(n!=0) a_n*L_n + a_0*Z_0 + sum_(n!=0) a_n*R_n)/(2*eta).
```

The exact complex finite divisor identity stays upstream. The actual center
correction has the identity

```text
Re(1/(c-1)-1/(c+1))
 = 2*(Re(c)^2-1-Im(c)^2)
   / (((Re(c)-1)^2+Im(c)^2)*((Re(c)+1)^2+Im(c)^2)).
```

[`pole_re_nonpos_of_height`](../RiemannGaussian/RationalVerticalCorrection.lean)
proves its favorable sign throughout the working geometry, so the upper
bound needs no positive center charge.

The right logarithm is split **exactly** into the original zeta mean minus
its rational mass. The complete common prime kernel is then used before
bounding any of its individual channels. Thus the real-axis prime mean
costs only `a_0`, rather than the nonconstant mass `W`. See
[`negative_nonconstant_le_exact`](../RiemannGaussian/ZetaRegularizedSechMean.lean).

Every integral and countable sum is genuinely integrable or summable.
[`exactBudget_antitone_depth`](../RiemannGaussian/ZetaStripPhaseFamily.lean)
proves that increasing `M` can only improve the complete family budget.
No limit as `M` tends to infinity is needed here.

## A fully elementary allowance

Set `H=abs(t)+2` and define

```text
Q = log(8192)+alpha*log(H)+log(log(H)),
E = Q+log(2)*(alpha+1/log(H))*abs(b)/H,
R = 8*sigma_plus/t^2 + 2*c_sigma_plus(0)*exp(-abs(t)/abs(b)),

B_elementary = 448*a_0*log(22)
  + (W*(E+R)+2*F+a_0*log(1+1/(delta+2*x)))/(2*eta).
```

The proved estimates are:

- The actual left mean is at most `E`, uniformly in every `M>=0`, including
  through low heights and zeros. The exact density mass is one and its first
  absolute moment is `log(2)`.
- At any frequency `omega>=1`, the left allowance is at most
  `E+2*log(omega)`. Its height-shift correction decreases with frequency.
- Every nonconstant rational mean is at most `R`. The distant low-height
  window costs an exponential tail; no growing frequency factor is paid.
- The full right prime mean is at most `log(1+1/(delta+2*x))`, with coefficient
  `a_0` only. The sharper original mean and real-axis zeta value remain upstream.

These are proved in
[`ZetaClippedEulerMean`](../RiemannGaussian/ZetaClippedEulerMean.lean),
[`ZetaClippedEulerFamily`](../RiemannGaussian/ZetaClippedEulerFamily.lean),
[`RationalVerticalCorrection`](../RiemannGaussian/RationalVerticalCorrection.lean),
and [`ZetaStripPhaseFamily`](../RiemannGaussian/ZetaStripPhaseFamily.lean).
The theorem `source_le_elementaryBudget` puts their combined bound on the
actual multiplicity-weighted zero source.

## The explicit finite-height exclusion test

For any proposed width `0<u<delta`, if

```text
a_0/x + B_elementary
  < a_1*pi/(2*eta)*cot(pi*(x+u)/(2*eta)),
```

then every actual zero at height `t` satisfies `u<1-beta`. Equivalently,
zeta is nonzero on the full closed right edge `Re(s)>=1-u` at that height.
The exact criterion with `B_exact` and the intermediate criterion retaining
the real-axis zeta value are also proved.

[`source_at_margin_le`](../RiemannGaussian/ZetaStripPhaseExclusion.lean)
uses the existing
[phase-increment cotangent monotonicity](../RiemannGaussian/PhaseIncrementInverse.lean).
It compares the actual zero to the proposed outside edge while retaining
its full multiplicity. No small-angle or radial-polynomial approximation
replaces the cotangent in this test.

## Remaining quantitative work

The analytic and arithmetic upper bound is proved. To obtain a larger region,
the strict elementary inequality must now be discharged for a specified
width on explicit height intervals, with an eligible family already proved
upstream. Improving the all-order Euler profile or retaining more of the
actual signed means can reduce that cost. The upstream identities preserve
both options.

The subsequent [Gaussian bridge](zeta-gaussian-strip-bridge.md) now connects
the original complex Gaussian prime sum to this signed strip boundary at
`Re(s)>1`. The actual complete nearby divisor retains all ordinates and
multiplicities, and every zero correction is controlled using the
[Gaussian remainder](zeta-gaussian-pole-remainder.md) and
[nearby compensation](zeta-gaussian-near-cancellation.md). The full smoothed
pole and Archimedean response remain visible. The classical general
smoothed comparison in [Yang, Lemma 4.7](https://arxiv.org/html/2301.03165v2)
is a guide for this construction. The subsequent
[full Gaussian phase-family surplus](zeta-gaussian-phase-band.md) now closes
the quantitative inequality on an explicit height band. It preserves all
three prime responses and proves actual zero exclusion using the existing
exact family.

Published comparisons must use matching heights and all applicable benchmark
regimes. The Gaussian continuation proves three exact width comparisons on
a stated common interval; an exhaustive literature and historical novelty
audit remains. The independent ordinary-prime lower bound needed by the
separate global RH contradiction remains open. These are classical strip
and Euler mechanisms formalized from the bottom up.

## Local validation

The seven modules in this slice provide 64 public theorems. All 49 affected
modules pass direct elaboration with warnings treated as errors. The focused
build passes 4,623 jobs and the full build passes 10,321 jobs. Root verbose
lint reports zero errors in 19,561 declarations plus 11,547 generated
declarations, across all 14 linters; whole-project lint also passes.
All 417 affected public theorems have explicit transitive axiom audits using
only `propext`, `Classical.choice` and `Quot.sound`.

The reproducible compiled inventory contains 1,474 project modules,
31,143 declarations and 27,325 theorems, with no project axioms or placeholder
dependencies. `rhImplied` remains false. The source scan includes all 1,617
Lean files, including untracked files. These results are local; no new
commit, push, or remote CI result is claimed.

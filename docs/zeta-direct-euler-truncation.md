# A uniform direct zeta remainder with coupled Fourier phases

The terminal theorem
[`ZetaEulerUniformRemainder.norm_remainder_le_power`](../RiemannGaussian/ZetaEulerUniformRemainder.lean)
proves, for every integer `N>=0`,

```text
A=N+1,  0<Re(s)<=1,  abs(Im(s))<=A
  => norm(R_N(s)) <= A^(-Re(s)).
```

For actual zeta, away from `s=1`, the same module proves

```text
zeta(s) = sum_(n=1)^N n^(-s) + A^(1-s)/(s-1) + R_N(s),

norm(zeta(s)-sum_(n=1)^N n^(-s))
  <= A^(1-Re(s))/norm(s-1)+A^(-Re(s)).
```

The endpoint uses **`A=N+1`**, and the finite prefix includes `n=1`.
There is no division by an eta factor. The complex pole endpoint has
not been folded into the remainder or replaced by a real approximation.
The remainder bound itself also holds at `s=1`; the zeta reconstruction
identity excludes that pole.

This is a formalization of a classical direct-truncation mechanism,
motivated by [Yang, section 3.2](https://arxiv.org/html/2301.03165v2)
and [Simonič, section 2.1](https://arxiv.org/html/1910.08274v2).
It is not a reproduction of their optimized numerical constants and is
not a historical novelty claim. No external analytic statement is assumed.

## Exact continuation from original Euler cells

For `n>=0`, define

```text
cell(s,n)=(n+1)^(-s)-integral_(n+1)^(n+2) x^(-s) dx,
R_N(s)=sum_(n>=0) cell(s,n+N).
```

[ZetaEulerCell](../RiemannGaussian/ZetaEulerCell.lean) proves the exact
finite telescoping identities and absolute convergence for `Re(s)>0`.
Multiplication by `1-s` produces entire cells.
[ZetaEulerContinuation](../RiemannGaussian/ZetaEulerContinuation.lean)
proves local uniform convergence in the full positive half-plane and
identifies the sum with actual regularized zeta by analytic continuation.
[ZetaEulerTruncation](../RiemannGaussian/ZetaEulerTruncation.lean) then
reconstructs actual zeta at every integer cutoff.

The initial derivative envelope gave a bound proportional to
`norm(s)*N^(-Re(s))/Re(s)`. Its height factor was too large. The following
steps use the richer signed cells to remove it.

## Extract the endpoints without losing the signed tail

Put `B2(y)=y^2-y+1/6`. Two integrations by parts give exactly

```text
T_N(s) = sum_(j>=0) integral_(j+N+1)^(j+N+2)
           B2(x-(j+N+1))*x^(-s-2) dx,

R_N(s) = A^(-s)/2 + s*A^(-s-1)/12 - s*(s+1)*T_N(s)/2.
```

[ZetaEulerBernoulli](../RiemannGaussian/ZetaEulerBernoulli.lean) proves
these identities for the actual original remainder and proves absolute
convergence. Its initial absolute-cell bound on `T_N` has order
`A^(-Re(s)-1)`; that alone still loses a height factor after multiplication
by `s*(s+1)`.

## Join cells before bounding the Fourier modes

Mathlib's Bernoulli Fourier theorem gives

```text
B2(y)=sum_(n>=1) cos(2*pi*n*y)/(pi^2*n^2).
```

[ZetaEulerFourier](../RiemannGaussian/ZetaEulerFourier.lean) proves the
precise coefficient mass `1/6`, absence of the constant mode, absolute
domination and the infinite sum-integral exchange. Since each cell base is
an integer, its cosine is exactly `cos(2*pi*n*x)`. Consecutive cells join
into **one integral on the whole interval**, before taking its norm.
No cell completion error or independent cell norm is inserted.

The two orientations of each cosine are kept as complex modes. For
`mode(x)=exp(i*w*x)*x^r`,
[OscillatoryPowerPrimitive](../RiemannGaussian/OscillatoryPowerPrimitive.lean)
proves

```text
F(x)=exp(i*w*x)*x^(r+1)/(i*w*x+r),
F'(x)=mode(x)+r*mode(x)/(i*w*x+r)^2.
```

If `2*abs(Im(r))<=abs(w)*x`, the original complex denominator has norm
at least `abs(w)*x/2`. The exact integral identity retains both primitive
endpoints and the complex defect. It then yields a quantitative bound
with two additional coordinate powers in the defect. This works for
both signs of `w`.

For the actual Bernoulli modes, `r=-s-2` and `w=+/-2*pi*n`, `n>=1`.
The height-sized cutoff discharges the separation condition for all modes.
After their complete summation and the upper-endpoint limit,
[ZetaEulerOscillation.norm_tail_le](../RiemannGaussian/ZetaEulerOscillation.lean)
proves

```text
norm(T_N(s)) <= (A^(-Re(s)-2)/pi
  +norm(s+2)*A^(-Re(s)-3)/(pi^2*(Re(s)+3)))/6.
```

This gains the needed cutoff power. On `0<Re(s)<=1` and `A>=abs(Im(s))`,
the proved bounds `norm(s)<=2*A`, `norm(s+1)<=3*A`, `norm(s+2)<=4*A`
reduce it to

```text
norm(T_N(s)) <= (13/162)*A^(-Re(s))/A^2.
```

Combining the two original endpoints and this bound proves the terminal
uniform remainder theorem. All side conditions and infinite exchanges
are discharged for actual zeta.

## Actual line growth and the complete zero budget

[ZetaEulerLineBound](../RiemannGaussian/ZetaEulerLineBound.lean) identifies
the literal Euler prefix with the existing ordinary dyadic prefix, including
`n=1` and the endpoint convention. At the actual dyadic depth, the endpoint
`A` exceeds `norm(s)` and is at most `5*abs(Im(s))` in the positive unit strip
at heights at least two. The prefix therefore pays an additional constant
six. The already proved block bounds give

```text
k>=1, Re(s)=line_k, abs(Im(s))>=2
  => norm(zeta(s)) <= 8192*abs(Im(s))^alpha_k*log(abs(Im(s))).
```

[ZetaEulerLogProfile](../RiemannGaussian/ZetaEulerLogProfile.lean) cancels
the Euler pole endpoint before norms. The genuine regularized function
`(s-1)*zeta(s)/(s+1)`, continued through the pole, is bounded by four for
`0<Re(s)<=1` and `abs(Im(s))<=2`. Thus its complete near-one line is bounded
by the exponential of

```text
Q_k(t)=log(8192)+alpha_k*log(abs(t)+2)+log(log(abs(t)+2)).
```

[ZetaEulerGaussianDisc](../RiemannGaussian/ZetaEulerGaussianDisc.lean)
propagates this profile through the original Gaussian carrier and full disc.
[ZetaEulerAngularBound](../RiemannGaussian/ZetaEulerAngularBound.lean)
retains the actual selected zero multiplicity and radial correction.
The [complete family theorem](../RiemannGaussian/ZetaEulerAngularPhaseFamily.lean)
then proves the exact improvement

```text
B_Euler+2*W*log(4/delta_k)/(pi*delta_k)=B_sharp.
```

Its strict budget criterion is a theorem about actual zeros for every
eligible finite or countable phase family. No coefficient search is used.
The [original signed vertical detector](zeta-sech-euler-bound.md) also now
inherits `Q_k`, with exact kernel moments and a complete pole-correction bound.

## What remains

The displayed [current region](zeta-log-log-zero-free.md) is unchanged and
has coefficient-dependent, unevaluated thresholds. The
[actual strip boundary constraint](zeta-strip-boundary-constraint.md) now
connects the selected cotangent source to complete physical integrals with
all radial limits proved. The
[complete strip family budget](zeta-strip-phase-budget.md) now applies the
sharp profile, exact rational correction and coupled right prime phases.
An elementary inequality suffices for actual finite-height nonvanishing;
proving its strict surplus on larger specified widths is next. A world-best comparison
needs explicit matching height ranges and every
relevant published region. The independent cofinal ordinary-prime lower bound
`Re(P_N)>=-1+epsilon`, for a fixed positive `epsilon`, remains open; RH is
not proved.

## Prior uniform-remainder checkpoint

The full warning-as-error build passes 10,291 jobs; the focused arithmetic,
Gaussian and Euler build passes 4,960 jobs. All 19 affected modules pass
strict direct elaboration. The whole-project declaration lint passes, and
all 111 public theorems in the affected modules have explicit axiom audits
using only `propext`, `Classical.choice` and `Quot.sound`.

The generated inventory covers 1,444 project modules, 30,611 declarations
and 26,840 theorems, with no project axioms or placeholder dependencies;
`rhImplied` remains false. Generated artifacts reproduce exactly, and the
source scan covers 1,587 Lean files.

These counts record the preceding uniform-remainder checkpoint. The current
growth and vertical-detector audit is recorded in
[the new detector documentation](zeta-sech-euler-bound.md).

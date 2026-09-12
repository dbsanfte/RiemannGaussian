# General phase families, the exact center shift, and Gaussian correction

The current theorem applies to every eligible countable family, including
infinite support. It does not search for coefficients or assert an optimum
across all possible families.

## General hypotheses and exact source

Let `a_n>=0` be summable, let `omega_0=0`, `omega_1=1`, and require
`omega_n>=1` for every `n!=0`. The full phase kernel must be nonnegative
at every real phase. Require also the finite logarithmic frequency moment

```text
W = sum_(n!=0) a_n,
F = sum_(n!=0) a_n*log(omega_n) < infinity.
```

For a positive center shift `r`, the selected pole competes with the
real-axis pole through the exact source

```text
Gamma(r) = a_1/(r+1) - a_0/r.
```

The [exact square identity](../RiemannGaussian/PhasePoleMargin.lean) proves,
for `0<a_0<a_1`,

```text
max_(r>0) Gamma(r) = (sqrt(a_1)-sqrt(a_0))^2,
r_opt = sqrt(a_0)/(sqrt(a_1)-sqrt(a_0)),

max Gamma - Gamma(r)
  = ((sqrt(a_1)-sqrt(a_0))*r-sqrt(a_0))^2/(r*(r+1)).
```

This is the unique maximizing **center shift at fixed weights**. The
repository's older coefficient optimizer used a different cost and is
not asserted to optimize the new angular objective.

## Actual source and the complete infinite allowance

[ZetaAngularPhaseFamily](../RiemannGaussian/ZetaAngularPhaseFamily.lean)
proves, for the actual selected zero and eligible full-radius geometry,

```text
a_1*m_rho*(1/d-d/delta_k^2) <= a_0/x+B_k(x,t),
B_k(x,t)=448*a_0*log(22)
          +2*sum_(n!=0) a_n*E_k(x,omega_n*t)/(pi*delta_k).
```

No arithmetic or analytic input is left as an unproved carrier assumption.
Multiplicity, the exact radial correction, every frequency and the signed
complex boundary identity remain available. At `x=r*u`, a zero within
margin `u`, with `4*(r+1)*u<delta_k`, forces

```text
Gamma(r) <= u*B_k(r*u,t)+a_1*(r+1)*(u/delta_k)^2.
```

[ZetaAngularPhaseAllowance](../RiemannGaussian/ZetaAngularPhaseAllowance.lean)
proves absolute convergence and bounds the whole allowance between
`W*E_k(x,t)` and `W*E_k(x,t)+2*F`. Thus no infinite frequency tail is
silently discarded.

On the single growing-order schedule `k=floor(log(log(abs(t)+2))/b)`,
`b>log(2)`, and `u=C*log(log(abs(t)+2))/log(abs(t)+2)`, the
[complete cost](../RiemannGaussian/ZetaAngularPhaseLimit.lean) tends to

```text
2*W*C*b/pi.
```

The finite logarithmic frequency moment and full radial correction are
lower order on that same schedule. The
[general exclusion theorem](../RiemannGaussian/ZetaAngularPhaseExclusion.lean)
therefore excludes eventual actual zeros whenever
`2*W*C*log(2)<pi*Gamma(r)`. Its optimized-shift version substitutes the
exact squared-root source above.

The existing exact contact family has `W<=61/100` and
`Gamma(13/4)>=11/625`. All coefficients, phase positivity and frequencies
are proved upstream. Its
[application](../RiemannGaussian/ZetaExactPhaseAngularExclusion.lean) gives
the [current coefficient range](zeta-log-log-zero-free.md), with no new
coefficient search.

## The finite-height Gaussian improvement

Retaining the real Gaussian quadratic and actual rational normalization gives

```text
G_k(t) = (3/(abs(t)+2))^2/4 + delta_k^2
           +log(1+2/(abs(t)-delta_k)),
0 <= G_k(t) <= 2                       (k>=2, abs(t)>=2),
norm(zeta(s)) <= exp(profile_k(t)+G_k(t))
```

throughout the full eligible disc. See
[the strip proof](../RiemannGaussian/ZetaGaussianSharpStrip.lean) and
[the full-disc theorem](../RiemannGaussian/ZetaGaussianSharpDisc.lean).
Replacing the previous correction `14` saves at least twelve logarithmic
units per nonconstant channel. The
[whole-family theorem](../RiemannGaussian/ZetaSharpAngularPhaseFamily.lean)
proves `B_sharp+24*W/(pi*delta_k)<=B_previous` and carries the improved
budget through the actual finite-height zero exclusion.

The [direct Euler growth theorem](zeta-direct-euler-truncation.md) now
removes the inherited eta-division cost from the whole profile. Its
[actual full-disc theorem](../RiemannGaussian/ZetaEulerGaussianDisc.lean)
uses `Q_k(t)=log(8192)+alpha_k*log(abs(t)+2)+log(log(abs(t)+2))`.
The [complete family bound](../RiemannGaussian/ZetaEulerAngularPhaseFamily.lean)
proves exactly

```text
B_Euler + 2*W*log(4/delta_k)/(pi*delta_k) = B_sharp.
```

The same multiplicity-weighted zero source and radial correction are kept.
The strict budget criterion reaches actual pointwise zero exclusion for
any eligible family. These finite-height savings do not change the displayed
asymptotic coefficient range by themselves.

The [complete strip phase-family budget](zeta-strip-phase-budget.md) now
provides a further route with an exact cotangent source, sharp Euler mean,
coupled right prime phases and controlled rational correction. Its actual
divisor identity, boundary limits, countable-family sums and elementary
finite-height exclusion criterion are all proved. Discharging its strict
cost inequality on explicit height ranges remains. No explicit threshold
or world-best region has yet been established.

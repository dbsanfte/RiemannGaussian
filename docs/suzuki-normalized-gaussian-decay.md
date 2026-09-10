# Normalized Gaussian drift decay through the zero divisor

Lean proves that the complete denominator-drift allowance, including its
squared smoothing factor, has integral tending to zero on every fixed
compact subset of an upper horizontal spectral line. Both scaled current
endpoints also vanish. Consequently the actual normalized arithmetic
Gaussian integral is eventually below every positive ceiling on each
fixed finite interval. No arithmetic decay hypothesis is assumed.

The terminal theorems are
[`tendsto_integral_suzukiGammaGaussianDriftAllowance_scaled`](../RiemannGaussian/SuzukiGammaNormalizedGaussianDecay.lean)
and
[`eventually_integral_suzukiGammaShiftArithmeticSource_gaussian_le`](../RiemannGaussian/SuzukiGammaNormalizedGaussianDecay.lean).
This is a finite-interval result. The independent upper bound for the
full singular reflection-weighted source remains open, and no new zeta
zero exclusion follows.

## Exact normalization and phase

Fix real `y >= 0`, write `z=x+i*y` and `s=1/2+y-i*x`, and use the
[shifted Gamma arithmetic representation](suzuki-arithmetic-band-reduction.md).
With `F`, `Q`, `D` and `d_r` as defined there, let

```text
U_r = |F|^2/d_r
S_r = i*F*conj(D)/d_r
T_r = -i*S_r-(1+conj(Q))*U_r = F*conj(F')/d_r.
```

The smooth xi definitions give these identities through common zeros as
well as ordinary carrier poles. Primes on `F` and `Q` are arithmetic
complex derivatives; primes on fields `U_r`, `S_r`, `T_r` and currents
below are horizontal real derivatives in `x`. The arithmetic source has
the exact complex representation

```text
A_r = 2*r^2*(T_r*U_r' - U_r*T_r').
Drift_r = -2*Im(T_r)-U_r'.
```

[`SuzukiGammaNormalizedCurrent.lean`](../RiemannGaussian/SuzukiGammaNormalizedCurrent.lean)
also identifies `Drift_r=U_r*d_r'/d_r`, including the defined common-zero
values, and retains the exact differentiated denominator. For every
differentiable complex weight `P`, it proves the current identity

```text
P*A_r = -2*r^2*(P*U_r*T_r)' + 2*r^2*P'*U_r*T_r
          + 4*r^2*P*T_r*U_r'.
```

The same identity is instantiated with the actual complex reflection
weight times the heat factor away from its two singular nodes. It is
retained independently of the subsequent real Gaussian estimate.

For `w(x)=exp(-tau*(x-c)^2)` and `J_r=w*U_r*T_r`, the exact square is

```text
w*Im(A_r) = -2*r^2*Im(J_r')
  - 8*r^2*w*(Im(T_r)+(Drift_r+tau*(x-c)*U_r)/4)^2
  + (r^2/2)*w*(Drift_r+tau*(x-c)*U_r)^2.
```

[`SuzukiGammaNormalizedGaussian.lean`](../RiemannGaussian/SuzukiGammaNormalizedGaussian.lean)
proves this identity and its finite-interval integral, with both endpoints
and genuine integrability of the square terms. All normalization drift
is present in both squares. No denominator is held constant.

## A derivative budget that vanishes at zeros

For every `r >= 1`, the actual fields share the same positive rescaling:

```text
h_r = 1+(r^2-1)*U_1
U_r = U_1/h_r
S_r = S_1/h_r
U_r' = U_1'/h_r^2.
```

The exact quadratic relation is `|S_r|^2=U_r-r^2*U_r^2`, including
common zeros. Differentiating its unit-scale version gives

```text
2*Re(S_1*conj(S_1')) = (1-2*U_1)*U_1'
(U_1')^2 <= 16*U_1*(|S_1'|^2+(U_1')^2).
```

The second inequality is a proved estimate of the actual fields. The
factor `U_1` preserves their vanishing at zeros. Combining it with the
rescaling law proves, for `r >= 2`,

```text
r^2*(U_r')^2 <= 32*(|S_1'|^2+(U_1')^2).
```

The right side is continuous on the entire horizontal line. The scaled
mass, carrier and mass derivative each tend to zero at every fixed point:
`r*U_r -> 0`, `r*S_r -> 0`, `r*U_r' -> 0`. At a zero of `U_1`,
nonnegativity proves `U_1'=0`; elsewhere the positive rescaling
denominator supplies decay. Dominated convergence therefore gives

```text
integral_K r^2*(U_r')^2 -> 0
```

for every fixed compact `K`. These are compiled in
[`SuzukiMassRescaling.lean`](../RiemannGaussian/SuzukiMassRescaling.lean)
and
[`SuzukiMassDerivativeEnergy.lean`](../RiemannGaussian/SuzukiMassDerivativeEnergy.lean).
No zero simplicity or separation hypothesis is needed.

## Closing the full finite-interval allowance

Write `k(x)=tau*(x-c)-2*Im(Q(s))`. The exact drift expansion is

```text
r^2*Allowance_r = w*(2*Re(r*S_r)-r*U_r'+k*(r*U_r))^2
Allowance_r = w*(Drift_r+tau*(x-c)*U_r)^2.
```

All three scaled terms tend to zero at every point. For `r >= 2`, Lean
proves the continuous majorant

```text
0 <= r^2*Allowance_r
  <= 3*w*(1+32*(|S_1'|^2+(U_1')^2)+k^2).
```

The shifted Gamma correction is analytic at every argument on the
upper spectral line, so this majorant is integrable on each fixed
compact `K`. It proves `integral_K r^2*Allowance_r -> 0` for every fixed
real `tau` and `c`. Compactness makes a positivity assumption on `tau`
unnecessary here.

The same exact field coupling gives `r*T_r -> 0` and `r^2*J_r(x) -> 0`
at each fixed endpoint. For `a <= b`, retaining the negative square
until taking an upper bound yields

```text
integral_a^b w*Im(A_r)
 <= -2*r^2*Im(J_r(b)-J_r(a)) + (r^2/2)*integral_a^b Allowance_r.
```

The right side tends to zero. Thus for every `epsilon > 0`, the left
side is eventually at most `epsilon`. The theorem proves this one-sided
ceiling; it does not assert convergence of the entire signed integral.

## Remaining global obstruction

The [arithmetic band reduction](suzuki-arithmetic-band-reduction.md) retains
the full positive source in an area integral with the complex factor
`W(z)=-(1/(z-a)-1/(z-beta))^2`. The present majorant is integrable on
fixed compact horizontal sets before that singular weight is applied.
It does not supply a majorant after multiplication by `W` through the
reflected node, nor uniform control for a growing interval.

The general complex current identity above retains the information
needed to investigate that weight. Its phase, differentiated weight
and possible concentration at the reflected node still require an
independent estimate. Neither the new finite-interval ceiling nor
pointwise decay permits exchanging the missing weighted area limit.

The subsequent [arithmetic node profile](suzuki-arithmetic-node-profile.md)
now identifies the complete weighted core as positive and radial,
uniformly over angles at fixed nonzero rescaled radius. All finite
normalized complex angular mixtures with a fixed bound on total absolute
weight preserve a positive core, including growing and changing families.
Thus that class of angular averages does not remove the missing source.

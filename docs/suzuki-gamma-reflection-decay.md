# The full reflected Gamma curvature error vanishes

The terminal theorem
[`tendsto_integral_norm_suzukiGammaShiftReflectionError`](../RiemannGaussian/SuzukiGammaReflectionDecay.lean)
proves L1 decay of the actual completion-curvature contribution over the
**entire upper half-plane**, including its reflected zero. This is an
independent error estimate in the actual normalized source, with its
original complex reflection weight. It is not a bound below the positive
source for the remaining arithmetic density, and gives no zero exclusion.

All statements below hold for the literal functions. There is no finite
eta truncation, coefficient search, simplicity assumption or arithmetic
decay hypothesis.

## Exact shifted representation

Let `zeta₁` be Mathlib's entire pole-removed zeta function. For `Re(s)>0`, set

```text
F(s) = zeta₁(s) / ((s+2)*(s+4))
H(s) = -8*pi^3*GammaR(s+6)
Q(s) = -log(pi)/2 + digamma((s+6)/2)/2
D(s) = F'(s) + (1+Q(s))*F(s).
```

The negative constant matches this repository's normalization
`xi(s)=s*(1-s)*GammaR(s)*zeta(s)` away from its removed poles.
[`SuzukiGammaShift.lean`](../RiemannGaussian/SuzukiGammaShift.lean) proves

```text
H(s)*F(s) = xi(s)
H(s)*D(s) = xi(s)+xi'(s)
Q(s) = H'(s)/H(s)
Q'(s) = digamma'((s+6)/2)/4.
```

`H` is holomorphic and nonzero throughout `Re(s)>0`; `F`, `Q` and `D`
are holomorphic there. The identities include `s=1`, arbitrary xi zeros
and common zeros. No totalized zeta pole is substituted for `zeta₁`.
All common factors cancel in the full smooth quotient before any bounds.

## A signed trigamma estimate

[`TrigammaHalfPlane.lean`](../RiemannGaussian/TrigammaHalfPlane.lean)
differentiates the actual convergent digamma difference series with a
uniform summable derivative majorant. It then keeps the exact midpoint
telescoper and its complex remainder:

```text
digamma'(z) = 1/(z-1/2) - sum_n R_n(z)
R_n(z) = 1 / (4*(n+z)^2*(n+z-1/2)*(n+z+1/2)).
```

For `x=Re(z)>1/2`, the independently proved error bound is

```text
|digamma'(z) - 1/(z-1/2)| <= 1/(4*normSq(z)*(x-1/2)).
```

The leading reciprocal retains its real part. Thus

```text
Re(digamma'(z)) >= ((x-1/2) - 1/(4*(x-1/2))) / normSq(z).
```

In particular the real part is positive for `x>1`. For the actual
shifted completion, this yields `Re(Q'(s))>0` and `|Q'(s)|<=1/8`
throughout `Re(s)>0`, uniformly in imaginary height. These are estimates
for a classical special function, not claims of historical novelty.

## The actual normalized source

Put `s=1/2-i*z` in the spectral plane, and let

```text
d = |D(s)|^2 + r^2*|F(s)|^2
U_r(z) = |F(s)|^2/d.
```

[`SuzukiGammaShiftSource.lean`](../RiemannGaussian/SuzukiGammaShiftSource.lean)
identifies `U_r` with the existing globally smooth actual xi mass and
transports the complete source through every numerator/denominator zero.
Its exact decomposition is

```text
V_r = A_r + C_r
A_r = 2*i*r^2*F^2*conj(F'^2-F*F'') / d^2
C_r = -2*i*r^2*U_r^2*conj(Q').
```

The full denominator is shared. For `r>0`, the proved mass bound
`0<=U_r<=1/r^2` gives

```text
Im(C_r) <= 0
|C_r| <= 1/(4*r^2).
```

This uniform pointwise estimate alone is insufficient for integration
against the singular reflection weight. The next step uses the actual
zero charts before taking a norm.

## Both reflection nodes and the entire upper half-plane

Let `W` be the original squared Cauchy-difference reflection weight and
`B(z)=2*Im(z)*exp(-tau*((c-Re(z))^2+Im(z)^2))` the original boundary heat.
The literal error is

```text
E_r(z) = W(z)*B(z)*(V_r(z)-A_r(z)) = W(z)*B(z)*C_r(z).
```

The exact full reflection source equals its remaining arithmetic
density plus `E_r`. That remaining density includes the original
companion heat term with the actual smooth carrier.

For every actual zero, its analytic carrier chart gives a global bound
`U_1(z)<=C_a*|z-a|^2`. Applying this at both reflection nodes proves

```text
|W(z)|*U_1(z) <= C_rho                 for every z.
r^2*U_r(z)^2 <= U_1(z)                for r>=1.
|E_r(z)| <= (C_rho/4)*|B(z)|          on Im(z)>=0, r>=1.
```

The right side is integrable in the whole plane for every fixed
`tau>0`. Meanwhile the independent pointwise estimate gives
`|E_r(z)|<=|W(z)*B(z)|/(4*r^2)`, hence pointwise decay. Dominated
convergence proves

```text
integral_{Im(z)>=0} |E_r(z)| -> 0     as r -> infinity.
integral_{Im(z)>=0} E_r(z) -> 0.
```

No punctures, principal values or expanding-area limit interchange are
used. `tendsto_setIntegral_suzukiGammaShiftReflectionError` also proves
the complex error tends to zero on **any moving spatial cutoffs** inside
the upper half-plane. This follows from the same global L1 bound.

## Precise remaining obligation

The active goal still needs an independent signed upper bound for the
remaining arithmetic density, strictly below the positive reflected
source after the proved errors. Its variable denominator and reflection
phase remain coupled. `Q` remains in `D`; this result does not remove
all Gamma information from that denominator. The subsequent
[arithmetic band reduction](suzuki-arithmetic-band-reduction.md) removes
the companion heat term in global L1, proves uniform moving-cutoff
control, and removes the entire arithmetic safe half-plane. The required
signed ceiling in the surviving band remains open.

The present limit fixes positive Gaussian time and sends `r` to infinity.
The previous [quartic Gaussian estimate](eta-quartic-gaussian.md) sends
Gaussian time to zero for a different, unnormalized numerator. No
uniform joint limit connecting those estimates is claimed. Nor does
integrability of their difference establish separate whole-half-plane
integrability of both full source terms.

## Local verification

The four new modules contain 43 public theorems and are imported by the
root library. Direct warnings-as-errors checks, the root and full builds,
the whole-project declaration linter and the root `#lint+` audit pass.
Explicit axiom checks for all 43 public theorems use only `propext`,
`Classical.choice` and `Quot.sound`. These results remain local; this
slice has not been committed or remotely verified.

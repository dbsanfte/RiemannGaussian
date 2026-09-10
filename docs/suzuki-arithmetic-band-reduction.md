# The full source reduces to arithmetic inside the zero strip

Lean removes both complete source errors and the entire arithmetic
contribution on the closed Euler half-plane `Re(s)>=1`. The latter now
has a global L1 bound `C/r^2`, without the extra positive buffer in the
earlier theorem. This leaves one normalized, reflection-weighted
arithmetic quartic inside the right half of the critical strip. Its
independent signed upper bound is still open. There is no new zero
exclusion or proof of RH.

The main terminal theorem is
[`tendsto_suzukiGammaShiftWeightedArithmeticSource_moving_zero_strip`](../RiemannGaussian/SuzukiEulerSourceDecay.lean).
It retains the full positive source of a hypothetical right-half zero.
The separate unconditional estimate
[`exists_integral_norm_suzukiGammaShiftWeightedArithmeticSource_euler_bound`](../RiemannGaussian/SuzukiEulerSourceDecay.lean)
proves quadratic L1 decay on the entire closed Euler half-plane, with no
right-half zero assumption.

The subsequent [compact source bounds](suzuki-compact-source-decay.md)
also control the strip itself: on every fixed compact upper spectral
region, the actual unweighted arithmetic L1 mass is at most `C_K/r`,
through all zeros and carrier poles. With the original reflection
weight and Gaussian, the exterior of a reflected `epsilon`-disk has
absolute integral at most `C/(r*epsilon^2)`, uniformly over the selected
right-half zero, positive radius and `r>=1`. The full source remains
in a moving reflected neighborhood whenever `r*epsilon(r)^2` tends
to infinity. Its independent signed ceiling remains open.

## Exact source and the two errors

Use the existing notation `a = spectralCoordinate(rho)`, `beta = conj(a)`,
`m = analyticZetaZeroMultiplicity(rho)`, and `s = 1/2-i*z`. The original
reflection weight and boundary heat are

```text
W(z) = -(1/(z-a)-1/(z-beta))^2
B(z) = 2*Im(z)*exp(-tau*((c-Re(z))^2+Im(z)^2)).
```

In the exact shifted Gamma representation,

```text
F(s) = zeta₁(s)/((s+2)*(s+4))
Q(s) = -log(pi)/2 + digamma((s+6)/2)/2
D(s) = F'(s)+(1+Q(s))*F(s)
d_r(s) = |D(s)|^2+r^2*|F(s)|^2
A_r(s) = 2*i*r^2*F(s)^2*conj(F'(s)^2-F(s)*F''(s))/d_r(s)^2.
```

[`suzukiXiSmoothReflectionSource_eq_weightedArithmetic_add_error`](../RiemannGaussian/SuzukiGammaArithmeticReduction.lean)
proves, including the defined values at common zeros,

```text
G_r(z) = W(z)*B(z)*A_r(s) + E_Gamma,r(z) + E_heat,r(z)
E_heat,r(z) = -i*W(z)*S_r(z)*H_heat(c,tau,i*z).
```

Both complete errors tend to zero in L1 on `Im(z)>=0` as `r` tends to
infinity, for each fixed `tau>0` and fixed real center `c`. This is
[`tendsto_integral_norm_suzukiGammaShiftSourceError`](../RiemannGaussian/SuzukiGammaArithmeticReduction.lean).
The companion term alone has L1 decay over the whole complex plane.

The companion proof uses actual zero charts to bound `S_1` linearly at
each reflection node. Monotonicity gives `|S_r|<=|S_1|` for `r>=1`, so

```text
|W(z)|*|S_r(z)| <= C_rho*(1/|z-a|+1/|z-beta|).
```

The reciprocal distances are locally integrable in the plane. The heat
source is a polynomial times a Gaussian, and its full norm is integrable.
These facts supply a global dominator through both nodes. The pointwise
bound `|S_r|<=1/(2*r)` then gives dominated convergence. No reflected
node is excised and no integrability hypothesis is left to the caller.

## Simultaneous cutoffs

The original boundary estimate contains `R^2*exp(-tau*R^2/4)`.
Bounding this by `4/tau` gives

```text
|integral_rectangle G_r - 2*pi*i*B(beta)/m|
  <= 1536*Im(a)^2/(tau*r).
```

[`norm_suzukiXiSmoothReflectionSource_rectangle_sub_mass_le`](../RiemannGaussian/SuzukiGammaArithmeticCutoff.lean)
proves this uniformly for `R>=1`, `2*|c|<=R` and `2*|Re(a)|<=R`.
Consequently every rectangle schedule satisfying those conditions may
move with `r`, without a relation between their growth rates. The exact
arithmetic source inherits the same limit after the two globally
negligible errors are removed. This does not assert global absolute
integrability of the arithmetic term inside the zero strip.

## The earlier estimate away from the boundary

Write `q(z)` for the original meromorphic Suzuki carrier. The preceding
global xi expansion already proves, on `Im(z)>=1/2`, that `q` is
holomorphic and

```text
|q(z)|^2 <= Im(q(z)).
```

Fix `delta>0` and `Im(z)>=1/2+delta`. A disk of radius `delta` around
`z` stays in this known zero-free half-plane. Applying the existing
Cayley--Schwarz theorem to `-q` proves

```text
|q'(z)| <= 2*Im(q(z))/delta <= 2*|q(z)|/delta.
```

The exact radial source identity retains its complex phase:

```text
V_r(z) = -2*i*r^2*q(z)^2*conj(q'(z))/(1+r^2*|q(z)|^2)^2.
```

Only after retaining this identity is the signed derivative bound used.
The elementary inequality `x^3 <= (1+x^2)^2` gives

```text
|V_r(z)| <= 4/(r*delta)
|A_r(1/2-i*z)| <= 4/(r*delta)+1/(4*r^2)
|W(z)| <= 4*Im(a)^2/delta^4.
```

These are compiled in
[`SuzukiSafeHalfPlaneSourceDecay.lean`](../RiemannGaussian/SuzukiSafeHalfPlaneSourceDecay.lean).
They give the explicit global bound

```text
integral_{Im(z)>=1/2+delta} |W(z)*B(z)*A_r(1/2-i*z)|
 <= [4*Im(a)^2/delta^4]*[4/(r*delta)+1/(4*r^2)]
      *integral_complex_plane |B(z)|.
```

The Gaussian norm integral is proved finite, so the left side tends to
zero. Arbitrary moving spatial cutoffs inside this half-plane inherit
the same decay. In arithmetic coordinates this is `Re(s)>=1+delta`.
The constants depend on `delta`; no simultaneous `delta->0` or
`tau->0` limit is claimed.

## Curvature removes the buffer and improves the rate

Write `A(z)=xi(1/2+i*z)` and `L(z)=A'(z)/A(z)`. On `Im(z)>=1/2`,
the genuine xi value and carrier denominator are nonzero. The exact
identities in
[`SuzukiEulerSourceDecay.lean`](../RiemannGaussian/SuzukiEulerSourceDecay.lean)
are

```text
q'(z) = -q(z)^2*L'(z)
V_r(z) = 2*i*r^2*|q(z)|^4*conj(L'(z))/(1+r^2*|q(z)|^2)^2.
```

The radial coefficient is nonnegative; the complex curvature, its sign,
and its orientation remain in this identity. Taking a norm downstream
gives `|V_r(z)| <= 2*|L'(z)|/r^2`.

[`RiemannXiEulerCurvature.lean`](../RiemannGaussian/RiemannXiEulerCurvature.lean)
proves a global polynomial majorant for the actual curvature. Above
absolute zero height one, the existing Stechkin margin supplies the
distance estimate. The remaining genuine zeros belong to a finite
window; the finite sum of their reciprocal edge distances supplies
the low-height constant. Thus, for a single `P>=1`,

```text
1 <= P*(1+|s|)*|s-rho|     for Re(s)>=1 and every genuine zero rho.
```

The exact absolutely convergent logarithmic-derivative difference
series then bounds the derivative by the already summable divisor
weight `sum_rho m(rho)/(1+|rho|^2)`. In particular,

```text
|(xi'/xi)'(s)| <= C*(1+|s|)^4      for Re(s)>=1
|L'(z)| <= C'*(1+|z|)^4           for Im(z)>=1/2.
```

This argument neither assumes a uniform positive zero gap at all
heights nor differentiates an unjustified infinite series. The
distance bound gives a local Lipschitz estimate for the exact full
series, which bounds its actual analytic derivative.

For the fixed selected zero, put `d=1/2-|Im(a)|>0`. Its original
reflection weight satisfies `|W(z)|<=4*Im(a)^2/d^4` on the same closed
half-plane. Every polynomial in `|z|` is proved integrable against
`|B(z)|`. Adding the already bounded Gamma-curvature error gives

```text
|A_r(1/2-i*z)| <= C_A*(1+|z|)^4/r^2
integral_{Im(z)>=1/2} |W(z)*B(z)*A_r(1/2-i*z)| <= C(rho,c,tau)/r^2.
```

The latter holds for all `r>=1`, each fixed real center `c`, and each
fixed `tau>0`. Its constant is independent of the spatial cutoff;
all moving subsets inherit decay. No `tau->0` limit is claimed.
The constants are mathematically defined finite bounds, not numerical
certificates. All zero avoidance, summability, and integrability
premises are discharged for the actual functions.

## What remains

For every hypothetical `Re(rho)>1/2`, the integral of the weighted
arithmetic quartic over the surviving band

```text
rectangle(R(r)) intersect {0<=Im(z)<1/2}
```

tends to `2*pi*i*B(beta)/m`, whose imaginary part is strictly positive.
This is exactly `1/2<=Re(s)<1` in arithmetic coordinates. The strip
is bounded vertically in spectral coordinates; its horizontal cutoff may grow.
The desired contradiction needs an independent signed upper bound
strictly below this source, after the proved errors. Smoothing alone
does not supply that deficit.

The earlier unnormalized eta Gaussian square estimate cannot be used
through `d_r(s)^2` or the complex reflection weight without a new
argument. The completion's first derivative `Q` still appears in `D`.
The present chain removes genuine error terms and the entire closed
Euler half-plane. It does not establish the arithmetic inequality
inside the strip or claim a new zero exclusion.

The subsequent [normalized Gaussian decay theorem](suzuki-normalized-gaussian-decay.md)
now retains the variable denominator in an exact current and Gaussian
square identity. Its full scaled drift allowance and endpoint currents
have proved decay on fixed finite upper horizontal intervals, including
all zeros. This closes the finite-interval arithmetic upper bound before
the singular reflection weight is applied. Controlling that complex
weight through its reflected node remains an independent obligation.

# Smooth carrier, complete Gaussian area bound, and retained reflection source

This slice constructs a bounded, globally real-smooth version of the actual
Suzuki carrier. It proves both an independent unweighted Gaussian area
decay bound and the exact source limit for the complete reflection-weighted
area. Geometric excision and outer boundary decay are proved, retaining
every carrier pole and both signed area terms. The independent signed
upper bound needed for a contradiction is still open. No new zero exclusion
or RH proof follows from this slice.

## Actual carrier and smooth quotient

Write

```
A(z) = xi(1/2+i*z),   E(z) = A(z)+i*A'(z),
C(z) = i*(1+Esharp(z)/E(z))/2.
```

Only where `E(z)!=0` is the literal original carrier equal to `i*A(z)/E(z)`.
For real `r>0`, define

```
D_r(z) = abs(E(z))^2+r^2*abs(A(z))^2,
S_r(z) = i*A(z)*conj(E(z))/D_r(z).
```

The homogeneous formula sets `S_r=0` at common zeros. Lean proves this value
matches an actual smooth extension using the local xi model. Consequently
`S_r` is globally real-smooth, including genuine carrier poles of all orders
and common xi/denominator zeros, and

```
abs(S_r(z)) <= 1/(2*r).
```

On the original regular domain there are two exact identities:

```
S_r = C/(1+r^2*abs(C)^2),
C = S_r+r^2*C^2*conj(S_r).
```

The second keeps the full complex complement; the estimate does not silently
replace the original carrier by its smooth part.

See [ComplexSmoothQuotient.lean](../RiemannGaussian/ComplexSmoothQuotient.lean)
and [SuzukiCarrierSmooth.lean](../RiemannGaussian/SuzukiCarrierSmooth.lean).

## Full signed area source

Use the repository's oriented Cauchy–Green convention

```
G(f) = i*partial_x(f)-partial_y(f) = 2*i*partial_bar(f).
```

Lean proves, globally for `r>0`,

```
G(S_r)(z) = J_r(z)
          = 2*r^2*A(z)^2*conj(A'(z)*E(z)-A(z)*E'(z))/D_r(z)^2.
```

This is a complex identity. Neither the Wronskian phase nor any of its
signed terms has been discarded. The explicit source is continuous,
including at common zeros where its displayed quotient has value zero.
Every finite rectangle therefore has a genuine area integral, and its
oriented boundary integral equals the integral of `J_r`.

The [Cauchy–Green algebra](../RiemannGaussian/ComplexCauchyGreenAlgebra.lean)
proves the exact product, quotient, conjugation and input-rotation rules.
The [actual flux identities](../RiemannGaussian/SuzukiCarrierSmoothFlux.lean)
discharge the analytic and integrability conditions for `S_r` and for the
existing Gaussian boundary heat.

## Independent bound with both Gaussian terms retained

In spectral coordinates the actual boundary heat is

```
B_(x,tau)(z) = 2*Im(z)*exp(-tau*((x-Re(z))^2+Im(z)^2)).
```

It vanishes on the real boundary. Let `H_(x,tau)` denote the existing
arithmetic-coordinate heat source. The exact rotated identity is
`G(B)(z)=-i*H_(x,tau)(i*z)`. Define the complete complex bulk

```
K_(r,x,tau)(z) = B_(x,tau)(z)*J_r(z)-i*S_r(z)*H_(x,tau)(i*z).
```

Both terms are retained inside the integral. For `r>0`, `tau>0`, `R>0`
and `R>=2*abs(x)`, the terminal bound is

```
abs(integral_[-R,R] integral_[0,R] K_(r,x,tau)(a+i*y) dy da)
  <= 4*R^2/r*exp(-tau*R^2/4).
```

It follows from the exact boundary identity, the global carrier bound,
the zero real boundary, and Gaussian decay on the three outer sides.
For every fixed positive `r,tau` and every real `x`, these exhausting
rectangle integrals tend to zero. This is not a claim of absolute
integrability over the full half-plane or a bound for either area term
separately.

The checked terminal theorems are
`norm_suzukiXiSmoothBoundaryHeatBulk_rectangle_le` and
`tendsto_suzukiXiSmoothBoundaryHeatBulk_rectangle_zero` in
[SuzukiCarrierSmoothHeatBound.lean](../RiemannGaussian/SuzukiCarrierSmoothHeatBound.lean).

## The original reflection source is still present

For a genuine zero `rho` of analytic multiplicity `m`, write
`alpha=zetaSpectralCoordinate(rho)` and `beta=conj(alpha)`. The original
weight is

```
W_rho(z) = -(1/(z-alpha)-1/(z-beta))^2.
```

At every xi node the smooth carrier has the same divided local source:

```
S_r(z)/(z-alpha)^2 = (1/m)/(z-alpha)+p(z),
```

where `p` is real-smooth near the node. This covers all multiplicities.
If `Im(alpha)!=0`, the complete original reflection weight therefore has

```
limit_(q -> 0+) integral_circle(beta,q) W_rho(z)*S_r(z) dz
  = -2*pi*i/m.
```

Multiplying by the moving Gaussian gives exactly
`-2*pi*i*B_(x,tau)(beta)/m`. Circle integrability is proved even if original
carrier poles lie on the circle. The differential identities, away only
from the two test nodes, are

```
G(W_rho*S_r) = W_rho*J_r,
G((W_rho*S_r)*B_(x,tau)) = W_rho*K_(r,x,tau).
```

These include every genuine carrier pole. They supply the local source
and density for the geometric excision theorem below. The preceding
vanishing bound for the integral of `K` is not a bound for the integral
of `W*K` across its reflection-node puncture.

See [SuzukiCarrierSmoothReflection.lean](../RiemannGaussian/SuzukiCarrierSmoothReflection.lean),
especially `tendsto_circleIntegral_suzukiXiSmoothCarrier_reflection_heat`.

## Complete geometric excision and expanding area limit

Let `F=W_rho*S_r*B_(x,tau)` and `G=W_rho*K_(r,x,tau)`. For a hypothetical
right-half zero, `alpha` lies below the real spectral axis and `beta` above
it. On an upper rectangle enclosing `beta`, remove a small square centered
at `beta`. The four remaining rectangles give actual integrals of `G`.
The finite identity is exactly

```
outerBoundary(F) = areaOutsideSquare(G)+squareBoundary(F).
```

All differentiability and side/area integrability conditions are discharged
for the actual field. There are no additional punctures at carrier poles
or other xi zeros. Taking the square radius `q` to zero gives

```
limit_(q -> 0+) areaOutsideSquare(G)
  = outerBoundary(F)+2*pi*i*B_(x,tau)(beta)/m.
```

The positive sign on the right is required: the subtracted node contour
has negative source. The terminal theorem is
`tendsto_area_suzukiXiSmoothReflectionSource` in
[SuzukiCarrierSmoothExcision.lean](../RiemannGaussian/SuzukiCarrierSmoothExcision.lean).

The complete reflection-weighted outer boundary itself satisfies the
coarse independent estimate

```
abs(outerBoundary_[-R,R]x[0,R](F))
  <= 384*Im(alpha)^2*R^2/r*exp(-tau*R^2/4)
```

for `r,tau>0`, `R>=1`, `R>=2*abs(x)` and `R>=2*abs(Re(alpha))`.
It therefore tends to zero. Combining the two proved limits gives

```
limit_(R -> infinity) limit_(q -> 0+) areaOutsideSquare(G)
  = 2*pi*i*B_(x,tau)(beta)/m.
```

The order of limits is explicit. The inner expression is a limit of
four geometric area integrals, not a newly defined replacement for the
original density. The source has strictly positive imaginary part for
every hypothetical right-half zero. These are
`tendsto_suzukiXiSmoothReflectionSource_iterated_area` and
`suzukiXiSmoothReflectionSource_mass_im_pos` in
[SuzukiCarrierSmoothReflectionLimit.lean](../RiemannGaussian/SuzukiCarrierSmoothReflectionLimit.lean).

This closes the weighted contour assembly. It does not provide an
independent bound for the surviving area source. The exact identity is a
necessary consequence of the hypothetical zero and cannot establish its
own contradictory upper bound.

## Removing smoothing remains singular

At every regular point, Lean proves `S_r(z)->C(z)` and `J_r(z)->0` as
`r->0`. At an actual carrier pole, however, the exact formula is

```
J_r(z) = -2/r^2*conj(E'(z)/A(z))    when E(z)=0 and A(z)!=0.
```

This retains every pole order; `E'(z)` can vanish at a multiple pole.
In particular, pointwise vanishing off the poles does not justify removing
the area source from an integrated identity. No interchange of smoothing,
area integration, pole summation or expanding-window limits is proved here.

The next mathematical obligation is an independent one-sided estimate for
the complete reflection-weighted area, using the actual arithmetic and
retaining both signed terms. Any eventual bound strictly below the displayed
positive source would contradict the proved limit. A nonpositive imaginary
part would be sufficient, but is not proved.

One fixed positive smoothing radius already suffices for that contradiction;
this route need not remove smoothing. Removal is required only if an estimate
is transported back to the original unsmoothed carrier. The existing original
source-plus-positive-energy limit and complete pole/strip target remain
available, and neither has acquired an independent source ceiling here.

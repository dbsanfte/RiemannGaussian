# Reflection nodes, ordinary signed areas and vanishing current edges

This local Lean slice closes the reflection-node regularity and planar
integrability gaps in the [finite mass-current identity](suzuki-reflection-mass-integral.md).
It also bounds the two outer current edges independently. The signed
arithmetic upper bound needed for zero exclusion remains open.

The follow-up [angular cancellation theorem](suzuki-reflection-angular-decay.md)
now proves signed decay of the complete remainder through the reflected
node on each fixed upper rectangle as smoothing grows. It does not bound
the mass variation or exchange the smoothing and expanding-area limits.

## Actual fields and orientation

Use the original entire spectral xi pair `A=xi(1/2+i*z)` and `E=A+i*A'`.
For fixed `r>0`, spectral coordinate `z=x+i*y`, and the literal Gaussian
and reflection weight, set

```text
d = |E|^2 + r^2*|A|^2
U = |A|^2/d
S = i*A*conj(E)/d
W = -(1/(z-alpha)-1/(z-conj(alpha)))^2
B = 2*y*exp(-tau*((c-x)^2+y^2))
P = W*B
J = P*U*S
M = P*S*U_x
Remainder = 2*i*r^2*P_x*U*S + i*W*S*H
G = W*(B*V-i*S*H).
```

`H` is the actual companion heat source evaluated at `i*z`; `V` is the
full smoothed carrier source. The sign of the real horizontal derivative
is retained. No xi or eta denominator separation or simple-zero
assumption is imposed.

## The exact current at a node

[SuzukiReflectionMassRegularity.lean](../RiemannGaussian/SuzukiReflectionMassRegularity.lean)
uses a single analytic xi chart for both `U` and `S`. At a selected node
`a`, with true analytic multiplicity `m`, that chart gives

```text
C(z) = (z-a)*q(z),  q(a)=1/m
U*S = C(z)^2*conj(C(z))/(1+r^2*|C(z)|^2)^2.
```

Its cubic vanishing cancels the double pole of `W`. The theorem
`exists_suzukiXiPlanarReflectionMassCurrent_node_factor` proves an exact
neighborhood identity, including the existing central value:

```text
J(z) = conj(z-a)*p(z)
p is real smooth at a
p(a) = -B(a)/m^3.
```

`contDiff_suzukiXiPlanarReflectionMassCurrent` proves global real
smoothness through both nodes, all carrier poles and common xi zeros.
The exact real differential is

```text
D J(a)[v] = -B(a)/m^3 * conj(v).
```

This coefficient is independent of `r`. Smoothness therefore does not
imply that the derivative decreases when smoothing grows. No uniform
decay estimate near the node is inferred from the fixed-interval budget.

## Genuine planar integrability

[SuzukiReflectionLocalIntegrability.lean](../RiemannGaussian/SuzukiReflectionLocalIntegrability.lean)
constructs a smooth numerator for the full weighted field near either
node: `W*S*B = p(z)/(z-a)` off the center, with `p(a)=-B(a)/m`.
Differentiating this identity retains both signed source terms. The
existing local integrability of the complex inverse then proves
`locallyIntegrable_suzukiXiSmoothReflectionSource` on the entire plane.

[SuzukiReflectionMassArea.lean](../RiemannGaussian/SuzukiReflectionMassArea.lean)
also proves local integrability of `M` and the complete remainder. The
pointwise identity holds almost everywhere, since the two selected
points are planar-null. On every finite rectangle `K=[l,v] x [b,u]`,
including rectangles containing both nodes, the proved ordinary identity is

```text
integral_K G
 = 2*i*r^2 * integral_b^u (J(v+i*y)-J(l+i*y)) dy
   - 4*i*r^2 * integral_K M - integral_K Remainder.
```

The terminal theorem is
`integral_suzukiXiSmoothReflectionSource_eq_mass_rectangle`. Fubini,
the fundamental theorem and all component integrability are discharged.
This does not assert one-dimensional integrability of the source on a
horizontal line through a node.

## Independent edge bound and the surviving source

[SuzukiReflectionMassExhaustion.lean](../RiemannGaussian/SuzukiReflectionMassExhaustion.lean)
proves, for `K_R=[-R,R] x [0,R]`, `r>0`, `tau>=0`, `R>0` and
`2*|Re(alpha)|<=R`,

```text
|2*i*r^2 * integral_0^R (J(R+i*y)-J(-R+i*y)) dy|
  <= 256*Im(alpha)^2/(r*R^2).
```

`norm_suzukiXiReflectionMassEdge_le` is independent of arithmetic values
and valid for every Gaussian center. The quartic reflection weight
suffices even at zero heat time. These edges tend to zero with `R` at
fixed positive `r`.

For a hypothetical right-half zero and positive heat time, planar
integrability identifies the prior shrinking-square limit with the
ordinary area integral. Thus `tendsto_suzukiXiReflectionMass_signed_area`
proves

```text
-4*i*r^2 * integral_K_R M - integral_K_R Remainder
  -> 2*pi*i*B(conj(alpha))/m.
```

The limit has strictly positive imaginary part. No separate limits for
the two retained terms are asserted. The remaining goal is an independent
signed upper bound for this pair that contradicts that positive source,
for one fixed positive smoothing radius and heat time. The earlier
`C/r` envelope is not uniformly integrable near a node and does not
supply that bound. No new zero exclusion or RH proof follows here.

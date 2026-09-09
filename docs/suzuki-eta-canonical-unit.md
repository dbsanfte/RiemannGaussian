# Quantifying the full denominator's analytic factor

Lean now constructs and bounds the analytic factor left after removing
the complete local divisor of the actual cleared eta denominator. The
normalized complex logarithm and its derivative have logarithmic height
bounds. An exact carrier identity keeps the eta numerator, pole product
and analytic phase together.

The global signed source ceiling remains open. These separate absolute
estimates have a large polynomial cost and do not control the signed
weighted pole contribution.

## Actual decomposition

Use the [previously proved cleared denominator](suzuki-eta-local-pole-count.md)

```
J(s)=F(s)*eta'(s)+((1+R(s))*F(s)-F'(s))*eta(s),
F(s)=1-2*2^(-s),   R(s)=G'(s)/G(s),
G(s)*J(s)=F(s)^2*(xi(s)+xi'(s)).
```

For every `T>=2`, set `c_T=3/2+i*T` and `f_T(w)=J(c_T+w)`.
The new proof selects a radius

```
33/32 < r_T < 17/16
```

whose boundary contains no zero of `f_T`. The full canonical
decomposition supplies an analytic function `g_T`, nonzero on the
closed disk. Its divisor retains every genuine denominator order and
both extra dyadic orders. No simplicity assumption or prescribed
zero-free interior is used.

Write the complete canonical pole product as

```
P_T(w)=product_i canonicalFactor(r_T,i,w)^(divisor f_T(i)).
```

At regular points `f_T(w)!=0`, Lean proves the exact complex identity
`g_T(w)=P_T(w)*f_T(w)`. The extended canonical decomposition remains
available at the level of meromorphic germs throughout the disk.

Canonical factors have norm one on the chosen boundary, so the
maximum-modulus argument transfers the actual denominator bound:

```
abs(g_T(w)) <= C0*(T+4)^2,
abs(g_T(0)) >= b0 > 0,
b0=staticContourSafeEtaFactorFloor^2/staticContourSafeZetaDirichletMass.
```

See [SuzukiEtaCanonicalUnit.lean](../RiemannGaussian/SuzukiEtaCanonicalUnit.lean).

## Full complex logarithm and derivative

The proof constructs a normalized analytic logarithm `L_T` with

```
L_T(0)=0,    exp(L_T(w))*g_T(0)=g_T(w),
L_T'(w)=g_T'(w)/g_T(w).
```

Let `C=C0/b0=suzukiEtaLocalPoleJensenConstant` and
`M_T=log(1+C*(T+4)^2)`. For every `abs(w)<=1`, Lean proves

```
abs(L_T(w)) <= 64*M_T,
abs(g_T'(w)/g_T(w)) <= 8320*M_T,
abs(g_T(w)) >= b0*exp(-64*M_T).
```

The first estimate uses Borel--Carathéodory; the derivative estimate
uses a Cauchy circle of radius `1/64`. Both real and imaginary parts
of the logarithm remain in the exact recovery identity.

The separate inverse-factor cost is explicit:
`exp(64*M_T)=(1+C*(T+4)^2)^64`. This equality is also checked in Lean.
See [SuzukiEtaCanonicalLog.lean](../RiemannGaussian/SuzukiEtaCanonicalLog.lean),
especially `norm_logDeriv_suzukiEtaCanonicalUnit_le`.

## Original carrier and the remaining coupled estimate

For `s=c_T+w`, `z=i*(s-1/2)`, at a regular point of the cleared
denominator the actual carrier is exactly

```
C(z)=i*F(s)*eta(s)*P_T(w)*exp(-L_T(w))/g_T(0).
```

Its downstream norm estimate retains `abs(P_T(w))` explicitly and
bounds the other factors by

```
(3*staticContourLocalEtaMass*(T+4)/b0)*(1+C*(T+4)^2)^64.
```

For the previously constructed admissible vertical coordinates `-T`,
the required nonvanishing is discharged on the entire segment
`z=-T+i*y`, `0<=y<=1/2`, including both endpoints. Here `w=y-1`.
The new unit estimates and this segment instantiation are stated for
positive arithmetic height `T`; the previous pole-count theorem
already covers both signs.

See [SuzukiEtaCanonicalCarrier.lean](../RiemannGaussian/SuzukiEtaCanonicalCarrier.lean),
including `suzukiXiZeroCarrier_eq_canonicalPoleProduct` and
`norm_suzukiXiZeroCarrier_admissible_strip_le_canonicalPoleProduct`.

The displayed separate polynomial cost is too large for the quartic
contour weight to absorb. It therefore does not close the target bound.
The useful remaining object is the exact numerator--pole-product
combination with its analytic phase, coupled to both oriented strip
sides. Estimating these factors separately loses cancellation that
the exact identity preserves. No bound on that complete signed
combination, new zero exclusion or RH proof is asserted here.

This slice is locally validated only. Commits remain on hold.

# Angular cancellation and through-node remainder decay

The complete actual reflection remainder now has vanishing complex
integral on every fixed upper rectangle containing the reflected zero,
as the smoothing parameter grows. This closes the node obstruction in
the [finite area identity](suzuki-reflection-mass-area.md).
The signed normalized mass variation remains unbounded; no new zero
exclusion or RH proof follows.

The follow-up [mass profile theorem](suzuki-reflection-mass-profile.md)
now identifies the retained signed mass: its smoothing limit is the
full reflected source. Its constant angular component survives
perpendicular coupling, so remainder decay alone supplies no deficit.

## The actual fields

Keep the original entire xi pair `A`, `E`, and positive smoothing parameter
`r`. With the spectral coordinate `z=x+i*y`, write

```text
U = |A|² / (|E|²+r²|A|²)
S = i*A*conj(E) / (|E|²+r²|A|²)
W = -(1/(z-alpha)-1/(z-beta))²
B = 2*y*exp(-tau*((c-x)²+y²))
P = W*B
H = the complete companion heat source at i*z
Rem = 2*i*r²*P_x*U*S + i*W*S*H.
```

Here `beta=conj(alpha)`, and derivatives use the real spectral horizontal
coordinate. The new theorems use the existing definitions, including
their original values at carrier poles and common xi zeros.

## A common chart for all smoothing parameters

[SuzukiReflectionRemainderChart.lean](../RiemannGaussian/SuzukiReflectionRemainderChart.lean)
proves `exists_suzukiXiCarrier_uniform_mass_chart`. At a selected node
`a` of multiplicity `m`, one analytic function `q` and one neighborhood
work simultaneously for every real `r`:

```text
q(a) = 1/m,  w = z-a,  C = w*q(z)
S = C/(1+r²|C|²)
U*S = C²*conj(C)/(1+r²|C|²)².
```

Both identities include the central value. No simplicity assumption or
smoothing-dependent neighborhood is used.

`exists_suzukiXiReflectionMassRemainder_angular_chart` then gives the
exact punctured identity

```text
Rem(r,z) = N(z)*K(r,Q(z),w) + i*W(z)*S(r,z)*H(z)
K(r,q,w) = r²/(1+r²|w|²*q)² * conj(w)/w
N(a) = 4*i*B(a)/m³
Q(a) = 1/m².
```

`N` and `Q` are real smooth at the node and independent of `r`.
The exact coefficients retain both the Gaussian source and multiplicity.

## Cancellation before estimation

[ComplexAngularResolvent.lean](../RiemannGaussian/ComplexAngularResolvent.lean)
proves

```text
K(r,q,i*w) = -K(r,q,w).
```

A quarter-turn preserves planar area and the centered disk. With genuine
integrability proved for `q >= 0`,
`complexAngularResolventKernel_disk_cancellation` concludes that the
whole complex integral is exactly zero. Its translated version works
at every node. The proof does not estimate the leading harmonic by its
absolute value before integration.

[ComplexAngularCancellation.lean](../RiemannGaussian/ComplexAngularCancellation.lean)
proves the uniform coefficient estimate. If `q1,q0 >= d > 0`,
`|N1-N0| <= L*|w|` and `|q1-q0| <= M*|w|`, then

```text
|N1*K(r,q1,w)-N0*K(r,q0,w)|
  <= (L/d + 2*|N0|*M/d²)/|w|.
```

This holds for every real `r` and nonzero `w`. Smoothness supplies these
Lipschitz bounds on a single fixed neighborhood. The inverse distance
is locally integrable in two real dimensions.

## The complete actual remainder

[SuzukiReflectionRemainderDecay.lean](../RiemannGaussian/SuzukiReflectionRemainderDecay.lean)
applies the estimate to the actual `N,Q`, and bounds the complete
companion term by another `C/|w|`, uniformly in `r`.
The terminal local bound is
`exists_suzukiXiReflectionMassRemainder_angular_error_bound`:

```text
|Rem(r,z) - (4*i*B(a)/m³)*K(r,1/m²,z-a)| <= C/|z-a|.
```

At every fixed point the actual remainder tends to zero as `r` grows.
After subtracting the exactly cancelling harmonic, dominated convergence
therefore gives

```text
integral_closedBall(a,epsilon) Rem(r,z) dz -> 0.
```

`exists_tendsto_integral_suzukiXiReflectionMassRemainder_node` proves this
for every sufficiently small positive disk radius. The reflected-node
theorem supplies the upper node of every hypothetical right-half zero.
These are ordinary area integrals through the node, with no principal
value or puncture limit.

## Fixed finite areas and the remaining target

[SuzukiReflectionRemainderCompact.lean](../RiemannGaussian/SuzukiReflectionRemainderCompact.lean)
combines the node disk with an independently dominated compact exterior.
`tendsto_integral_suzukiXiReflectionMassRemainder_compact_reflected`
works for any compact region excluding `alpha` and containing `beta`
in its interior. The explicit rectangle theorem permits every fixed
upper rectangle `[l,v] × [b,u]` with `b >= 0` and `beta` strictly inside.
It holds for every real Gaussian center and heat parameter.

For `K_R=[-R,R] × [0,R]`, nonnegative heat time, and the stated node
containment and width conditions,
`tendsto_suzukiXiReflectionSource_add_mass_rectangle` further proves

```text
integral_K_R G(r,z) dz
  + 4*i*r²*integral_K_R M(r,z) dz -> 0, as r -> infinity,
```

where `G` is the original full source and `M=P*S*U_x` the retained signed
mass variation. The existing independent current-edge bound and the new
complete remainder decay discharge both error terms.

This does not give an independent bound for `M`. Nor does it prove
absolute remainder decay, a quantitative global rate, or an interchange
between `r -> infinity` and `R -> infinity`. The earlier expanding-area
source theorem takes `R -> infinity` at fixed positive `r`; that order
remains explicit. The next arithmetic task is still an independent
signed bound beating the positive source after the controlled errors.

# The surviving signed mass and its rescaled profile

The signed mass variation does not become negligible when smoothing grows.
On every fixed eligible upper rectangle it tends, with its original
coefficient, to the entire positive reflected-zero source. This is a
checked obstruction to obtaining a source deficit merely from increasing
smoothing. It is not a new zero exclusion or an independent arithmetic
upper bound.

The previous [angular cancellation theorem](suzuki-reflection-angular-decay.md)
remains intact: the complete remainder and current-edge contribution
vanish on fixed areas. The new results identify what survives them.

## The actual fields and scale

Use the original spectral xi pair `A`, `E=A+i*A'`, and

```text
U = |A|²/(|E|²+r²|A|²)
S = i*A*conj(E)/(|E|²+r²|A|²)
W = -(1/(z-alpha)-1/(z-beta))²
B = 2*Im(z)*exp(-tau*((c-Re(z))²+Im(z)²))
P = W*B
M = P*S*U_x.
```

Here `beta=conj(alpha)` is the upper reflected node of a hypothetical
right-half zero, and `m` is its original analytic multiplicity. The signed
area term in the source identity is `-4*i*r²*integral M`. Every derivative
uses the real spectral horizontal coordinate.

## One exact chart, including the coefficient derivative

[SuzukiReflectionMassNodeChart.lean](../RiemannGaussian/SuzukiReflectionMassNodeChart.lean)
constructs one analytic `q` and one smooth heat numerator `g`, independent
of smoothing, with

```text
q(a)=1/m,  g(a)=-B(a),  w=z-a,  Q(z)=|q(z)|²
U=|w*q|²/(1+r²|w*q|²)
S=w*q/(1+r²|w*q|²)
P=g/w².
```

The normalized-field identities include the central zero and work for
every real `r` on one common neighborhood. Differentiating that same
chart gives the actual signed variation, off the selected node:

```text
M(r,z) = g(z)*q(z)*(2*Re(w)*Q(z)+|w|²*Q_x(z))
           / (w*(1+r²|w|²*Q(z))³).
```

Terminal theorem: `exists_suzukiXiReflectionMassVariation_node_chart`.
The derivative `Q_x` is retained; it is not assumed small or omitted.
Genuine carrier poles and common/repeated xi zeros keep their original
definitions throughout the proof.

## The checked local limit

[SuzukiReflectionMassProfile.lean](../RiemannGaussian/SuzukiReflectionMassProfile.lean)
proves, for every nonzero complex `w`,

```text
-4*i*M(r,beta+w/r)
  -> (4*i*B(beta)/m³)*(1+conj(w)/w)/(1+|w|²/m²)³.
```

The terminal theorem is
`tendsto_suzukiXiReflectionMassVariation_reflected_profile`.
Before taking the limit, the exact rescaled expression still contains
`(|w|²/r)*Q_x(beta+w/r)`. Its decay follows from the proved continuity of
the local coefficient derivative. All other local coefficients converge
to their exact central values.

Thus the leading profile depends only on the Gaussian value and
multiplicity. Higher local analytic coefficients do not appear in this
limit. The full angular phase is retained: `conj(w)/w` changes sign under
a quarter-turn, while the constant `1` does not.

`tendsto_suzukiXiReflectionMassVariation_quarter_turn_pair` proves this
directly for two actual moving points:

```text
-4*i*(M(r,beta+w/r)+M(r,beta+i*w/r))
  -> 8*i*B(beta)/(m³*(1+|w|²/m²)³).
```

The limit is not zero at the upper reflected node. Perpendicular phase
coupling cancels the second harmonic and leaves twice the constant
component. This differs from the remainder, whose leading local kernel
contained only the second harmonic.

These are pointwise rescaled limits. They do not assert uniform profile
convergence, weak convergence of measures, or an interchange with area
integration. No theorem here evaluates the integral of the profile.

## The actual signed area limit

[SuzukiReflectionMassConcentration.lean](../RiemannGaussian/SuzukiReflectionMassConcentration.lean)
evaluates the area limit separately using the already proved exact
through-node source identity and independent boundary estimate.
For a fixed rectangle `K_R=[-R,R] × [0,R]`, with

```text
tau>0, R>=1, 2*|c|<=R, 2*|Re(alpha)|<=R,
```

`tendsto_suzukiXiReflectionMassVariation_smoothing_area` proves

```text
-4*i*r²*integral_K_R M(r,z) dz -> L
L = 2*pi*i*B(beta)/m.
```

Under the hypothetical right-half zero, `Im(L)>0`. The theorem
`eventually_suzukiXiReflectionMassVariation_im_gt_half_source` gives

```text
Im(-4*i*r²*integral_K_R M) > Im(L)/2
```

for every sufficiently large `r`. This is an actual lower bound for the
retained term, not the upper bound needed for the RH contradiction.
The area proof does not integrate the pointwise profile or exchange
smoothing with an expanding-region limit.

## Consequence for the active goal

The vanishing remainder removes a genuine analytic error, but the
retained term still carries the full source. The constant angular
component also survives the explicit phase coupling just tested.
Consequently neither small values of the normalized fields nor this
large-smoothing limit supplies the missing source deficit.

The active goal remains an independent arithmetic inequality for the
complete signed density, with the normalization and completion retained.
This audit does not rule out such an inequality or all other test
families. It rules out assuming that the retained mass becomes negligible
merely because the analytic error vanishes. No new zeta zero is excluded.

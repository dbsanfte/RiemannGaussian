# Reflection cancellation and the remaining source ceiling

The canonical reflection difference now gives a sharper actual contour
error and retains strictly positive Gram energy. The joint pole/strip
correction has a proved limit equal to its reflected source plus that
energy. An independent upper bound at the source, even with a vanishing
allowance, would suffice for the hypothetical-zero contradiction. That
upper bound remains open. No new zeta zeros have been excluded.

## The canonical test and exact cancellation

For a genuine zero rho, write

```
alpha = -i*(rho-1/2),  d = |Im(alpha)|,
rho* = the critical-line reflection partner,
alpha_rho* = conj(alpha).
```

The coefficients `(1,-1)` are fixed by this reflection involution. For
any mixed matrix M, retain the complete quadratic

```
Q_rho(M) = M_rho,rho - M_rho,rho* - M_rho*,rho + M_rho*,rho*.
```

It is the negative direction of the enclosed reflected-source matrix.
This test is used directly for every hypothetical right-half zero.

Let `C` be the actual Suzuki carrier and

```
P_rho(z) = 1/(z-alpha) - 1/(z-conj(alpha)).
F_rho(z) = Q_rho(C(z)/((z-conj(alpha_a))*(z-alpha_b))).
```

Lean proves exactly

```
F_rho(z) = -C(z)*P_rho(z)^2
```

at every complex point, including totalized node values. Away from the
two nodes it also proves

```
F_rho(z) = 4*Im(alpha)^2*C(z) /
             ((z-alpha)^2*(z-conj(alpha))^2).
```

The leading resolvent term has cancelled inside the original mixed
expression. Both cross terms are essential. These identities and the
exact source evaluation are in
[SuzukiCarrierReflectionContrast.lean](../RiemannGaussian/SuzukiCarrierReflectionContrast.lean).

## The improved actual error

On the proved safe upper half-plane, `|C|<=1`. Once both node distances
are at least `R/2`, the coupled integrand is bounded by `64*d^2/R^4`.
For the admissible outer rectangles and node-size conditions already
used in the [real contour comparison](suzuki-carrier-real-contour.md):

- the top costs at most `256*d^2/R^3`;
- each safe vertical piece costs at most `128*d^2/R^3`;
- their full signed reflection error costs at most `512*d^2/R^3`.

The integrals are coupled before these bounds are taken. Applying the
previous `32/R` entry estimate separately to four entries would give
`128/R`; the new proof retains the cancellation and the squared actual
distance from the critical line. The exact side splitting remains
available alongside the estimate.

See `norm_suzukiXiReflectionPairQuadratic_side_error_le` in
[SuzukiCarrierReflectionBounds.lean](../RiemannGaussian/SuzukiCarrierReflectionBounds.lean).

## Exact signed source and the retained energy

For `Re(rho)>1/2`, alpha lies below the real spectral axis and its partner
lies above it. Every sufficiently large actual upper rectangle encloses
the partner and excludes alpha. Lean discharges this enclosure and proves

```
Q_rho(Z) = -1/m_rho,
```

where Z is the original first-channel xi source and m is the genuine
analytic multiplicity. The signed source is therefore `-2*pi/m_rho`.
There is no simplicity assumption.

Let K be the complete matrix of genuine carrier-pole residues in the
rectangle, and S the signed matrix of the two retained vertical strip
segments. Define the joint correction

```
J_rho(l,r,u) = 2*pi*Re(Q_rho(K)) - Re(Q_rho(S)).
```

All pole orders and their full residue coefficients remain in K. The
exact real contour comparison gives

```
J_rho(l,r,u) = 2*pi/m_rho + E_rho[l,r] + e_rho(l,r,u),
|e_rho(l,r,u)| <= 512*d^2/R^3.
```

Here `E_rho[l,r]` is the actual reflection Gram on the real interval,
proved nonnegative. The finite source floor and actual admissible
rectangles satisfying it are proved in
[SuzukiCarrierReflectionComparison.lean](../RiemannGaussian/SuzukiCarrierReflectionComparison.lean).

The complete energy has the genuine representation

```
E_rho = integral_R |C(x)*P_rho(x)|^2 dx.
```

It is finite. The real carrier is nonzero almost everywhere, with both
exceptional divisors proved countable. For an off-axis node the reflection
difference is nonzero everywhere. Lean consequently proves `E_rho>0`.
The real-axis exhaustion retains the two mixed terms and converges to
this complete energy. These results are in
[SuzukiCarrierReflectionEnergy.lean](../RiemannGaussian/SuzukiCarrierReflectionEnergy.lean).

## The precise remaining upper bound

Actual expanding admissible families are constructed for every zero.
For every such family, Lean now proves the joint limit

```
J_rho(l_R,r_R,u_R) -> 2*pi/m_rho + E_rho,
E_rho > 0  under the hypothetical right-half-zero assumption.
```

Neither the pole series nor the strip sides are required to converge
separately. Their joint correction remains intact throughout the proof.

Thus an independent eventual estimate

```
J_rho(l_R,r_R,u_R) <= 2*pi/m_rho + a_R,
a_R -> 0,
```

would contradict the hypothetical zero. It needs no prescribed strict
deficit below the source: the actual positive energy supplies a margin.
`not_eventually_suzukiXiReflectionStripCorrection_le_source_add_vanishing`
checks this conclusion in
[SuzukiCarrierReflectionLimit.lean](../RiemannGaussian/SuzukiCarrierReflectionLimit.lean).

The ceiling must still be obtained independently from the arithmetic or
additional structure of the actual carrier. The source-plus-energy limit
is a consequence of the hypothetical zero and the exact contour identity;
it does not establish that ceiling. The retained reflected Poisson reserve
and complete signed xi expansion remain available for this open step.
Further improvements to the already vanishing outer error do not by
themselves supply the missing inequality.

The [finite signed pole budgets](suzuki-carrier-local-pole-budget.md) now
bound the complete imaginary logarithmic derivative by a local ordinate
band, with its omitted divisor proved nonpositive. They localize genuine
carrier poles to actual Jensen disks and bound the carrier outside those
disks. They do not yet control the weighted residue contribution in J.

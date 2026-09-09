# Complete finite mixed carrier contour

The actual Suzuki mixed carrier now has a constructed finite rectangular
residue formula. Every pole order, xi-node coefficient, contour orientation
and mixed index is retained. The signed matrix identity separates the
known xi source from the full carrier-pole correction. It does not yet
bound that correction or prove the global arithmetic inequality. No new
zeta-zero exclusion or `13/18` certificate is established.

## Removing every negative Laurent coefficient

For an analytic numerator F and a local model `f(z)=F(z)/(z-c)^m`, the
complete principal part is

```text
J_(m,F,c)(z) = [sum_(k<m) (z-c)^k*F^(k)(c)/k!]/(z-c)^m
            = sum_(k<m) [F^(k)(c)/k!]*(z-c)^(k-m),   z != c.
```

Taylor's theorem constructs an analytic representative of f-J near c.
Finitely many such local remainders patch into one analytic representative
after subtracting the full finite principal sum. Merely subtracting the
simple residue would not remove a multiple pole.

The rectangular primitive identity is proved using the fundamental theorem
of calculus on all four sides; it does not require a primitive to be
analytic inside the rectangle. Consequently every integer Laurent power
except -1 integrates to zero. The complete principal part has integral

```text
integral_(counterclockwise rectangle) J(z) dz = 2*pi*i*r,
r = 0 if m=0, otherwise F^(m-1)(c)/(m-1)!.
```

Entry points:

- `exists_finitePole_analytic_regularization` in
  [FinitePoleRegularization.lean](../RiemannGaussian/FinitePoleRegularization.lean).
- `rectangularBoundaryIntegral_eq_finitePole_residues` in
  [RectangularPoleIntegral.lean](../RiemannGaussian/RectangularPoleIntegral.lean).

## Actual Suzuki pole data

Keep the repository's original functions and coordinates:

```text
A(z)=xi(1/2+i*z),    E(z)=A(z)+i*A'(z),
C(z)=i*A(z)/E(z)    where E(z)!=0,
alpha_rho=-i*(rho-1/2),
F_(rho,sigma)(z)=C(z)/[(z-conj(alpha_rho))*(z-alpha_sigma)].
```

The literal carrier definition, including its exceptional point values,
is retained. Quotient identities are applied only where their denominators
are nonzero, or on proved punctured neighborhoods.

At every xi node c, the original mixed local model is `L/(z-c)+p(z)`
with p analytic. Its exact coefficient is

```text
L = 1/m_c if conj(alpha_rho)=c=alpha_sigma, otherwise 0.
```

This already accounts for every analytic xi multiplicity m_c. The mixed
local numerator `L+(z-c)*p(z)` has value L at c. Removable xi-node terms
are retained with zero residue.

Away from the xi divisor, the local order is the actual analytic order
of E. Its full mixed numerator is exactly the one used in the preceding
[carrier-pole residue theorem](suzuki-carrier-reflected-reserve.md).
Thus the complete local coefficient agrees with the original arbitrary-order
circle residue at every genuine E pole, and is zero at every regular point.
See [SuzukiCarrierFinitePoles.lean](../RiemannGaussian/SuzukiCarrierFinitePoles.lean).

## Actual finite windows and admissible contours

The potential singular set is exactly `{A=0} union {E=0}`. The actual
entire product A*E is nonzero at i, so this set is finite in every compact
region and countable globally. A contour window contains every point of
this set in the closed rectangle `[l,r] x [b,u]`.

Admissibility means `l<r`, `b<u`, and the four complete side lines avoid
this set. This condition is proved achievable by avoiding its countable
real and imaginary coordinate projections. For every `R>=1` and `delta>0`,
there is an actual admissible upper rectangle with

```text
-R-1 < l < -R,       R < r < R+1,
0 < b < min(delta,1/2),       R < u < R+1.
```

At every admissible rectangle, the original mixed channel is integrable
on each side. Its entire interior analytic remainder is constructed from
the complete local models; no omitted analytic hypothesis is presumed.

## Explicit source plus the complete pole correction

Let `Z_(rho,sigma)(R)` be `1/m_sigma` when
`conj(alpha_rho)=alpha_sigma` and that node lies in the rectangle, and
zero otherwise. Let

```text
K_(rho,sigma)(R) = sum_(c in rectangle, E(c)=0, A(c)!=0)
                     r_(rho,sigma)(c),
```

where r is the full arbitrary-order mixed residue. The actual identity is

```text
integral_(counterclockwise R) F_(rho,sigma)(z) dz
  = 2*pi*i * [Z_(rho,sigma)(R)+K_(rho,sigma)(R)].
```

This is `suzukiXiMixedCarrierChannel_rectangle_eq_source_add_poles` in
[SuzukiCarrierFiniteContour.lean](../RiemannGaussian/SuzukiCarrierFiniteContour.lean).
Both ordered nodes, all complex residues and all pole multiplicities
survive. The remaining correction is the literal complete finite pole
sum, rather than a chosen family or an assumed remainder.

## The signed mixed matrix and its remaining boundary terms

Write B for the left-to-right bottom integral and V for the other three
sides, with the top subtracted, the right traversed upward and the left
downward. Define the displaced signed matrices

```text
H_b(rho,sigma) = [B(rho,sigma)-conj(B(sigma,rho))]/(2*i),
H_V(rho,sigma) = [V(rho,sigma)-conj(V(sigma,rho))]/(2*i).
```

The finite comparison is exactly

```text
H_b + H_V = pi * [Z+Z* + K+K*],
```

where the star means conjugate transpose, including the exchange of both
mixed indices. The richer first-channel equality remains available before
this projection. This theorem holds for every pair of genuine zeros, so
no coefficient-family search or diagonal truncation is involved.

The actual outer top integral is bounded by `16/R` whenever its height
is at least R, its width is at most 4R, and `R>=1`. This applies to the
variable admissible upper rectangles above. The proof uses the already
established carrier bound outside the strip and both original node gaps.
The matrix comparison and this bound are in
[SuzukiCarrierFiniteGram.lean](../RiemannGaussian/SuzukiCarrierFiniteGram.lean).

The subsequent [real-boundary slice](suzuki-carrier-real-contour.md) now
identifies the displaced matrix with the actual truncated Gram in the
limit, for every pair without a repeated real node. It also proves the
real-bottom contour identity directly and bounds the combined safe
outer sides by `32/R`. The two fixed-height strip segments and complete
coupled pole correction still need an independent signed bound. The
repeated real-node separated channel still requires its principal value
and half-residue term; the noncolliding limit does not cover that case.

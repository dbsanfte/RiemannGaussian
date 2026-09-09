# Actual real Gram and a finite-height strip correction

This slice closes the finite real-axis boundary step for every mixed pair
without a repeated real node. It also bounds the top and the parts of the
vertical sides above the zero strip. The independent signed bound inside
the strip remains open; no new zeta zeros have been excluded.

## The boundary limit

Write `A(z)=xi(1/2+i*z)`, `E=A+i*A'`, and let `C` denote the literal
Suzuki carrier already defined in Lean. For spectral nodes
`alpha_rho=-i*(rho-1/2)`, the first mixed channel is

```
F_rho,sigma(z) = C(z) / ((z-conj(alpha_rho))*(z-alpha_sigma)).
```

The condition is

```
conj(alpha_rho) != alpha_sigma  or  Im(alpha_sigma) != 0.
```

It is symmetric under exchanging the mixed indices and holds for every
pair whose second node is off the real axis. In particular, it covers all
mixed pairs of off-axis zeros, including each hypothetical right-half
zero and its reflected partner. It is not a choice of coefficient family.

Every real `E` zero is an `A` zero. At each such point the complete
first-channel principal part vanishes under the stated condition. Full
finite Laurent regularization supplies an analytic representative along
any compact real segment, equal to the literal channel outside a finite
complex set. An injective line parametrization meets this exceptional
set at only finitely many parameters, so all original line integrals
are unchanged.

Compactness of the segment supplies a common analytic neighborhood and
a uniform integrable majorant for small displacements. Consequently

```
B_rho,sigma(b) = integral_l^r F_rho,sigma(x+i*b) dx
B_rho,sigma(b) -> B_rho,sigma(0)  as b -> 0.
```

The convergence is two-sided. Coupling the conjugate-transposed entry
before taking the limit gives

```
(B_rho,sigma(b) - conj(B_sigma,rho(b))) / (2*i) -> H_rho,sigma[l,r],
```

where `H[l,r]` is the actual common-carrier Gram integral. Its real
integrand is `conj(C(x))*C(x)` divided by the same mixed denominator.
As arbitrary endpoints exhaust the real axis, `H[l,r]` converges to the
existing complete Gram entry. This last convergence holds for all pairs
and has no asserted rate.

The repeated real-node separated channel is excluded from the first
limit: it requires its principal value and half-residue correction.
The existing common-subtraction and principal-value theorems remain
available for that case.

These results are in
[AnalyticHorizontalBoundary.lean](../RiemannGaussian/AnalyticHorizontalBoundary.lean)
and [SuzukiCarrierRealBoundary.lean](../RiemannGaussian/SuzukiCarrierRealBoundary.lean).

## Exact contour with a real bottom

The generic residue theorem now permits finitely many removable points
on a rectangle's boundary, provided their entire principal parts and
residues are proved zero. It preserves the literal values at those
points in the original line integrals.

The actual upper rectangle has bottom zero and three side lines avoiding
the complete xi and `E` singular set. Such rectangles exist at every
outer scale `R>=1`, with left, right and top coordinates within one of
`-R`, `R` and `R`, respectively. Real xi nodes may lie on the bottom.
All analytic and integrability premises are discharged for the original
mixed channel.

Let `Z` be the explicit reflected xi source and `K` the sum of all genuine
`E`-pole residues in the rectangle. The source is `1/m_sigma` precisely
when the reflected pair matches and its node is enclosed, and zero
otherwise. Every pole retains its genuine order and full Taylor-jet
residue. With `V` the signed matrix of the three remaining oriented sides,
Lean proves exactly

```
H[l,r] + V[l,r,u] = pi * (Z + Z* + K + K*).
```

Here `*` exchanges both indices and takes the complex conjugate.
The exact first-channel contour identity is retained before this
projection. There is no displaced-bottom or boundary-limit premise
left in the displayed real Gram comparison.

See [RectangularRemovableBoundary.lean](../RiemannGaussian/RectangularRemovableBoundary.lean)
and the terminal theorem
`suzukiXiTruncatedGram_add_otherSides_eq_source_and_poles` in
[SuzukiCarrierRealContour.lean](../RiemannGaussian/SuzukiCarrierRealContour.lean).

## Quantitative removal of the safe outer sides

Split each vertical side exactly at height `1/2`. Let `S[l,r]` be the
signed matrix of only the two oriented segments with `0<=Im(z)<=1/2`.
For

```
R >= 1,
R <= |l|, |r|,
2*|Re(alpha_rho)| <= R,  2*|Re(alpha_sigma)| <= R,
R <= u <= 2*R,  |r-l| <= 4*R,
```

the actual carrier bound `|C(z)|<=1` above height `1/2` gives a mixed
integrand bound `4/R^2`. Each safe vertical integral therefore costs
at most `8/R`; the top costs at most `16/R`. The exact side splitting
is proved before applying these bounds. It yields

```
|V[l,r,u] - S[l,r]| <= 32/R
|H[l,r] + S[l,r] - pi*(Z + Z* + K + K*)| <= 32/R.
```

These are per-entry complex norm bounds with both indices retained.
They hold for every pair satisfying the explicit node and boundary
conditions above. For any fixed finite set of nodes, the size conditions
hold once `R` is sufficiently large. No norm-square substitution is
made for the nonreal pole coefficients.

The terminal theorem is `norm_suzukiXiTruncatedGram_strip_comparison_le` in
[SuzukiCarrierContourStrip.lean](../RiemannGaussian/SuzukiCarrierContourStrip.lean).

## Remaining independent inequality

The uncertainty is now localized to the signed carrier-pole matrix and
the two fixed-height strip segments. The already-proved reflected
Poisson reserve must stay coupled to that matrix. The bound `32/R`
controls the discarded safe sides; it is not a bound on these retained
terms or on the location of a zeta zero. Establishing an independent
inequality that beats the reflected source remains the RH-strength
step of this route. The subsequent
[reflection-contrast slice](suzuki-carrier-reflection-contrast.md) retains
the canonical pair before estimation, improves its safe error to cubic
decay, and proves a strictly positive actual limiting energy. Consequently
an independent source ceiling with a vanishing allowance would suffice;
that ceiling remains unproved.

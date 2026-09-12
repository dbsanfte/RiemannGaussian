# Zero exclusion from retained Gaussian curvature

The theorem `exists_eventual_strip` in
[GaussianFermiCurvatureZeroFree.lean](../RiemannGaussian/GaussianFermiCurvatureZeroFree.lean)
proves that there exists a finite `T>=1` such that every nontrivial zero
`rho=beta+i*t` with `abs(t)>=T` satisfies

\[
\frac{3}{16\log|t|}<\beta<1-\frac{3}{16\log|t|}.
\]

The same module proves literal `riemannZeta(s)!=0` on the corresponding
closed right edge. Every arithmetic and analytic premise is discharged.
The height threshold is existential and has not been numerically
evaluated. This is an edge exclusion, not a proof of RH or a fixed-width
interior strip at all heights.

## The information retained in the Gaussian bound

The existing exact shifted identity is

\[
G_1(-x)=e^{x^2/4}\left(\frac{\sqrt\pi}{2}
+\int_{-x/2}^0 e^{-v^2}\,dv\right).
\]

[GaussianHalfLaplaceCurvature.lean](../RiemannGaussian/GaussianHalfLaplaceCurvature.lean)
retains curvature in the finite interval. The exponential tangent gives,
for `v^2<=h^2`,

\[
e^{-v^2}\le\frac1{1+v^2}\le1-\frac{v^2}{1+h^2}.
\]

For `h>=0`, integration yields

\[
\int_{-h}^0e^{-v^2}\,dv\le h-\frac{h^3}{3(1+h^2)}.
\]

The exact interval identity remains available upstream. Only its upper
estimate is replaced. At the required negative damping, this gives the
Lean-checked enclosure `G_1(-9/20)<=1167/1000`. The integrated tangent gives
the source enclosure `G_1(19/1000)>=1753/2000`.

## A general feedback theorem for the complete divisor

The theorem `exists_eventual_common_log_margin` in
[ZetaLogRegionBand.lean](../RiemannGaussian/ZetaLogRegionBand.lean) applies to
**any positive coefficient `a` with a proved eventual logarithmic strip**.
At every sufficiently large `H`, the margin `a/log(H)` is positive,
less than `1/4`, and valid simultaneously for every actual zero with
`abs(Im(rho))<=H`.

The low zeros are not omitted. Below the original threshold, the existing
positive global Fermi margin controls them. Above it, monotonicity of
`a/log(t)` supplies the comparison. Once `a/log(H)` is below the fixed
low-height margin, the two ranges give one common margin.

The present exclusion feeds the earlier proved coefficient `9/50` through
this generic theorem. The new coefficient `3/16` is then fed back through
the same theorem by `exists_eventual_common_margin`, making the latest
region available to subsequent common-margin phase budgets. The existing
global function `zetaFermiZeroMargin` and older squarefree-radius theorems
still have their original `3/20` eventual formula; they are not silently
redefined by this construction.

## Uniform surplus and the actual contradiction

Write `L=log(abs(t))`, `H=48*abs(t)`, `m=9/(50*log(H))` and
`B=4/(25*L^2)`. For `L>=100000`, Lean proves
`1799/10000<=L*m<=9/50`, and this Gaussian scale is admissible.

The comparison in
[GaussianFermiCurvatureProfile.lean](../RiemannGaussian/GaussianFermiCurvatureProfile.lean)
is uniform for the whole established coefficient class
`0<=a0<=37/200`, `a1>=79/250`, `M<=61/100`. With
`1799/10000<=mu<=9/50`, it gives

\[
a_0G_1(-5\mu/2)+M/10+1/20000
\le a_1G_1\bigl(5(3/16-\mu)/2\bigr).
\]

The original exact phase family satisfies these same bounds; no new
phase coefficients are fitted. Exact dilation gives source at least

\[
a_0G_B(-m)+ML/4+L/8000
\]

for a proposed zero within distance `3/(16L)` of the right edge. The full
pole and gamma cost is at most `a0*G_B(-m)+M*L/4+8`. The original complete
divisor allowance eventually bounds its weighted tail cost by one. Actual
multiplicity is at least one, so such a zero would require `L/8000<=9`,
contradicting `L>=100000`. Horizontal reflection gives the other edge.

The newer width-independent Fisher tail estimate is not needed for this
coefficient improvement: the earlier tail already tends to zero. The gain
comes from feeding back the stronger margin and retaining Gaussian
curvature in the leading pole estimate.

## Scope of the remaining problem

The finite threshold combines the common-band threshold, the older global
margin transition and the whole-divisor allowance threshold, as well as
the logarithmic lower bound. `exp(100000)` alone does not suffice. No
numerical zero-height verification or imported external zero-free theorem
is assumed.

The independent signed ordinary-prime bound and RH remain open. The
width still tends to zero with height. Repeated feedback has not been
proved to reach the critical line. These elementary Gaussian inequalities
and the coefficient improvement are not claimed to be historically novel
or stronger than the best published zero-free regions.

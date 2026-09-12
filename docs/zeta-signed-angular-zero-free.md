# Signed angular control in the actual zero-free theorem

For every fixed `0<A<pi/(140*log(2))`, Lean proves a finite threshold
`T(A)>=2` such that every actual nontrivial zero `rho=beta+i*t` with
`abs(t)>=T(A)` satisfies

```text
A*log(log(abs(t)))/log(abs(t)) < beta
  < 1-A*log(log(abs(t)))/log(abs(t)).
```

The terminal theorem is
[`ZetaLogLogZeroFree.exists_eventual_strip`](../RiemannGaussian/ZetaLogLogZeroFree.lean#L62).
The same module proves literal nonvanishing on the corresponding closed
right edge and margins for the complete bounded-height divisor. Every
analytic and arithmetic premise is discharged. The coefficient-dependent
threshold is existential and has not been numerically evaluated.

## Recover the whole complex boundary moment first

For an analytic function on a neighborhood of a positive closed disc,
nonzero at the center and on its boundary, write `avg_R` for the normalized
circle average and define

```text
M_R(f) = avg_R (2*z/z^2 * log(norm(f(z)))).

logDeriv(f,0) = M_R(f)
  + sum_a divisor(f,ball(0,R),a)*(-1/a+conj(a)/R^2).
```

[`AnalyticDiscBoundaryMoment`](../RiemannGaussian/AnalyticDiscBoundaryMoment.lean)
proves this exact complex identity. Canonical factorization removes the
complete interior zero divisor and preserves the boundary norm. A
normalized analytic logarithm and the Herglotz--Poisson representation
identify the entire derivative of the resulting nonvanishing function.
No norm or real projection replaces that richer identity.

Its negative real projection is exactly

```text
Re(-M_R(f)) = (2/R^2)*avg_R (-Re(z)*log(norm(f(z)))).
```

This kernel changes sign between the two semicircles. To bound it above,
suppose the actual boundary values satisfy

```text
Re(z)<=0 =>  log(norm(f(z))) <= B,
Re(z)>=0 => -log(norm(f(z))) <= C.
```

The exact projection masses are

```text
avg_R max(Re(z),0) = avg_R max(-Re(z),0) = R/pi.
```

[`SignedCircleProjection`](../RiemannGaussian/SignedCircleProjection.lean)
proves these masses and the signed integral inequality for every
circle-integrable real boundary function with the stated semicircle
bounds. Thus
[`AnalyticDiscSignedBoundary.neg_moment_re_le`](../RiemannGaussian/AnalyticDiscSignedBoundary.lean)
gives

```text
Re(-M_R(f)) <= 2*(B+C)/(pi*R).
```

The assumptions are boundary estimates with opposite directions. This
is a bound on the signed projection; it does not assert the same bound
for the norm of the full complex derivative. The analytic mechanism is
classical. No claim of historical novelty is made.

## Both semicircle bounds hold for actual zeta

Use the existing actual growth data

```text
alpha_k=1/(2^(k+2)-2),          delta_k=(k+2)*alpha_k,
c=1+x+i*t,                    0<x<=delta_k/4,
E_k(x,t)=profile_k(t)+14+log(1+1/x).
```

For `k>=2` and `abs(t)>=2`, the full radius-`delta_k` disc is analytic
and lies in the already proved Gaussian strip. On its left semicircle,
the Gaussian bound gives `log(norm(zeta(c+z)))<=profile_k(t)+14`.
Every right-pointing displacement lies in the Euler half-plane, where
the full Mobius L-series bound proves

```text
-log(norm(zeta(c+z))) <= log(1+1/x),       Re(z)>=0.
```

[`ZetaNearOneAngularBound.right_arc_lower`](../RiemannGaussian/ZetaNearOneAngularBound.lean)
has no zero-free-region or hypothetical-zero premise. It supplies the
missing direction of control on that entire semicircle.

At every eligible zero-free radius `r<=delta_k`, the full complex
boundary identity holds for translated zeta. Every other coupled local
zero term has favorable real sign. For a selected zero at the center's
ordinate, with `d=x+1-beta<delta_k`, passing through the proved sequence
`r_n -> delta_k` gives

```text
Re(-zeta'(c)/zeta(c))
 <= 2*E_k(x,t)/(pi*delta_k) - m_rho*(1/d-d/delta_k^2).
```

The same module proves the upper bound without a selected zero.
Multiplicity, the reciprocal-distance source and its radial correction
remain together. The outer sphere may contain zeros; its nonvanishing
is not assumed. The [full-radius construction](zeta-full-radius-zero-free.md)
supplies the required approaching circles.

## The actual prime contradiction and joint limit

The genuine three-height prime positivity theorem and real-axis pole
bound now give

```text
B_k(x,t)=1344*log(22)+(8*E_k(x,t)+2*E_k(x,2*t))/(pi*delta_k),

4*m_rho*(1/d-d/delta_k^2) <= 3/x+B_k(x,t).
```

At `x=6*u`, an actual zero with `1-beta<=u` and `28*u<delta_k` forces

```text
cost=14*u*B_k(x,t)+392*(u/delta_k)^2 >= 1.
```

[`ZetaAngularPrimeBudget`](../RiemannGaussian/ZetaAngularPrimeBudget.lean)
proves these statements with all prime, analytic and multiplicity
inputs discharged. The selected source and radial correction have
exactly their original coefficients.

On the [joint order-height schedule](zeta-log-log-zero-free.md),
`L=log(abs(t)+2)`, `ell=log(L)`, `k=floor(ell/b)`, `u=C*ell/L` and
`b>log(2)`, all moving center and width corrections tend to zero, and

```text
u*B_k(x,t) -> 10*C*b/pi,             cost -> 140*C*b/pi.
```

For `140*C*log(2)<pi`, choose `log(2)<b<pi/(140*C)`. The complete cost
is eventually below one while all geometric conditions hold on this
same schedule. This contradicts a zero in the stated margin. Transfer
from smoothed to ordinary logarithms preserves the entire open
coefficient range; reflection gives the other strip edge.

## Arithmetic consequence and next targets

For every coefficient in the larger range, the actual quotient
`zeta(s)/zeta(2*s)` is analytic on a neighborhood of the entire closed
disc centered at `3/2+i*y` with radius

```text
R_A(y)=1+A*log(log(H))/(2*log(H)),       H=2*abs(y)+3,
```

above a coefficient-dependent threshold. The same result supplies
[all marked response bounds and fixed-mark decay](../RiemannGaussian/ZetaSquarefreeLogLogRadius.lean).
The signed prime envelope remains explicit; it has not been replaced
by an assumed uniform estimate for growing prime sets.

The next phase target is a theorem for general nonnegative trigonometric
families, so that the selected source, real pole and all oscillatory
allowances can be compared symbolically. No such extension of this
angular prime budget is claimed in this slice.

The [published-region survey](zero-free-region-transport.md) records
the distinction between classical logarithmic, Littlewood and
Vinogradov--Korobov regions. A competitive coefficient alone does not
establish a world-best region: comparisons must use proved height
ranges. This threshold is still unevaluated. Improving the asymptotic
shape beyond Littlewood also requires stronger near-one growth than
the present derivative recursion supplies.

The separate ordinary-prime source at a hypothetical fixed right-half
zero still needs an independent cofinal bound `Re(P_N)>=-1+epsilon`
with a fixed `epsilon>0`. Its known negative multiplicity limit would
then contradict that bound. The stronger squarefree decay does not
provide it; RH remains open.

## Validation

The warning-as-error full build passes all 10,273 jobs; the focused
arithmetic build passes all 4,905 jobs. All nine affected modules pass
strict direct elaboration and verbose declaration lint. Explicit axiom
audits cover 41 public theorems, including the 24 added in the five new
modules, using only `propext`, `Classical.choice` and `Quot.sound`.

All new modules are root-imported. The whole-project declaration lint and
strict inventory pass across 1,426 compiled project modules and 30,365
declarations, including 26,623 theorems. There are no project axioms or
placeholder-dependent declarations, and `rhImplied` remains false.
The source scan covers 1,569 Lean files. Documentation links, whitespace,
README scope and generated-artifact reproducibility are checked for the
complete slice.

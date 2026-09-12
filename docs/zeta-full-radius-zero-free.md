# Full-radius signed control and the larger proved region

For every fixed `0<A<1/(140*log(2))`, Lean proves an eventual exclusion
width `A*log(log(abs(t)))/log(abs(t))` for actual nontrivial zeta zeros:

```text
exists T(A)>=2, for every rho=beta+i*t with abs(t)>=T(A),
  A*log(log(abs(t)))/log(abs(t)) < beta
    < 1-A*log(log(abs(t)))/log(abs(t)).
```

The terminal theorem is
[`ZetaLogLogZeroFree.exists_eventual_strip`](../RiemannGaussian/ZetaLogLogZeroFree.lean#L62).
The corresponding literal closed-right-edge nonvanishing and complete
bounded-height margins are proved in the same module. Each coefficient's
threshold is existential and unevaluated; this is not a numerical
height certificate or a claim of an optimal coefficient. RH remains open.

## The full analytic disc is already available

Retain the actual near-one growth data

```text
alpha_k=1/(2^(k+2)-2),             delta_k=(k+2)*alpha_k,
c=1+x+i*t,                       0<x<=delta_k/4,
E_k(x,t)=profile_k(t)+14+log(1+1/x).
```

For `k>=2`, `delta_k<=2/7`. Thus the entire closed disc
`norm(s-c)<=delta_k` has

```text
1-delta_k <= Re(s) <= 3/2,       abs(Im(s)-t)<=1.
```

The already proved Gaussian strip bound therefore controls all of it.
For `abs(t)>=2`, the pole at one is excluded throughout the disc.
[`ZetaNearOneFullDisc`](../RiemannGaussian/ZetaNearOneFullDisc.lean)
proves its geometry, actual analyticity and the unchanged growth
allowance. Here “full radius” means this entire strip-width radius
`delta_k`; it is not asserted to be the largest possible analytic disc.

## Boundary zeros do not require shrinking by a fixed fraction

An analytic function nonzero at the center has a complete finite zero
divisor on the closed disc. Consequently, every nonempty interval of
radii below the outer radius contains a zero-free circle.
[`AnalyticDiscBoundarySequence`](../RiemannGaussian/AnalyticDiscBoundarySequence.lean)
proves this and constructs positive radii `r_n<R` tending to `R` with
zero-free spheres. The outer sphere may contain zeros.

At each such sphere,
[`AnalyticDiscCanonicalControl.exists_controlled_decomp`](../RiemannGaussian/AnalyticDiscCanonicalControl.lean)
keeps the entire complex identity

```text
logDeriv(f,0)=logDeriv(g_n,0)
  + sum_a divisor(f,ball(0,r_n),a)*(-1/a+conj(a)/r_n^2),

norm(logDeriv(g_n,0)) <= 2*(B+C)/r_n.
```

The constants require only the actual boundary growth and center cost.
Canonical removal preserves the boundary norm and increases the center
norm. The [sharp Carathéodory estimate](zeta-caratheodory-zero-free.md)
provides the residual bound. These general theorems can receive another
proved growth profile without rebuilding the divisor argument.

## The selected source and correction pass together to the radius

For translated zeta, every local zero lies left of the Euler-side center.
The real part of each complete coupled kernel, including its actual
multiplicity, is nonnegative. Let the selected actual zero be
`rho=beta+i*t` and put `d=x+1-beta<delta_k`. Every sufficiently late circle
encloses it. Its full contribution gives

```text
Re(-zeta'(c)/zeta(c))
 <= 2*E_k(x,t)/r_n - m_rho*(1/d-d/r_n^2).
```

The explicit right side is continuous as `r_n` tends to `delta_k>0`.
The resulting theorem
[`neg_logDeriv_re_le_sub_zero`](../RiemannGaussian/ZetaNearOneFullRadius.lean)
is

```text
Re(-zeta'(c)/zeta(c))
 <= 2*E_k(x,t)/delta_k - m_rho*(1/d-d/delta_k^2).
```

The same module proves the upper bound `2*E_k/delta_k` without selecting
a zero. Only the explicit scalar bounds need a limit; the canonical
decompositions may vary with the radius. Every interior source is
included eventually and outer-boundary zeros cause no unproved
nonvanishing assumption.

## The complete prime contradiction

The genuine three-height von Mangoldt positivity theorem and real-axis
pole bound give

```text
B_k(x,t)=1344*log(22)+(8*E_k(x,t)+2*E_k(x,2*t))/delta_k,

4*m_rho*(1/d-d/delta_k^2) <= 3/x+B_k(x,t).
```

At `x=6*u`, an actual zero with `1-beta<=u` and `28*u<delta_k` forces

```text
cost=14*u*B_k(x,t)+392*(u/delta_k)^2 >= 1.
```

[`ZetaFullRadiusPrimeBudget`](../RiemannGaussian/ZetaFullRadiusPrimeBudget.lean)
proves both statements with the prime, analytic and multiplicity inputs
discharged. The earlier intermediate-radius estimates remain available
as separate theorems.

Use the [joint order-height schedule](zeta-log-log-zero-free.md):
`L=log(abs(t)+2)`, `ell=log(L)`, `k=floor(ell/b)`, `u=C*ell/L` and
`b>log(2)`. All moving center and width corrections already tend to zero.
The full-radius budget now satisfies

```text
u*B_k(x,t) -> 10*C*b,             cost -> 140*C*b.
```

The required `k>=2` holds eventually on this same schedule. For
`140*C*log(2)<1`, choose `log(2)<b<1/(140*C)`. The actual cost is then
eventually below one, contradicting a zero in that margin. The full
ordinary-log coefficient range, both strip edges and complete low divisor
are retained.

## Arithmetic consequence and remaining work

At `c=3/2+i*y`, `H=2*abs(y)+3`, the actual squarefree quotient
`zeta(s)/zeta(2*s)` has an analytic neighborhood of the full radius

```text
R_A(y)=1+A*log(log(H))/(2*log(H))
```

above the coefficient-dependent threshold. The larger allowed
coefficient range supplies every existing marked response bound and
fixed-mark decay theorem in
[`ZetaSquarefreeLogLogRadius`](../RiemannGaussian/ZetaSquarefreeLogLogRadius.lean).
The signed prime envelope remains in those bounds.

The independent signed ordinary-prime lower bound at a hypothetical
interior zero remains open. The [arithmetic rate audit](prime-tail-literature-audit-2026-09-11.md)
explains why a subexponential PNT-error estimate alone is insufficient at
its factorial source normalization. The [published-region survey](zero-free-region-transport.md)
records stronger growth tools worth formalizing.

One remaining loss in the present local detector is replacing the angular
boundary growth profile by its uniform maximum. Its exact complex
canonical identity and signed boundary norm data remain available for
examining that loss. This is a next proof target, not an additional
estimate already established here.

## Validation

The warning-as-error full build passes all 10,268 jobs; the focused
arithmetic build passes all 4,899 jobs. Nine affected modules pass strict
direct compilation and verbose declaration lint. Explicit axiom audits
cover 33 public theorems, including the 16 added in this slice, and use
only `propext`, `Classical.choice` and `Quot.sound`.

All new modules are imported by the root library. The whole-project lint
and generated-status integrity audit pass across 1,421 compiled project
modules and 30,301 declarations, including 26,563 theorems, with no project
axioms or placeholder-dependent declarations. The source scan covers all
1,564 Lean files. Documentation links, whitespace, README scope and
generated-artifact reproducibility are checked with the complete package.

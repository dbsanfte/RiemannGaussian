# Sharp derivative control in the actual zero-free chain

The subsequent [signed angular slice](zeta-signed-angular-zero-free.md) gives the
current stronger region. This page records the sharp-center improvement
and its original validation. The theorem at that stage was
[`ZetaLogLogZeroFree.exists_eventual_strip`](../RiemannGaussian/ZetaLogLogZeroFree.lean#L62):
for every fixed `0<A<1/(560*log(2))`, there is a finite `T(A)>=2` such
that every genuine nontrivial zeta zero `rho=beta+i*t` with
`abs(t)>=T(A)` satisfies

```text
A*log(log(abs(t)))/log(abs(t)) < beta
                            < 1-A*log(log(abs(t)))/log(abs(t)).
```

The threshold depends on the coefficient and is not numerically evaluated.
The coefficient limit is a sufficient value, not a claimed optimum.
The corresponding literal closed-right-edge nonvanishing, complete
bounded-height bands and actual squarefree arithmetic transport all use
this larger range. RH and the independent signed ordinary-prime bound
remain open.

## The avoidable analytic loss

Let `f` be holomorphic on the open disc of radius `R>0`, with `f(0)=0`
and `Re(f(z))<=M` there, for `M>0`. The exact transform

```text
w(z)=f(z)/(2*M-f(z))
```

is holomorphic, has `w(0)=0` and maps the disc into the closed unit disc.
Its denominator cannot vanish: that would give `Re(f(z))=2*M>M`.
Schwarz at the center gives `norm(w'(0))<=1/R`; the quotient derivative
is exactly `w'(0)=f'(0)/(2*M)`. Consequently

```text
norm(f'(0)) <= 2*M/R.
```

[`AnalyticDiscCaratheodory.norm_deriv_zero_le`](../RiemannGaussian/AnalyticDiscCaratheodory.lean)
proves this for every positive radius and allowance. It does not assume
a norm bound for `f` or a bound on its imaginary part. Applying Schwarz
before introducing an auxiliary-circle maximum preserves the complete
complex derivative and the classical constant two.

For a nonvanishing analytic function `g`, the existing exact normalized
logarithm satisfies `exp(L(z))*g(0)=g(z)` and `L'=g'/g`. If
`norm(g)<=exp(B)` and `-log(norm(g(0)))<=C`, then `Re(L)<=B+C`.
The new
[`norm_logDeriv_center_le_sharp`](../RiemannGaussian/AnalyticDiscLogarithm.lean)
therefore gives `norm(g'(0)/g(0))<=2*(B+C)/R` when `B+C>0`.
The earlier weaker bound remains available as a compatibility theorem.

This is a classical Carathéodory estimate, not a claim of novel mathematics.
The new result here is its verified use throughout this repository's
actual zeta exclusion chain.

## The full arithmetic propagation

Use the notation and joint schedule from the
[log-log proof](zeta-log-log-zero-free.md). Complete canonical removal on
an actual zero-free sphere `delta_k/4<r<3*delta_k/8` preserves the original
boundary norms and increases the center norm. The residual now satisfies

```text
norm(logDeriv(g,0)) <= 2*E_k/r <= 8*E_k/delta_k.
```

The exact complex pole-plus-correction identity remains available. Every
actual local zero contributes with its full multiplicity and a
nonnegative coupled real kernel. For a selected zero, `d=x+1-beta`, the
actual bound is

```text
Re(-zeta'(1+x+i*t)/zeta(1+x+i*t))
 <= 8*E_k(x,t)/delta_k - m_rho*(1/d-16*d/delta_k^2).
```

Only the analytic residual allowance has changed. The radial correction
and the selected multiplicity source keep their original values. The
actual three-height prime inequality now has

```text
B_k(x,t)=1344*log(22)+(32*E_k(x,t)+8*E_k(x,2*t))/delta_k.
```

With `L=log(abs(t)+2)`, `ell=log(L)`, `k=floor(ell/b)`, `b>log(2)`,
`u=C*ell/L` and `x=6*u`, the already proved complete correction estimates
give

```text
u*B_k(x,t) -> 40*C*b,
14*u*B_k(x,t)+6272*(u/delta_k)^2 -> 560*C*b.
```

An actual zero with `1-beta<=u` forces the latter cost to be at least
one. Choosing `log(2)<b<1/(560*C)` makes it eventually smaller than one.
The entire passage to ordinary logarithms and both strip edges is proved;
no radius, center, prime or multiplicity premise is left unproved.

The larger coefficient range reaches the actual quotient
`zeta(s)/zeta(2*s)` and every valid marked squarefree response through
[`ZetaSquarefreeLogLogRadius`](../RiemannGaussian/ZetaSquarefreeLogLogRadius.lean).
At `3/2+i*y`, its proved radius is
`1+A*log(log(H))/(2*log(H))`, `H=2*abs(y)+3`, above the coefficient's
threshold. The signed prime envelope is retained; larger radii do not
by themselves control that envelope for growing prime sets.

## What the stronger literature requires

The [published-region survey](zero-free-region-transport.md) records the
height restrictions and boundary conventions needed to combine the
available results. For research, the candidate set can be restricted by
their union. The compiled chain uses only regions with fully discharged
Lean proofs.

[Bellotti's published proof](https://www.researchgate.net/publication/378454423_Explicit_bounds_for_the_Riemann_zeta_function_and_a_new_zero-free_region)
supplies a zeta growth exponent proportional to `(1-sigma)^(3/2)`, using
uniform logarithmic exponential sums and Vinogradov mean-value estimates.
This is the substantive additional input for the stronger
Vinogradov--Korobov shape. Our present derivative recursion does not
establish it.

The following scale calculation is a guide for that formalization,
not an additional proved theorem here. Put `d=1-sigma` and `L=log(t)`.
A growth allowance of size `L*d^(3/2)+log(L)` on a radius comparable to
`d` leads to derivative cost `L*sqrt(d)+log(L)/d`. Balancing the terms at
`d` of order `(log(L)/L)^(2/3)` gives reciprocal cost of order
`L^(-2/3)*log(L)^(-1/3)`. This explains why a different growth estimate
improves the width's shape, while the present sharp derivative step
improves its coefficient.

Neither improvement alone supplies the missing signed ordinary-prime
lower bound at a hypothetical interior zero.

## Validation of the sharp-center slice

All 11 audited modules pass direct compilation with warnings treated as
errors. The focused arithmetic build passes 4,894 jobs and the full
library passes 10,263 jobs. Whole-project declaration lint and verbose
lint of the 11 modules pass. Explicit audits of all 60 public theorems
in this checked slice use only `propext`, `Classical.choice` and
`Quot.sound`; two public theorem names are new, and the downstream
region has the stronger conclusion.

The strict generated inventory contains 1,416 project modules and 26,536
project theorems, with no project-defined axioms or placeholder-dependent
declarations. It reports `rhImplied=false`. The source scan covers 1,559
Lean files, and 686 local documentation links pass. The README's Current
Direction was one paragraph of 428 characters at that checkpoint.

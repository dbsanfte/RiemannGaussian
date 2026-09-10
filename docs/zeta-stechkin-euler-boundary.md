# Exact Stechkin arithmetic at the Euler boundary

The terminal
`tendsto_zetaPhase_stechkin_primeWork_sub_pole_boundary` in
[ZetaStechkinBoundaryPhase.lean](../RiemannGaussian/ZetaStechkinBoundaryPhase.lean)
proves the Abel limit of the complete prime work after the entire pole
family is subtracted. The companion
`zetaPhase_stechkin_boundary_source_le` retains the exact signed
completion and full selected right-half source at the boundary.

This closes an analytic passage needed to examine sampling lines tending
to one. It does not prove the independent arithmetic bound required for
RH or claim mathematical novelty. The domination below now uses the
subsequently proved [Stechkin zero-free strip](zeta-stechkin-zero-free.md).

## Remove the pole before taking the limit

Write `Z1(s)` for the actual entire pole-removed zeta function: away from
one it equals `(s-1)*zeta(s)`, and `Z1(1)=1`. It is nonzero on the closed
Euler half-plane. The compiled complex identity
`logDeriv_riemannXi_eq_regular_add_poleRemoved` is

```
xi'(s)/xi(s) = R(s) + Z1'(s)/Z1(s),
R(s) = 1/s - log(pi)/2 + digamma(s/2)/2.
```

It includes `s=1`. On the larger domain `Re(s)>0` its explicit
nonvanishing condition on `Z1(s)` is required. The closed Euler
half-plane discharges that condition unconditionally.

Retain the algebraic Stechkin parameters from the
[preceding comparison](zeta-stechkin-phase-budget.md):

```
tau(sigma) = (1+sqrt(1+4*sigma^2))/2,
c(sigma) = sigma/sqrt(1+4*sigma^2).

F_sigma(t) = -Z1'(sigma+it)/Z1(sigma+it)
            + c(sigma)*Z1'(tau(sigma)+it)/Z1(tau(sigma)+it),
G_sigma(t) = R(sigma+it) - c(sigma)*R(tau(sigma)+it).
```

Both `F` and `G` are kept as complex functions in
[ZetaStechkinBoundary.lean](../RiemannGaussian/ZetaStechkinBoundary.lean).
The actual zero comparison `M_sigma(t)` obeys

```
Re F_sigma(t) + M_sigma(t) = Re G_sigma(t),  sigma >= 1.
```

Here `M` is the absolutely convergent sum of the genuine critical
reflection pairs, with their true multiplicities and fixed points
counted once. Each pair is nonnegative. Neither the zero background nor
the exact signed Gamma term has been replaced by a norm allowance in
this identity.

## Uniform domination is proved for the actual zeta function

[ZetaEulerPoissonBound.lean](../RiemannGaussian/ZetaEulerPoissonBound.lean)
uses the proved margin `1/(64*log(abs(t)+22))`. With
`L(t)=log(abs(t)+26)`, it proves

```
sum_rho P(sigma+it,rho) <= 325*L(t)
  for 1 <= sigma <= 3 and abs(t) >= 5.
```

Nearby zero atoms use the existing margin; far atoms use their exact
rational comparison with the line shifted by `1/L(t)`. This is a bound
on the complete actual mass, not a new exclusion margin.

[ZetaEulerBoundaryControl.lean](../RiemannGaussian/ZetaEulerBoundaryControl.lean)
then proves

```
abs(Re(Z1'/Z1)(sigma+it)) <= 326*L(t)
  for 1 <= sigma <= 3 and abs(t) >= 5.
```

Actual analyticity and nonvanishing on the compact remaining rectangle
give one positive constant for all heights on this closed strip.
Together with `1 <= tau(sigma) <= 3` for `1 <= sigma <= 2`, this bounds
`abs(Re F_sigma(t))` uniformly by a constant times `L(t)`.
The real completion comparison is bounded by `4*L(t)` on the same range.

These constants serve as dominators; no claim is made that they are sharp.

## Every admissible phase family

Let `a(n)>=0` be summable, let `omega(n)` be arbitrary real frequencies,
and assume `sum a(n)*log(1+abs(omega(n)))` is summable. The proved
inequality

```
L(omega*y) <= L(y) + log(1+abs(omega))
```

provides a summable dominator. Thus the real response, exact completion,
and complete zero mass are all summable over the family, including at
`sigma=1`. Frequencies may be zero, negative, infinitely numerous, or
accumulate at zero. The zero sum is formed first at each frequency;
no exchange of zero and frequency sums is assumed.

Write `W_sigma(a,omega,y)` for the complete prime work and `Q_sigma(t)`
for the exact Stechkin pole comparison. For `sigma>1`, the compiled
identity and limit are

```
W_sigma(a,omega,y) - sum_n a(n)*Q_sigma(omega(n)*y)
  = sum_n a(n)*Re F_sigma(omega(n)*y)
  --> sum_n a(n)*Re F_1(omega(n)*y),  sigma -> 1+.
```

The family and height are fixed during each limit. This is not a uniform
limit for families varying with the sampling line. The boundary
identity itself holds for every admissible family.

At frequency zero the original pole and prime work diverge separately.
The theorem subtracts their full exact contributions before taking the
limit. It does not interpret the totalized value of the original pole
formula at `sigma=1,t=0` as that limit. For frequencies accumulating at
zero, the entire pole family is retained in the subtraction as well.

## The remaining arithmetic inequality

For an actual right-half zero `rho=beta+i*gamma`, multiplicity `m`, and
an index `r` with `omega(r)=1`, the boundary source theorem gives

```
a(r)*m/(1-beta) + sum_n a(n)*Re F_1(omega(n)*gamma)
  <= sum_n a(n)*Re G_1(omega(n)*gamma).
```

The selected source is the full source from its distinct reflected pair.
An independent lower bound on the regularized arithmetic which makes
the left side strictly larger would exclude that hypothetical zero.
Such a bound has not been proved here.

The earlier positivity of complete prime work does not establish a sign
after a divergent pole is subtracted. Nor does the logarithmic dominator
supply the needed sharp one-sided bound. The new theorem makes the
boundary expression and its convergence available for an arithmetic
attack while keeping the exact signed completion accessible.

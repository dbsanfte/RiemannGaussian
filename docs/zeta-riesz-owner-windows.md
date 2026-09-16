# Larger independently controlled composite-owner ranges

The full original signed Riesz carrier has a larger independently controlled
component. Write each squarefree composite integer uniquely as `m = p a`,
where `p` is its largest prime. The estimates here delete complete fibres
with **composite** cofactor `a`; semiprime owners remain in the signed sum.

These are component bounds. **The joint bound for the remaining signed
carrier, a zero-free region from this path, and RH remain open.**

## Two concrete improvements

For every fixed complex polynomial filter `P`, the following bounds hold
at every sufficiently large order, uniformly over all real heights `t`.
Let `W_N(m)` be the original band weight, including its arithmetic
coefficient, complete factorial filter and complex phase.

```math
u^{N+1}\sum_{\substack{m\text{ in the original band}\\
a=m/P^+(m)\text{ composite}\\ \log a\le N/5}}
|W_N(m)|\le C(P,u)\,r_5^N,
\qquad 0<u<e^{-2/3},
\quad r_5=\frac32e^{-9403/23040}<1.
```

This includes every atom in the previous `exp(N/10)` owner range and
raises the logarithmic cutoff to `N/5`.

```math
u^{N+1}\sum_{\substack{m\text{ in the original band}\\
a=m/P^+(m)\text{ composite}\\ \log a\le N/10}}
|W_N(m)|\le C(P,u)\,r_{10}^N,
\qquad 0<u<e^{-16/25},
\quad r_{10}=\frac32e^{-10427/25600}<1.
```

The second estimate retains the old cutoff while expanding its explicit
source-radius range. Both use the finite constant
`C(P,u) = u * ZetaArithmeticLogWindow.tiltConstant P (2/3) (513/512)`.
The starting order is proved to exist but has not been numerically
evaluated. Moving heights are allowed because each estimate is uniform
in `t`. The sum is on the original band, with unique integer ownership;
no prime completion or smaller physical annulus is substituted.

The checked endpoints are
`ZetaRieszOwnerBounds.eventually_fifth_owner_mass_le` and
`ZetaRieszOwnerBounds.eventually_tenth_owner_mass_le`.

## The retained correlation

The physical length is exactly

```math
L_N=2\log(D_N+2),\qquad
D_N=\left\lfloor\frac{u^{-N}}{N+1}\right\rfloor.
```

Lean proves the eventual ceiling `L_N <= -2 log(u) N` for every
`0<u<1`. Once a composite owner is saturated (`log a <= L_N`), its
coefficient vanishes whenever `log p >= L_N`. A surviving product with
`log a <= delta N` therefore satisfies

```math
\log m\le(-2\log u+\delta)N.
```

The whole original divisor majorant pays this logarithmic window in one
sum. There is no additional growing cofactor-count factor. For any
`q>1/2` and `sigma>1`, the resulting geometric base is

```math
r(u,\delta,q,\sigma)
=\frac{u}{q}\exp\big((\sigma-3/2+q)(-2\log u+\delta)\big).
```

The explicit bounds above keep the correlation between `u` and `L_N`
until this rate is evaluated. All summability and filter costs are paid.

## A general source-dependent window

At the boundary `delta=0`, `sigma=1`, this expression is exactly the
previously audited scalar tilt rate. Its analytic optimizer is
`q = 1/(-2 log u)`. The strict margin away from `u=exp(-1/2)` allows
both a positive growth exponent and a summable majorant exponent.

`ZetaRieszOwnerMass.exists_growing_owner_mass_decay` proves that, for
every `1/2<u<1` except that single value, **some** `delta(u)>0` gives
decay of the full absolute owner mass, for every fixed filter and every
sequence of heights. It does not give the same fixed exponent throughout
the interval or prove that this cofactor exponent is optimal. The scalar
contact is a limitation of this estimate, not an exceptional zeta-zero
statement or a failure of every possible method. Earlier estimates remain
available there.

## What remains in the contradiction

The selected atoms form entire complete prime cells. Their aggregate
cell-norm mass vanishes, so all their signed contributions can be deleted
without using any additional cancellation. At a hypothetical right-half
zero, the remaining cells still satisfy

```math
u^{N+1}\sum_{K\text{ remaining}} B_{N,K}
\longrightarrow -m(\rho),\qquad u=\frac32-\Re\rho.
```

The full pole-jet filter and arbitrary multiplicity remain; no exposed,
simple or globally rightmost zero is assumed. Each source endpoint keeps
its stated radius hypothesis. Remaining cells have a prime cofactor
(semiprimes) or a composite cofactor with `log a > delta N`.

An independent cofinal normalized upper bound below `m(rho)`, or a real
lower bound above `-m(rho)`, would contradict this source. That joint
arithmetic bound is still missing. Keep the signs and correlations between
these remaining classes available.

The `owner-windows` supporting explorer endpoint records these theorems
and their audits. The default RH endpoint, proved zero-free region and
numerical certificate are unchanged. No exhaustive certificate computation
is added to ordinary CI, and no historical novelty claim is made here.

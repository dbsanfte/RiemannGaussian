# Source audit of the centered logarithmic convolution

The new convolution identity preserves the full source when its pair
subtraction is retained. The separate convolution can be small at a simple
zero. `SuzukiConvolutionSource.lean` proves this and a local error bound;
**it does not bound the Suzuki potential or exclude a zeta zero.**

## Genuine arithmetic response

For a fixed real center `r`, let

```text
c_r(n) = sum_(d*k=n) mu(d)*log(k)*(log(k)-r).
```

`LSeriesHasSum_moebius_log_mul_sub_center` proves absolute convergence
and the exact response on `Re s > 1`:

```text
sum_n c_r(n)/n^s = Q_r(s) = zeta''(s)/zeta(s) + r*zeta'(s)/zeta(s).
```

The complete pair coefficient has response `P(s)=(zeta'/zeta)(s)^2`.
Their difference is the centered prime coefficient's response:

```text
Q_r(s)-P(s) = (zeta'/zeta)'(s) + r*(zeta'/zeta)(s).
```

The equality with the second derivative quotient is used only at nonzero
analytic points. The local continuation across a zero is handled through
punctured neighborhoods, not by its totalized value at the zero.

## Exact remainder and uniform bound

The proof applies to any complex function analytic at a point `a` with
finite analytic order `m`. One analytic remainder `h` gives, throughout
a punctured neighborhood with `d=s-a`,

```text
ell(s)  = m/d + h(s),
ell'(s) = -m/d^2 + h'(s),          ell = f'/f.
```

Before taking norms, Lean proves that two analytic functions `A,D`,
independent of the center, satisfy `D(a)=m` and, simultaneously for all
complex centers `r`,

```text
d^2*(ell'(s)+ell(s)^2+r*ell(s)) - m*(m-1)
  = d*(A(s)+r*D(s)).
```

Consequently some `B>0` satisfies the local estimate

```text
norm(d^2*Q_r(s)-m*(m-1)) <= B*(1+norm(r))*norm(d)
```

at every sufficiently close punctured point, for every center at once.
`exists_zetaCenteredConvolution_uniform_bound` specializes this to actual
nontrivial zeta zeros without assuming simplicity or RH. The constant and
neighborhood may depend on the zero. This is an estimate as `s` approaches
that zero, not as a physical arithmetic cutoff tends to infinity.

## All convergent weights and moving centers

Suppose `w(s)->v` and `(s-rho)*r(s)->b` in the punctured neighborhood of a
nontrivial zero `rho`. Lean retains the full complex limits:

```text
(s-rho)^2*w(s)*Q_(r(s))(s)       -> v*(m*(m-1)+b*m),
(s-rho)^2*w(s)*(Q_(r(s))(s)-P(s)) -> v*m*(b-1).
```

These statements apply to every family satisfying the displayed limit
hypotheses. They do not assume a finite polynomial ansatz or select
numerical coefficients. They also do not assert uniformity for arbitrary
families whose weights fail to converge in this limit.

For a fixed center, `b=0`. When `m=1` the first limit is zero, even for
`v` nonzero. The second limit is then `-v`. More generally it is `-v*m`,
nonzero at every actual nontrivial zero when `v` is nonzero.
`not_tendsto_zetaCenteredConvolution_sub_pair_zero` proves this
nonvanishing for every center with scaled limit zero.

A center growing at reciprocal distance can change the source. For
example the complete signed source is zero when `b=1`; that choice erases
the source rather than giving a contradiction. The general formula keeps
this contribution explicit, so fixed-center estimates cannot silently be
applied to such a moving family.

## Implication for the open arithmetic task

Decay of the separate convolution at the quadratic local scale is
compatible with a simple zero and supplies no contradiction. The exact
[finite arithmetic identity](suzuki-logarithmic-convolution.md) still
retains all signs, products, and cutoffs. Its original centered prime
moment, complete pair subtraction, and nonlinear block entropy must
remain coupled in any estimate of the Suzuki potential.

The [global one-sided subpolynomial bound on balanced cells](suzuki-balanced-subpolynomial.md)
is still open. The local source estimate does not improve a zero-free
region, provide a cutoff-decay rate, or prove a previously open RH
direction. No mathematical novelty claim is made for the local pole
calculation.

Principal declarations:

- `LSeriesHasSum_vonMangoldt_center`
- `LSeriesHasSum_moebius_log_mul_sub_center`
- `AnalyticAt.exists_logDeriv_deriv_common_remainder`
- `AnalyticAt.exists_logarithmicConvolution_uniform_remainder`
- `AnalyticAt.exists_logarithmicConvolution_uniform_bound`
- `AnalyticAt.tendsto_logarithmicConvolution_source`
- `AnalyticAt.tendsto_logarithmicPrime_source`
- `exists_zetaCenteredConvolution_uniform_bound`
- `tendsto_zetaCenteredConvolution_source`
- `tendsto_zetaCenteredConvolution_sub_pair_source`
- `tendsto_zetaCenteredConvolution_simple`
- `not_tendsto_zetaCenteredConvolution_sub_pair_zero`

The module is imported from the root library. Direct warnings-as-errors
elaboration, focused and full builds, whole-project and root declaration
lint, twelve terminal axiom audits, the placeholder scan, generated-status
freshness, and whitespace checks passed locally. The axiom audits use only
`propext`, `Classical.choice`, and `Quot.sound`. Work remains uncommitted;
no remote CI run was started for this slice.

# Five signed prime phases widen the proved zero-free region

`ZetaSignedFiveHeight.lean` proves an unconditional bound for the literal
nontrivial zeta zeros. If `rho = beta + i*gamma` and `abs gamma >= 1`, then

```text
1 / (28000 * log(abs gamma + 22)) < beta
beta < 1 - 1 / (28000 * log(abs gamma + 22)).
```

The terminal theorem is
`nontrivialZetaZero_mem_fiveHeight_reciprocal_log_strip`.
`riemannZeta_ne_zero_of_fiveHeight_margin` also states nonvanishing directly
for the actual `riemannZeta` on the corresponding closed right-edge region.

The previous uniform reciprocal-logarithm result had denominator `56458`.
`two_mul_quadratic_uniform_margin_lt_fiveHeight` proves that the new margin
is strictly more than twice that uniform margin. This comparison concerns
those two uniform formulas, not every multiplicity-sensitive bound in the
repository. This is a stronger formalized region in this repository, with
no claim of a new result in analytic number theory.

## Arithmetic inequality

The exact identity

```text
35 + 56*cos(t) + 28*cos(2*t) + 8*cos(3*t) + cos(4*t)
  = 8*(1+cos(t))^4 >= 0
```

keeps five prime phases together. The coefficients are fixed mathematical
coefficients from a fourth power, with no numerical fit.

For `a>1`, each von Mangoldt amplitude is nonnegative and the Dirichlet
series converges absolutely. Summing the identity therefore proves
`neg_logDeriv_riemannZeta_five_height_nonneg` for the actual logarithmic
derivative at heights `0, y, 2*y, 3*y, 4*y`. No continuation of that prime
series into the critical strip is assumed.

## Complete local pole sums

At the evaluation point `1+x+i*y`, write `S_y(x)` for the existing complete
local zero pole sum, with every analytic multiplicity. For `0<x<=1/4`
and `y!=0`, `five_height_localZetaPoleSum_re_le` proves

```text
35*Re S_0(x) + 56*Re S_y(x) + 28*Re S_(2y)(x)
  + 8*Re S_(3y)(x) + Re S_(4y)(x)
  <= 35/x + 68096*log(abs y+22) + 9209*x/(144*y^2).
```

All five sums remain in this interface. The final single-zero estimate
uses their previously proved nonnegative real parts and retains the full
multiplicity of the selected zero. The analytic remainder bound and the
pole at one are included explicitly.

The height comparison also retains the shared ordinate:

```text
log(abs(k*y)+22) <= log(abs y+22) + log k   (k>=1).
```

## Source versus allowance

Let `d=1-beta`, `L=log(abs gamma+22)`, and let `m` be the actual analytic
multiplicity. For `beta>=15/16`, evaluation at `x=4*d` gives the compiled
inequality `multiplicity_le_fiveHeight_signed_zero_gap`:

```text
2016*m - 1575 <= 12257280*L*d + 46045*d^2/gamma^2.
```

An actual zero has `m>=1`, so the left side is at least `441`. If also
`abs gamma>=1` and `d<=1/(28000*L)`, the complete right side is strictly
smaller than `441`. Lean checks this contradiction. Zeros outside the
local neighborhood already satisfy the wider margin, and completion
reflection proves the identical left-edge bound.

## Scope and remaining goal

This slice excludes a larger region near the two edges of the critical
strip. It does not force `beta=1/2`, strengthen the Suzuki mass–moment
potential's global floor, or close the independent signed inequality for
every hypothetical right-half zero. The trigonometric-polynomial method is
classical. The full RH goal remains active.

Direct Lean elaboration and the focused build passed with warnings treated
as errors. The full root/default build passed (9,756 jobs), as did the
whole-project declaration lint. The focused audit checked 13 declarations
and 7 generated declarations with 14 linters; all 11 public theorems use
only `propext`, `Classical.choice`, and `Quot.sound`. Source and whitespace
checks passed. Validation is local; commits and generated status updates
remain held.

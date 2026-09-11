# A wider zero-free region from the signed pole subtraction

The Lean development proves that every nontrivial zero
`rho = beta + i*t` satisfies

```text
Delta(t) < beta < 1 - Delta(t),
Delta(t) = 792 / (7625*log(abs(t)+2) - 2000).
```

The denominator is positive at every real ordinate. The literal Riemann
zeta function is nonzero on the closed right-edge region
`Re(s) >= 1 - Delta(Im(s))`, away from its pole at one.

The terminal theorems are `nontrivialZetaZero_mem_signedPole_strip` and
`riemannZeta_ne_zero_of_signedPole_margin` in
[ZetaSignedPoleZeroFree.lean](../RiemannGaussian/ZetaSignedPoleZeroFree.lean).
Every arithmetic and analytic hypothesis is discharged. This is a partial
edge exclusion within the classical phase/Stechkin framework. It does not
prove RH, establish mathematical priority, or claim a best published region.

## The sign that was lost

Write

```text
tau = (1 + sqrt(1+4*sigma^2))/2,
c = sigma/(2*tau-1),
x = sigma-1, b = tau-1.
```

The exact pole term in the existing signed identity is

```text
P(sigma,t) = x/(x^2+t^2) - c*b/(b^2+t^2).
```

The preceding shifted source estimate discarded the second term and then
bounded the first by `x/t^2`. After summing frequencies and normalizing by
`d=1-beta`, this introduced a positive quadratic pole allowance.

`zetaStechkinPoleBudget_neg` instead proves

```text
1 <= sigma <= 4/3, 3 <= t^2  ==>  P(sigma,t) < 0.
```

The common numerator is

```text
x*b^2 - c*b*x^2 - (c*b-x)*t^2.
```

The auxiliary quadratic identity and the exact comparison coefficient give
`b^2 <= 7/8`, `c <= 8/17`, and `c*b-x >= 5/51`.
Thus the first term is at most `7/24`, the last subtraction is at least
`5/17`, and the middle subtraction has favorable sign. The full numerator
is strictly negative. Both denominators have proved positive sign.

## Complete phase families

`zetaPhase_stechkinPole_le_constant` transports that pointwise sign through
the genuine convergent countable sum. It applies to nonnegative summable
coefficients and arbitrary real frequencies with one designated constant
mode, provided every other sampled ordinate has square at least three.

For integer frequencies, every nonconstant mode satisfies that separation
at any actual nontrivial zero: the independent eta theorem already proves
`t^2 > 3`. Consequently `phase_stechkinPole_le_constant` gives

```text
sum_n a_n P(sigma,n*t)
  <= a_0/(sigma-1) - a_0*c/(tau-1).
```

There is no restriction to finitely many coefficients or a chosen frequency
count. The sharper constant-mode subtraction also remains explicit.

`phase_shifted_source_add_primeWork_add_signedPoleReserve_le` carries the
result into the source inequality for every admissible integer-frequency
family. It retains the selected analytic multiplicity, complete signed
prime work, negative completion constant, and constant-pole reserve
together. The required sampling condition is `kappa*(1-beta) <= 1/3`.
The previous richer signed identity remains available upstream.

## Actual zero exclusion

The existing exact phase optimizer is used with its coefficients unchanged
and the existing shift `kappa=13/4`. Its new necessary zero budget, for
`beta >= 35/39`, is

```text
11/625 + d*W(sigma,t) + d*a_0*c/(tau-1)
  <= d*(1-c)*(481*d/1600 + 61*log(sigma+abs(t))/200 - 1/8),

d=1-beta, sigma=1+13*d/4.
```

`W` is the complete convergent Stechkin prime-power work with the original
nonnegative phase kernel. Its nonnegativity is proved independently;
the constant-pole reserve is also nonnegative. The uniform exclusion uses
only these signs, while the stronger budget keeps both full expressions.

The actual eta height bound gives `L=log(abs(t)+2)>13/10`. Assuming
`d <= Delta(t)` implies `d <= 4/39`, so the signed pole theorem applies.
`zetaSignedPole_allowance_le` then proves

```text
d*(1-c)*(481*d/1600 + 61*L/200 - 1/8)
  <= 11/625 - (221/28080)*d.
```

Since `d>0`, this contradicts the full source budget. Critical reflection
supplies the left-edge result at the same ordinate.

`completionReserve_margin_scaled_lt_signedPole` proves at every real height

```text
(1584/1525) * (1/(10*log(abs(t)+2))) < Delta(t).
```

This compares the new region with the preceding strongest project width.
It is a comparison of exclusion widths, not a count of additional zeros.

## Remaining obligation

The new bound removes an unnecessary positive pole error in the edge
argument. It does not bound the surviving oscillatory squarefree sum in the
interior strip. The independent cofinal signed upper bound below the unit
source is still open, including after the proved larger prime and
cofactor cutoff.

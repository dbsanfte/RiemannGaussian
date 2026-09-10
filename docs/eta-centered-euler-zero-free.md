# Centered Euler eta expansion and zero exclusion

The actual eta function now has a checked complex expansion with an
explicit remainder on the entire positive half-plane. Keeping its first
Euler correction before taking a norm proves a polynomial zero-free
region. Functional-equation reflection then excludes every nontrivial
zeta zero with squared ordinate at most three.

As a result, the earlier reciprocal-logarithm edge strip holds for every
nontrivial zero, without a height restriction. These are partial zero
exclusions. They do not establish RH, a new best classical zero-free
region, or a novel theorem in the mathematical literature.

## The signed expansion

Let `sigma=Re(s)>0`, `X=2N+1`, and let `eta_N(s)` be the existing paired
eta partial sum. For each real `x>0`, retain the complex block

```text
K(s,x) = integral_x^(x+1) (u-x-1/2) u^(-s-2) du
         - integral_(x+1)^(x+2) (u-x-3/2) u^(-s-2) du.
```

Integration by parts gives the exact identity

```text
x^(-s) - 2(x+1)^(-s) + (x+2)^(-s)
  = (s/2) (x^(-s-1) - (x+2)^(-s-1)) + s(s+1) K(s,x).
```

Summing the derivative term before estimating yields

```text
eta(s) - eta_N(s)
  = X^(-s)/2 + (s/4) X^(-s-1)
    + (s(s+1)/2) sum_(n>=N) K(s,2n+1).
```

This is a complex identity, including both endpoint phases and both
orientations of the centered triangular kernel. The series is proved
absolutely convergent. Its two weights have absolute value at most
`1/2`, so integration of the real power gives

```text
sum_(n>=N) |K(s,2n+1)| <= X^(-sigma-1)/(2(sigma+1)),
|eta(s)-eta_N(s)-X^(-s)/2-(s/4)X^(-s-1)|
  <= |s| |s+1| X^(-sigma-1)/(4(sigma+1)).
```

These formulas hold at every cutoff, including zero. No zero equation,
coefficient family, numerical computation, or eventual-cutoff assumption
is used. The signed identity remains available upstream of the norm bound.

The declarations in
[EtaCenteredEulerExpansion.lean](../RiemannGaussian/EtaCenteredEulerExpansion.lean)
include:

- `cpow_secondDiff_eq_centered_euler`;
- `pairedEtaCorePartialSum_eq_centered_euler`;
- `summable_pairedEtaCenteredEulerBlock`;
- `pairedEtaCore_eq_centered_euler`;
- `norm_pairedEtaCore_sub_centered_euler_le`;
- `pairedEtaCore_tail_eq_centered_euler`;
- `norm_pairedEtaCore_tail_sub_centered_euler_le`.

## An independent source-beating inequality

At cutoff zero the center is `1/2+s/4`, and the error is at most
`|s| |s+1|/(4(sigma+1))`. Consequently eta is nonzero wherever

```text
t^4 + sigma^2 t^2 < 4(sigma+1)^3,    t=Im(s).
```

This follows from an exact square identity:

```text
[4(sigma+1)]^2 |1/2+s/4|^2 - |s|^2 |s+1|^2
  = 4(sigma+1)^3 - sigma^2 t^2 - t^4.
```

The source exceeds the entire independently bounded remainder in this
region. For `sigma>=1/2` and `t^2<=3`, the difference is strictly positive.
An actual zeta zero has eta value zero; critical reflection covers its
left-half partner with the same ordinate. Therefore

```text
every nontrivial zero rho satisfies Im(rho)^2 > 3.
```

Literal zeta is nonzero throughout `Re(s)>0`, `Im(s)^2<=3`, `s!=1`.
Combining this with the [half-logarithm edge theorem](zeta-half-log-zero-free.md)
gives, for every genuine nontrivial zero `beta+i*gamma`,

```text
1/(24*log(abs(gamma)+22)) < beta < 1-1/(24*log(abs(gamma)+22)).
```

The corresponding terminal declarations in
[ZetaCenteredEulerZeroFree.lean](../RiemannGaussian/ZetaCenteredEulerZeroFree.lean)
are `pairedEtaCore_ne_zero_of_centered_euler`,
`nontrivialZetaZero_centered_euler_constraint`,
`nontrivialZetaZero_im_sq_gt_three`,
`riemannZeta_ne_zero_of_im_sq_le_three`,
`nontrivialZetaZero_mem_half_log_strip_all_heights`, and
`riemannZeta_ne_zero_of_half_log_margin_all_heights`.

## Remaining global obstruction

For bounded real part and large ordinate, the error in this estimate
grows quadratically while the center grows linearly. This bound therefore
does not exclude higher interior zeros. Its contribution is a proved
low-height contradiction and a general signed expansion that can be used
before further cancellation arguments. The source-beating arithmetic
inequality needed throughout the unbounded right half-strip remains open.

The [exact adjacent-ratio expansion](eta-uniform-tail-bound.md) now improves
tail control at moving heights. For `X>=|s|`, its normalized error from the
Euler half endpoint is at most `3|s|/(2X)`. The full complex ratio and signed
remainder are retained; the independent arithmetic estimate is still open.

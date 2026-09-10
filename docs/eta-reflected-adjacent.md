# Reflected eta phases at every cutoff

Lean proves a uniform bound on the phase of the actual reflected adjacent
eta product. It also extends the exact adjacent summation identity to every
cutoff and transports it into the completed zeroth moments. The independent
signed arithmetic bound required for RH remains open.

## The full neighboring phase

For `x>0`, set

```text
delta(x) = log((x+1)/x),
q(s,x) = exp(-s*delta(x)),
g(s,x) = 1/(1+q(s,x)),
H(s,x) = g(s,x)*x^(-s).
```

For `Re(s)>0`, Lean proves `|q(s,x)|<1`, hence `1+q(s,x)` is nonzero.
There is no condition `x>=|s|`. These are the existing ratio, inverse,
and boundary definitions, extended to their full nonsingular domain.

Write `s'=1-conj(s)` and assume `0<sigma=Re(s)<1`. Reflection gives

```text
q(s,x)*conj(q(s',x)) = exp(-delta(x)),
g(s,x)+conj(g(s',x))-1 = (1-exp(-delta(x)))*P(s,x),
P(s,x) = g(s,x)*conj(g(s',x)).
```

The first identity cancels the shared oscillating phase before any norm.
The mixed inverse still retains the difference between the two radial
amplitudes.

## Uniform sector and all nonnegative families

At every height and positive cutoff, the compiled theorems prove

```text
Re(P)>0,
4 sigma(1-sigma) |P|^2 <= Re(P)^2,
2 sqrt(sigma(1-sigma)) |P| <= Re(P),
4 sigma(1-sigma) Im(P)^2 <= (2sigma-1)^2 Re(P)^2.
```

The constant depends only on the horizontal coordinate. At `sigma=1/2`
the odd channel vanishes. Away from that line it is controlled relative
to the retained positive real channel. Individual neighboring rotations
may be large; this statement does not assume the safe tail range.

For every finite family `w_i>=0`, `x_i>0`,

```text
2 sqrt(sigma(1-sigma)) sum_i w_i |P(s,x_i)|
  <= Re(sum_i w_i P(s,x_i)).
```

The same theorem holds for arbitrary index types and infinite families
when `sum_i w_i |P(s,x_i)|` is finite. Summability of the full complex sum
is proved from that hypothesis before commuting its real part and sum.
No particular weight family or coefficient search is used.
Both reflected channels in each summand use the same `x_i`. Control of
cross terms between different cutoffs remains outside this estimate.

The proof keeps the exact trigonometric denominator. Its radial input is
the proved inequality, for `0<=sigma<=1` and `t>=0`,

```text
|exp(-(1-sigma)t)-exp(-sigma*t)|
  <= |2sigma-1|*(1-exp(-t)).
```

This follows from convexity of `sinh` on the positive half-line. A
sum-of-squares identity then bounds the imaginary component of the
shared-phase denominator, and inversion preserves the sector inequality.

All these declarations are in
[EtaReflectedAdjacent.lean](../RiemannGaussian/EtaReflectedAdjacent.lean):
`pairedEtaAdjacentRatio_mul_conj_reflected`,
`pairedEtaAdjacentInverse_reflected_sum`,
`eta_complementary_exp_contrast_le`,
`pairedEtaReflectedAdjacentProduct_sector`,
`pairedEtaReflectedAdjacentProduct_norm_le_re`, and
`pairedEtaReflectedAdjacentProduct_im_sq_le`.

## Actual eta sums and completed current

Retain the existing signed variation

```text
R(s,x) = (g(s,x)-g(s,x+1))*(x+1)^(-s)
       + (g(s,x+2)-g(s,x+1))*(x+2)^(-s).
```

For every `Re(s)>0`, every natural cutoff `N`, and `X=2N+1`,

```text
eta(s)-eta_N(s) = H(s,X)+sum_(n>=N) R(s,2n+1).
```

The signed remainder series is absolutely convergent. Finite interval
identities retain both endpoint terms before passing to the infinite sum.
The earlier quantitative tail estimates still require `X>=|s|`; extending
the exact identity does not remove that restriction from those estimates.

For the actual boundary product,

```text
H(s,x)*conj(H(s',x)) = x^(-1)*P(s,x).
```

Thus it inherits the same sector bound. The theorem is also instantiated
at every actual nontrivial zeta zero and its repository reflection partner.

Let `F` be the existing xi completion factor and `M_N(rho)` the actual
completed zeroth moment. At each actual nontrivial zero,

```text
M_N(rho) = -F(rho)*(H(rho,X)+sum_(n>=N) R(rho,2n+1)).
```

The existing signed zeroth pair is exactly

```text
|F(rho')*(H(rho',X)+R_tail(rho',N))|^2
  - |F(rho)*(H(rho,X)+R_tail(rho,N))|^2.
```

Lean retains this as the full complex `etaSignedCompletedPair`, including
both completion channels. The linear-in-height safe-tail estimate also
reaches the completed moment:

```text
|M_N(rho)+F(rho)*H(rho,X)|
  <= |F(rho)| |rho| X^(-Re(rho)) delta(X),   X>=|rho|.
```

These results are in
[EtaReflectedAdjacentSums.lean](../RiemannGaussian/EtaReflectedAdjacentSums.lean),
especially `pairedEtaCore_tail_eq_adjacent_of_re_pos`,
`tsum_pairedEtaReflectedAdjacentProduct_norm_le_re`,
`pairedEtaFiniteCompletedMoment_zero_eq_adjacent`,
`pairedEtaFiniteCompletedMomentPair_zero_eq_adjacent`, and
`norm_pairedEtaFiniteCompletedMoment_zero_add_adjacent_le`.

The mixed-product estimate is not an upper bound for this difference of
completed energies. Nor does it bound the signed variation terms in the
finite range where `X<|rho|`. Those terms and their interaction with the
completion factors remain in the exact identity. Controlling the actual
signed current strongly enough to beat its forced source is still the
global arithmetic obstruction; no additional zero exclusion follows here.

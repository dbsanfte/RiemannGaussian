# Global xi expansion and actual carrier bounds

The global logarithmic-derivative expansion is now constructed from the
repository's canonical xi decomposition and unconditional growth bounds.
It supplies an independent signed estimate for the actual Suzuki carriers
outside the known zero strip, and an explicit vanishing bound for both
outer horizontal sides of every mixed carrier Gram integral. This does
not exclude any additional zeta zeros or establish the global arithmetic
inequality required for RH.

## Constructing the expansion

Let `R_n` be the existing zero-free canonical radii, `g_n` the actual
zero-free residual, and `L_n` its normalized analytic logarithm. The
existing global xi bound is `|xi(z)| <= exp(A*(|z|+1)^(3/2))` for a
proved constant `A >= 1`. Two Cauchy estimates give

```text
|(logDeriv g_n)'(z)| <= 64*A*(R_n+1)^(3/2)/R_n^2
                                      when |z| <= R_n/8.
```

The convex mean value estimate therefore proves

```text
|logDeriv g_n(s) - logDeriv g_n(w)|
  <= 64*A*(R_n+1)^(3/2)*|s-w|/R_n^2 -> 0
```

for arbitrary fixed complex `s,w`. Individual residual logarithmic
derivatives are not asserted to vanish. The subtraction is what removes
the possible additive constant. The terminal theorem is
[`tendsto_logDeriv_riemannXiCanonicalResidual_sub`](../RiemannGaussian/RiemannXiCanonicalLogVariation.lean).

Canonical factors also contain a mirror term

```text
J_(R,i)(z) = conj(i)/(R^2-conj(i)*z).
```

Its exact signed difference has numerator `conj(i)^2*(s-w)`. For
`|i| <= R` and `|s|,|w| <= R/2`, its norm is at most `4*|s-w|/R^2`.
The complete multiplicity count is at most
`A*(2*R+1)^(3/2)/log(2)`. Consequently the sum of all mirror differences
also tends to zero. Both this limit and the exact finite decomposition
are proved in [RiemannXiCanonicalCauchy.lean](../RiemannGaussian/RiemannXiCanonicalCauchy.lean).

The finite divisor is then reindexed as genuine nontrivial zeta zeros,
with no simplicity assumption. Absolute summability follows from the
proved multiplicity-weighted inverse-square zero sum: sufficiently far
from the two fixed evaluation points,

```text
|1/(s-rho) - 1/(w-rho)| <= 8*|s-w|/(1+|rho|^2).
```

[`hasSum_zetaLogDerivDifference`](../RiemannGaussian/RiemannXiGlobalLogDerivative.lean)
proves the complete identity

```text
xi'/xi(s) - xi'/xi(w)
  = sum_rho m_rho * (1/(s-rho) - 1/(w-rho))
```

whenever both xi values are nonzero. The sum is absolutely convergent,
so this is not a merely formal or conditionally ordered expansion.

## Reflection retains the signed Poisson formula

Taking `w=1-s` and using the xi functional equation yields

```text
2*xi'/xi(s) = sum_rho m_rho * (1/(s-rho) - 1/(1-s-rho)).

2*Re(xi'/xi(s)) = sum_rho m_rho *
  ((Re(s)-Re(rho))/|s-rho|^2
   +(Re(s)+Re(rho)-1)/|1-s-rho|^2).
```

Both signed numerators and both denominators are retained, along with
every analytic multiplicity. The compiled entry points are
`hasSum_zetaLogDeriv_reflection` and
`two_mul_re_logDeriv_riemannXi_eq_reflected_zero_sum`.
Because every genuine zero has `0 < Re(rho) < 1`, the real part is
nonnegative for `Re(s) >= 1` and nonpositive for `Re(s) <= 0`.

## Actual carrier estimates

The repository's coordinates are

```text
s = 1/2 + i*z,       alpha_rho = -i*(rho-1/2),
A(z) = xi(1/2+i*z),  q(z) = A'(z)/A(z).
```

Thus `Im(z) >= 1/2` corresponds to `Re(s) <= 0`. The exact Jacobian
gives `Im(q) <= 0` in that closed upper safe half-plane.
For every `eta >= 0`, the factorization

```text
A+i*eta*A' = A*(1+i*eta*q)
```

has `Re(1+i*eta*q) >= 1`, proving `|A+i*eta*A'| >= |A| > 0`.
This discharges nonvanishing for the actual entire denominator, rather
than assuming it when taking the quotient.

At `eta=1`, the literal carrier is `C=i/(1+i*q)`. Lean retains the exact
phase-energy defect

```text
Im(C)-|C|^2 = -Im(q)/|1+i*q|^2.
```

Consequently `|C|^2 <= Im(C)` and `|C| <= 1` on `Im(z) >= 1/2`.
The reflected carrier `C_sharp(z)=conj(C(conj(z)))` satisfies
`|C_sharp|^2 <= -Im(C_sharp)` and `|C_sharp| <= 1` on
`Im(z) <= -1/2`. The upper carrier is analytic at every point of its
closed safe half-plane. These are theorems in
[SuzukiCarrierSafeHalfPlane.lean](../RiemannGaussian/SuzukiCarrierSafeHalfPlane.lean).

## Vanishing outer sides, with mixed indices retained

For any genuine pair, define the left-to-right upper side

```text
U_(rho,sigma)(T) = integral_(-T)^T
  C(x+i*T)/[(x+i*T-conj(alpha_rho))*(x+i*T-alpha_sigma)] dx.
```

For `T >= 1` both distances are at least `T/2`, uniformly in `x` and
both nodes. The integrand is continuous and bounded by `4/T^2`.
Therefore

```text
|U_(rho,sigma)(T)| <= 8/T -> 0.
```

The reflected left-to-right lower side obeys exactly
`L_(rho,sigma)(T)=conj(U_(sigma,rho)(T))`; both indices must be exchanged.
It is also genuinely integrable, bounded by `8/T`, and tends to zero.
The entry points are `norm_suzukiXiCarrierUpperHorizontal_le`,
`tendsto_suzukiXiCarrierUpperHorizontal`,
`suzukiXiCarrierLowerHorizontal_eq_conj_upper`, and
`tendsto_suzukiXiCarrierLowerHorizontal` in
[SuzukiCarrierSafeContour.lean](../RiemannGaussian/SuzukiCarrierSafeContour.lean).
Both definitions use left-to-right parametrization; an oriented closed
rectangle must apply the appropriate sign to its top side.

## Remaining obligation

When closing the upper `C` channel, possible carrier poles remain in
`0 < Im(z) < 1/2`; the lower sharp channel has the reflected obstruction.
Their residues, the remaining vertical sides, and the already explicit
real-node subtraction poles still need a complete signed treatment.
No full-plane exclusion of denominator zeros is asserted. The bounds on
individual mixed entries do not by themselves justify an infinite
coefficient sum or a bound uniform in time.

The next useful theorem must carry those remaining terms into the actual
arithmetic-versus-screw comparison, then supply the independent signed
bound needed by the subexponential compensator or balanced-cutoff
criterion. Those arithmetic premises remain open. This slice is local
Lean work; the user has asked to hold commits and pushes.

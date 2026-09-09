# Xi-node cancellation in the complete Suzuki Gram

[SuzukiCarrierLocalCancellation.lean](../RiemannGaussian/SuzukiCarrierLocalCancellation.lean)
closes the local divisor step needed to analyze the
[signed carrier integral](suzuki-carrier-phase.md). It proves the exact
polar coefficients of both channels, retains their reflected-node pairing,
and proves cancellation on genuine small-circle integrals. It supplies no
independent global arithmetic bound or new zero exclusion.

## Local models with analytic remainders

Let `A` be spectral xi, `alpha` any genuine xi zero, and `m` its positive
analytic multiplicity. The existing logarithmic derivative theorem gives

```text
A'(z)/A(z) = m/(z-alpha) + h(z),   h analytic near alpha.
```

For every nonzero complex parameter `b`,
`exists_suzukiXiCayley_local_model` proves that the denominator is nonzero
on a punctured neighborhood and that

```text
b*A(z)/(A(z)+b*A'(z)) = (z-alpha)*q_b(z),
q_b(z) = b/[b*m + (z-alpha)*(1+b*h(z))],
q_b(alpha) = 1/m.
```

Thus the common leading coefficient does not depend on the Cayley
parameter. This is a local identity for all nonzero parameters, not a
search for a preferred parameter or a uniform global bound.

Take `b=i` and `b=-i`. The two corresponding literal carriers are `C` and
`C_sharp(z)=conj(C(conj(z)))`. Their analytic local factors `q,r` satisfy

```text
C(z)       = (z-alpha)*q(z),    q(alpha)=1/m,
C_sharp(z) = (z-alpha)*r(z),    r(alpha)=1/m.
```

`exists_suzukiXiCarrier_pair_local_model` proves these simultaneously,
including nonvanishing of both denominators away from the center. All
statements retain the literal totalized definitions via punctured-local
equalities; they do not change values assigned at the center.

`exists_suzukiXiCarrier_diagonal_polar_models` then proves

```text
C(z)/(z-alpha)^2       = 1/[m*(z-alpha)] + p(z),
C_sharp(z)/(z-alpha)^2 = 1/[m*(z-alpha)] + q_1(z),
```

where both remainders are analytic. Divided differences retain their full
values rather than replacing them by a norm estimate.

The signed identity also extends off the real axis, wherever both carrier
denominators are nonzero:

```text
(C-C_sharp)/(2*i) = C*C_sharp.
```

Consequently the signed diagonal quotient has an analytic regularization
with exact central value `1/m^2`.
`exists_suzukiXiCarrier_signed_diagonal_regularization` and
`tendsto_suzukiXiCarrier_signed_diagonal` prove this for every genuine xi
zero, including multiple and nonreal zeros.

## Full mixed entries and reflected pairing

For genuine nodes `alpha_rho, alpha_sigma`, put

```text
D_(rho,sigma)(z) = (z-conj(alpha_rho))*(z-alpha_sigma).
```

At any genuine node `alpha_tau`, define

```text
L_(rho,sigma,tau) =
  1/m_tau   if conj(alpha_rho)=alpha_tau and alpha_sigma=alpha_tau,
  0         otherwise.
```

`exists_suzukiXiCarrier_mixed_polar_models` proves that the complete
simple-pole coefficient of both `C/D` and `C_sharp/D` is precisely `L`.
Both full analytic remainders are retained. A real node contributes to
the matching diagonal; at a nonreal node the matching condition is the
reflected pairing. This is the orientation relevant to the Weil form.
It has not been replaced by an ordinary diagonal or an absolute value.

Define the coupled continuation

```text
K_(rho,sigma)(z) = (C(z)-C_sharp(z))/(2*i*D_(rho,sigma)(z)).
```

Every xi-node singularity of this function is removable, by
`exists_suzukiXiCarrierGramContinuation_regularization`. Its real-axis
restriction is genuinely integrable and its integral equals the existing
carrier Gram kernel, by
`integrable_suzukiXiCarrierGramContinuation_ofReal` and
`suzukiXiBoundaryCarrierGramKernel_eq_continuation_integral`.

## Exact puncture integrals

The local analytic models justify actual circle integrability and Cauchy's
theorem, including the omitted center. For every sufficiently small
positive radius,

```text
integral_circle C/D dz       = 2*pi*i*L,
integral_circle C_sharp/D dz = 2*pi*i*L,
integral_circle K dz         = 0.
```

These are exact eventual equalities, not numerical approximations or
uncontrolled limiting statements. The compiled entry points are
`eventually_suzukiXiCarrier_mixed_circle_residues` and
`eventually_suzukiXiCarrierGram_circle_eq_zero`. The radius can depend on
the chosen nodes. These full-circle results do not silently assert a
principal-value formula on the real axis or a half-circle contribution.

## Remaining global estimate

`analyticAt_suzukiXiCarrierGramContinuation` proves analyticity away from
the named denominators. Together with the xi-node regularizations, this
locates the remaining possible genuine poles at zeros of `E=A+i*A'` or
`E_sharp=A-i*A'` outside the xi divisor. Their contributions have not been
estimated or shown to vanish.

The two separated residues are kept even though they cancel in the
combined small-circle integral. They would enter a calculation that
closes the channels on different sides of the axis. The subsequent
[boundary split](suzuki-carrier-boundary-split.md) now proves the genuine
real-node principal values and an integrable split for every mixed entry.
It retains the auxiliary poles introduced by its common subtraction.
Oriented contour boundaries, any indentation formula, and all additional
carrier poles still need control. A full-plane local cancellation does
not supply those global statements.

The next proof must use the actual arithmetic signal to control the
resulting signed discrepancy uniformly with time, strongly enough for
the existing subexponential compensator, or prove the
[balanced-cutoff arithmetic bound](suzuki-balanced-subpolynomial.md)
directly. Removing an auxiliary integrand's local singularity does not
remove a zero of zeta. The independent bound remains open.

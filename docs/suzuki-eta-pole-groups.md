# Finite eta contours for complete carrier-pole groups

The actual Suzuki carrier now has a finite arithmetic contour
approximation that retains pole groups of every analytic order. On a
fixed admissible rectangle inside the open spectral strip, it gives a
signed upper bound for the complete weighted pole sum with any prescribed
positive error after sufficiently long truncation. The arithmetic
expression on the right still needs a bound at the RH source threshold.

## The actual arithmetic denominator

Use the original spectral coordinate and its reflection:

```
A(z)=xi(1/2+i*z),   E(z)=A(z)+i*A'(z),
s=1/2-i*z,         H(s)=pairedEtaXiCompletionFactor(s),
eta(s)=pairedEtaCore(s),   L(s)=H'(s)/H(s).
```

On `0<Re(s)<1`, the repository's completed eta theorem gives
`H(s)*eta(s)=xi(s)`. The factor `H` is analytic and nonzero there, and
`L` equals the explicit elementary and digamma correction already
formalised in the eta branch. Differentiating the actual completed
identity and using the xi functional equation gives

```
D(s)=eta'(s)+(1+L(s))*eta(s),
E(z)=H(s)*D(s),
C(z)=i*eta(s)/D(s)   when E(z)!=0.
```

These identities do not divide by eta. They therefore include xi zeros
where the original carrier denominator is nonzero. The exact equivalence
`D(s)!=0 iff E(z)!=0` is proved, with the completion nonvanishing discharged.
At a shared xi/denominator zero, the original literal carrier's totalized
value is not silently identified with this quotient.

The main identity is `suzukiXiZeroCarrier_eq_etaCarrier` in
[SuzukiEtaCarrier.lean](../RiemannGaussian/SuzukiEtaCarrier.lean).

## Finite arithmetic coefficients and their signed numerator

Let `eta_N` be the first `N` paired odd/even eta terms, and `eta_N'` its
explicit finite derivative sum. Define

```
D_N(s)=eta_N'(s)+(1+L(s))*eta_N(s),
C_N(z)=i*eta_N(s)/D_N(s),  s=1/2-i*z.
```

The finite denominator is exactly

```
sum_{n=0}^{N-1}
  (1+L(s)-log(2n+1))*(2n+1)^(-s)
  -(1+L(s)-log(2n+2))*(2n+2)^(-s).
```

These are the literal arithmetic coefficients, with their original
odd/even signs and logarithmic phases. No coefficient family is searched
for or selected. For any complex test value `B`, Lean also proves

```
Im(B*C_N(z))
  = Re(B*eta_N(s)*conj(D_N(s)))/normSq(D_N(s)).
```

The eta sum and logarithmically weighted sum stay coupled in this exact
numerator. No positivity or cancellation estimate for it is asserted.
See `suzukiEtaFiniteCarrierDenominator_eq_log_weighted_sum` and
`im_mul_suzukiEtaFiniteCarrier`.

## Compact convergence with the analytic conditions proved

The existing eta and differentiated eta convergence theorems imply
`D_N->D` locally uniformly in `0<Re(s)<1`. The full and finite
denominators are analytic, including through their zeros.

Consequently `C_N->C` locally uniformly on precisely

```
-1/2 < Im(z) < 1/2,   E(z)!=0.
```

On every compact subset, the finite denominators are eventually all
nonzero. The proof uses the positive minimum of the actual denominator
norm and uniform convergence. The finite carriers are then proved
continuous there. Every fixed continuous complex weight and compact
parametrized path in that domain has a convergent interval integral,
with eventual integrability established before passing to the limit.

Only the path avoids poles; its enclosed region need not do so.
These results are in
[SuzukiEtaCarrierLimit.lean](../RiemannGaussian/SuzukiEtaCarrierLimit.lean).

## Complete mixed residue groups

For the original genuine zero nodes `rho,sigma`, replace only the carrier
in the mixed channel:

```
F_N(rho,sigma,z)
  = C_N(z)/((z-conj(alpha_rho))*(z-alpha_sigma)).
```

Let `[l,r] x [b,u]` be an actual admissible rectangle, meaning its four
side lines avoid the complete xi/carrier singular set. Require

```
-1/2 < b < u < 1/2.
```

The finite arithmetic rectangular integral converges to

```
2*pi*i*(Z(rho,sigma)+K(rho,sigma)),
```

where `Z` is the exact original xi-node source, with its analytic
multiplicities, and `K` is the sum of **all** genuine carrier-pole mixed
residues inside the rectangle. The existing arbitrary-order residue
theorem supplies this complete sum. No slope division, simplicity
assumption, pole separation, or enumeration of finite-approximant poles
is used.

For any finite node set `S` and complex weights `w`, write

```
I_N(w)=sum_{rho,sigma in S} conj(w_rho)*w_sigma*integral_rectangle F_N,
Z(w)=sum_{rho,sigma in S} conj(w_rho)*w_sigma*Z(rho,sigma),
K(w)=sum_{rho,sigma in S} conj(w_rho)*w_sigma*K(rho,sigma).
```

The complete complex identity is `I_N(w)->2*pi*i*(Z(w)+K(w))`.
All mixed weights and contour orientations remain present. Therefore
the literal finite arithmetic expression

```
Phi_N(w)=Im(I_N(w))/(2*pi)-Re(Z(w))
```

converges to `Re(K(w))`. In particular, for every `epsilon>0`,

```
Re(K(w)) <= Phi_N(w)+epsilon
```

for all sufficiently large `N`. The exact source is subtracted with
its original sign; it is not absorbed into the allowance. The statements
hold for every fixed finite complex weight family. No absolute error
uniform over arbitrarily rescaled weights is claimed.

The terminal theorem is `eventually_suzukiXiPoleForm_le_etaFinite_add` in
[SuzukiEtaPoleGroups.lean](../RiemannGaussian/SuzukiEtaPoleGroups.lean).

## What still prevents the global contradiction

The active target remains an independent source ceiling for

```
J_R=2*pi*Re(Q_rho(K_R))-Re(Q_rho(S_R)).
```

Its proved limit under a hypothetical right-half zero is the source
`2*pi/m_rho` plus strictly positive Gram energy. The new result bounds
fixed pole groups by explicit finite arithmetic contours, but does not
show that those contours lie below the required source ceiling after
coupling them to the two strip sides.

The eta convergence domain is the **open** spectral strip. The endpoint
`Im(z)=1/2` is not included: the completion has apparent dyadic-factor
singularities on the corresponding line `Re(s)=1`. At the real spectral
boundary, shared xi/denominator zeros also need the existing removable
boundary analysis. Neither passage is supplied by fixed compact
convergence alone. Expanding contours and changing truncations require
their own controlled limit argument.

The next arithmetic estimate must control the retained logarithmically
weighted eta numerator together with its denominator and oriented strip
terms. The finite expression can still carry the full source excess.
No new zero has been excluded and no global source bound has been proved.

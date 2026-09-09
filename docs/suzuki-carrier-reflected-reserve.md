# Reflected reserves and the actual carrier-pole contribution

The constructed global xi expansion now reaches the repository's existing
spectral Cauchy windows and complete Blaschke sum. It proves a signed bound
that retains any finite amount of the reflected divisor. In parallel,
the actual carrier-pole contributions are evaluated without assuming simple
poles or positive residues. These are analytic advances needed for the
contour comparison; the independent global arithmetic inequality remains
open. No additional zeta-zero exclusion or `13/18` certificate is proved.

## The full spectral expansion

Use the actual repository coordinates and functions

```text
A(z) = xi(1/2+i*z),       alpha_rho = -i*(rho-1/2),
q(z) = A'(z)/A(z),       E(z) = A(z)+i*A'(z),
C(z) = i*A(z)/E(z),      C_sharp(z) = -i*A(z)/E_sharp(z).
```

The quotient identities require their respective denominators to be
nonzero. In particular, they are not used to assign analytic values at
carrier poles.

The genuine functional partner sends `alpha` to `-alpha`, preserves the
analytic multiplicity, and permutes every nonnegative symmetric cutoff.
Transporting the absolutely convergent completed reflected pairs therefore
proves

```text
sum_(|Re alpha| <= T) m_alpha/(z-alpha) -> q(z)
```

where `A(z) != 0`. This is convergence of the existing literal spectral
windows; the unpaired complex series is not asserted to converge
absolutely. The previous `riemannXiSpectralWindowLogDerivativeRawRemainder`
now tends to zero. Entry points:

- `tendsto_riemannXiSpectralWindowCauchySum`
- `tendsto_riemannXiSpectralWindowLogDerivativeRawRemainder`

Both are in [RiemannXiGlobalBlaschkeSplit.lean](../RiemannGaussian/RiemannXiGlobalBlaschkeSplit.lean).

## Keeping the reflected baseline

Let `U_T`, `K_T`, and `L_T` denote the upper, critical, and lower spectral
Cauchy windows. The existing signed Blaschke window is `B_T=U_T-L_T`.
The exact complex identity, before taking an imaginary part, is

```text
(U_T+K_T+L_T)-B_T = K_T+2*L_T.
```

For `Im(z)>0`, `A(z)!=0`, the constructed limits give

```text
K_T(z)+2*L_T(z) -> q(z)-B(z),
Im(q(z)-B(z)) <= 0,
```

where `B` is the existing absolutely convergent complete signed Blaschke
logarithmic derivative. No unknown additive constant survives. These are
`tendsto_riemannXiSpectral_reflectedCauchyWindow` and
`im_logDeriv_riemannXiSpectral_sub_blaschke_nonpos`.

Keeping the size of the negative contribution sharpens this sign bound.
Define the actual finite reserve

```text
P_alpha(z) = m_alpha*(Im(z)-Im(alpha))/|z-alpha|^2,

R_T(z) = sum_(critical window T) P_alpha(z)
         + 2*sum_(lower window T) P_alpha(z).
```

The terms are nonnegative in the upper half-plane, and Lean proves

```text
0 <= R_S(z) <= R_T(z)                    (0 <= S <= T),
R_T(z) -> Im(B(z))-Im(q(z)),
Im(q(z)) <= Im(B(z))-R_T(z)             (T >= 0).
```

Thus the unexplored reflected tail has a favorable sign. Retaining a
larger window never weakens the estimate. No numerical or specially chosen
coefficient family occurs here.

At an actual carrier pole away from the xi divisor, `q(c)=i` exactly.
Consequently

```text
Im(B(c)) >= 1+R_T(c)                    for every T >= 0.
```

If an independent estimate instead gives `Im(B(z)) < 1+R_T(z)`, it proves
`E(z)!=0` and

```text
|C(z)| <= 1/(1+R_T(z)-Im(B(z))).
```

These theorems apply inside the strip as well as outside it. The strict
Blaschke upper budget is an explicit, still-open hypothesis where the
global comparison needs it; proving this implication does not prove that
budget. Terminal entry points in
[SuzukiCarrierReflectedReserve.lean](../RiemannGaussian/SuzukiCarrierReflectedReserve.lean):

- `tendsto_riemannXiReflectedPoissonReserve`
- `im_logDeriv_riemannXiSpectral_le_blaschke_sub_reserve`
- `one_add_reserve_le_im_blaschke_at_suzukiXiE_pole`
- `norm_suzukiXiZeroCarrier_le_of_blaschke_reserve_budget`

## Carrier poles cannot be dropped from the signed contour

The actual entire `E` is nonzero at the safe point `i`, so its analytic
order is finite everywhere. At a zero `c` with `A(c)!=0`, let that order
be `m>=1`. Its local factorization is

```text
E(z) = (z-c)^m*u_c(z),       u_c(c)!=0,
C(z) = G_c(z)/(z-c)^m,      G_c(z)=i*A(z)/u_c(z).
```

Both `u_c` and `G_c` are analytic at `c`; `G_c(c)!=0`. For the original
ordered mixed denominator

```text
D_(rho,sigma)(z) = (z-conj(alpha_rho))*(z-alpha_sigma),
```

both factors are nonzero at `c`. The exact mixed residue is

```text
r_(rho,sigma)(c) = (G_c/D_(rho,sigma))^(m-1)(c)/(m-1)!.
```

For every sufficiently small positive radius, the genuine circle integral
of `C/D` is `2*pi*i*r`. The reflected channel has zero circle integral
there: `E(c)=0` and `A(c)!=0` imply `E_sharp(c)!=0`. Therefore the signed
Gram continuation `(C-C_sharp)/(2*i*D)` has circle integral

```text
pi*r_(rho,sigma)(c).
```

This generally survives the channel subtraction. It differs from the
already-proved removal of the mixed Gram's xi-node singularities. Multiple
carrier poles require the derivative of the full mixed numerator, including
the node denominators; a simple-residue formula cannot replace it.
See `eventually_suzukiXiCarrierGram_circle_at_E_pole` in
[SuzukiCarrierPoleResidues.lean](../RiemannGaussian/SuzukiCarrierPoleResidues.lean).

## All finite tests retain the reflected phase

At any such carrier pole, differentiation gives `E'(c)=i*A(c)*q'(c)`.
If the pole is simple, `q'(c)!=0`, and

```text
r_(rho,sigma)(c) = 1/(q'(c)*D_(rho,sigma)(c)).
```

For arbitrary finite zero nodes `S` and arbitrary complex coefficients
`w_rho`, set `P(z)=sum_(rho in S) w_rho/(z-alpha_rho)`. The exact full
quadratic contribution is then

```text
sum_(rho,sigma in S) conj(w_rho)*w_sigma*r_(rho,sigma)(c)
  = conj(P(conj(c)))*P(c)/q'(c).
```

The two evaluation points differ at a nonreal pole, and the slope has its
own complex phase. A norm-square interpretation would lose this structure
and could impose a sign that has not been proved. The compiled theorem is
`suzukiXiMixedCarrierPoleResidue_quadratic_eq_reflected_test` in
[SuzukiCarrierPoleQuadratic.lean](../RiemannGaussian/SuzukiCarrierPoleQuadratic.lean).

## Remaining mathematical obligation

The subsequent [finite contour assembly](suzuki-carrier-finite-contour.md)
now expresses the actual mixed channel as its explicit reflected xi source
plus the complete carrier-pole correction. It also retains the signed
matrix, its conjugate transpose and all oriented side terms. The original
symmetric outer horizontal bound is `8/T`; variable admissible upper
rectangles have outer top bound `16/R`.

The real-axis limit, collective pole correction and vertical sides remain
uncontrolled. The limiting comparison must retain both mixed indices,
the positive reflected reserve and any required real-node half residues.
A positive boundary Gram or the nonpositive reflected remainder alone
supplies no global RH bound.

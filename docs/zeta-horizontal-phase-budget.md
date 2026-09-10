# Horizontal phase comparisons and the signed zero background

The actual zeta completion has a favorable sign under horizontal
subtraction. This produces an exact phase identity with a nonnegative
Gamma reserve and no positive Gamma allowance. The paired identity
requires only summable nonnegative coefficients, with arbitrary real
frequencies and no logarithmic frequency moment.

The complete zero difference is signed. Its negative background remains
in every identity and inequality. Controlling that background together
with the prime work is still necessary for a source contradiction.

## The actual completion, before taking a bound

The preceding [global budget](zeta-global-phase-budget.md) uses

```text
R(s) = 1/s - log(pi)/2 + digamma(s/2)/2.
```

One exact Gamma recurrence gives, on `Re(s)>0`,

```text
R(s)  = digamma(s/2+1)/2 - log(pi)/2,
R'(s) = trigamma(s/2+1)/4.
```

The existing signed trigamma estimate proves

```text
Re R'(s) > 0,     |R'(s)| <= 1,     Re(s)>0.
```

Consequently, at every fixed real `y`, `Re R(sigma+i*y)` is strictly
increasing with `sigma>0`. Also

```text
|R(w)-R(s)| <= |w-s|,     Re(s)>0, Re(w)>0.
```

These are actual completion estimates with all derivative hypotheses
discharged. The compiled entries are
[`zetaGlobalRegularCorrection_eq_shifted`,
`hasDerivAt_zetaGlobalRegularCorrection`,
`norm_zetaGlobalRegularCorrection_sub_le`,
`strictMonoOn_re_zetaGlobalRegularCorrection`](../RiemannGaussian/ZetaRegularCorrectionVariation.lean).

## Complete horizontal blocks

Fix `1 < sigma <= tau`. Let `P(s,rho)` denote the actual
multiplicity-weighted Poisson summand from the global expansion. Define

```text
Z_delta(y) = sum_rho [P(sigma+i*y,rho)-P(tau+i*y,rho)],
Q_delta(y) = (sigma-1)/((sigma-1)^2+y^2)
               - (tau-1)/((tau-1)^2+y^2),
G_delta(y) = Re[R(tau+i*y)-R(sigma+i*y)].
```

Every zero series is absolutely convergent at its fixed ordinate.
Subtracting the complete global identities gives

```text
Re[-zeta'/zeta(sigma+i*y)] - Re[-zeta'/zeta(tau+i*y)]
  + Z_delta(y) + G_delta(y) = Q_delta(y).
```

Here `G_delta(y)>=0` and `|G_delta(y)|<=tau-sigma` for every `y`.
The arithmetic Euler-axis bound, exact pole bound, and complete Gamma
variation therefore give

```text
|Z_delta(y)| <= 1/(sigma-1) + 1/(tau-1) + tau-sigma
                 + Re[-zeta'/zeta(sigma)]
                 + Re[-zeta'/zeta(tau)].
```

This bound is independent of height. It controls the signed complete
block; it does not bound the sum of absolute values of all its zero
terms by the same constant. See
[`zeta_horizontal_real_budget`,
`zeta_horizontal_real_budget_le`,
`abs_tsum_zetaHorizontalPoissonSummand_le`](../RiemannGaussian/ZetaHorizontalBudget.lean).

## Arbitrary countable phase families

Let `a_n>=0`, with `sum a_n` finite, and choose arbitrary real
frequencies `omega_n`. Define

```text
K(theta) = sum_n a_n*cos(omega_n*theta),
W_delta  = sum_m Lambda(m)*(m^(-sigma)-m^(-tau))*K(y*log(m)).
```

All channels in the following identity are proved convergent:

```text
W_delta + sum_n a_n*Z_delta(omega_n*y)
        + sum_n a_n*G_delta(omega_n*y)
  = sum_n a_n*Q_delta(omega_n*y).
```

The uniform bound on each signed zero block proves
`sum_n |a_n*Z_delta(omega_n*y)| < infinity`. No condition on
`sum_n a_n*log(1+|omega_n|)` is needed. Each zero block is formed first;
the proof does not exchange the zero and frequency sums or assert
absolute convergence of the corresponding double series.

The complete prime series is the difference of two genuinely convergent
arithmetic series. The exact identity is
[`zetaPhase_horizontal_primeWork_add_zeroMass_add_gamma_eq`](../RiemannGaussian/ZetaPhaseHorizontalBudget.lean).

If `K(theta)>=0` for every `theta`, each prime-power contribution to
`W_delta` is nonnegative. Every finite set `F` therefore satisfies

```text
sum_(m in F) Lambda(m)*(m^(-sigma)-m^(-tau))*K(y*log(m))
  + sum_n a_n*Z_delta(omega_n*y)
  + sum_n a_n*G_delta(omega_n*y)
  <= sum_n a_n*Q_delta(omega_n*y).
```

The full favorable Gamma reserve stays on the left. This is
[`zetaPhase_horizontal_finite_primeWork_add_zeroMass_add_gamma_le`](../RiemannGaussian/ZetaPhaseHorizontalBudget.lean).

## What happens to the selected source

For a genuine zero `rho=beta+i*gamma` with multiplicity `m`, write
`u=sigma-beta`, `v=tau-beta`, and `r=y-gamma`. Its exact contribution is

```text
P(sigma+i*y,rho)-P(tau+i*y,rho)
  = m*(tau-sigma)*(u*v-r^2)/((u^2+r^2)*(v^2+r^2)).
```

For `sigma<tau`, its value at `y=gamma` is the strictly positive source
`m*(tau-sigma)/(u*v)`. When `r^2>u*v`, the same contribution is strictly
negative. Both signs are compiled theorems, including the genuine
multiplicity and domain conditions:
[`zetaHorizontalPoissonSummand_at_ordinate`,
`zetaHorizontalPoissonSummand_eq_signed_fraction`,
`zetaHorizontalPoissonSummand_pos_at_ordinate`,
`zetaHorizontalPoissonSummand_neg_of_far`](../RiemannGaussian/ZetaHorizontalBudget.lean).

The positive source at its own ordinate is present for critical-line
zeros too. It does not by itself distinguish a hypothetical right-half
zero. A contradiction must control the remaining signed zero background
and arithmetic work with the selected off-line source retained.

This comparison changes both the prime amplitudes and the zero kernel.
It does not replace the error in the previous single-abscissa zero
inequality by zero while leaving that inequality otherwise unchanged.
The new result removes the Gamma allowance and the logarithmic frequency
condition in the paired identity. The independent estimate needed for
global exclusion remains open, and no new zero region or RH theorem is
asserted.

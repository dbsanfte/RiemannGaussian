# Exact phase optimizer with the global half-logarithm bound

The compiled theorem `nontrivialZetaZero_mem_phase_half_log_strip` in
[ZetaPhaseHalfLogZeroFree.lean](../RiemannGaussian/ZetaPhaseHalfLogZeroFree.lean)
proves that every genuine nontrivial zero `rho=beta+i*gamma` satisfies

```text
1/(12*log(abs(gamma)+22)) < beta < 1-1/(12*log(abs(gamma)+22)).
```

All arithmetic and analytic premises are discharged. The corresponding
`riemannZeta_ne_zero_of_phase_half_log_margin` gives literal zeta
nonvanishing on the closed right-edge region, with its pole excluded.
The width is exactly twice the preceding
[half-logarithm strip](zeta-half-log-zero-free.md), at every ordinate.
This improves the repository's proved region. It is not a claim of a
best published region, and the global RH objective remains open.

## The combination

The proof uses the existing exact phase optimizer, including all its
separated higher frequencies. Its coefficients and optimizer definition
are unchanged. The newer global completion estimate applies to all
admissible phase families; it can therefore be applied to that exact family.
No coefficient search is needed.

Let `a` be the exact family, `d=1-beta`, `sigma=1+(13/4)*d`, and let `c`
be the canonical Stechkin coefficient. Write `m` for the actual analytic
multiplicity and `W` for the complete signed Stechkin prime work. The first
theorem keeps the exact source and all frequency costs:

```text
source(a) + (4/17)*a(1)*(m-1) + d*W
 <= d*(1-c)*(a(0)*log(sigma)+A*log(sigma+abs(gamma))+B)/2
      +(13/4)*A*d^2/gamma^2,
```

where `A` is the full nonconstant-frequency mass and `B` its logarithmic
frequency moment. No height restriction or further zero-location premise
is required beyond selecting a right-half zero.

The existing exact optimizer theorems give

```text
source(a) >= 11/625,   A <= 61/100,   B <= 1/4.
```

Its normalized coefficient budget also gives `a(0)<=1`. Thus
`phaseContactExact_half_log_zero_budget` proves

```text
11/625 + d*W
 <= d*(1-c)*H + (793/400)*d^2/gamma^2,
H=(log(sigma)+(61/100)*log(sigma+abs(gamma))+1/4)/2.
```

Both the complete signed-work theorem and its numerical cost bound remain
available. The existing nonnegative exact phase kernel, applied to each
nonnegative Stechkin prime-power amplitude, proves the independent floor
`W>=0`.

## The actual contradiction

Set `L=log(abs(gamma)+22)>3`. A zero violating the asserted right margin
would satisfy

```text
d*L <= 1/12,   d <= 1/36,   log(sigma) <= 13/144,
log(sigma+abs(gamma)) <= L,   H <= (181/500)*L.
```

The proved comparison coefficient gives `c>=4/9`. The
[centered Euler eta theorem](eta-centered-euler-zero-free.md) gives
`gamma^2>3` for every actual nontrivial zero. Consequently

```text
d*(1-c)*H <= (181/900)*d*L,
(793/400)*d^2/gamma^2 <= (793/129600)*d*L.
```

The full right side is therefore at most

```text
26857/1555200 < 11/625 <= 11/625+d*W.
```

This is the independent source-beating inequality in the stated region.
Actual critical reflection gives the matching left margin. The theorem
`zetaPhaseHalfLogZeroMargin_eq_twice` checks the exact width comparison.

## Stronger arithmetic reserve retained

For every `1<sigma<=5/4`, the existing binomial prime-power theorem also
transfers to the full Stechkin work:

```text
(1-c)/40 * exp(-4*(sigma-1)*log(2)) <= W(sigma,gamma).
```

This is `phaseContactExact_stechkin_binomial_floor`. Its substitution into
the complete half-logarithm budget is
`phaseContactExact_half_log_scaled_zero_source`, valid for actual zeros
with `beta>=12/13`. It retains a strictly positive arithmetic reserve
`d*(1-c)/40*exp(-13*d*log(2))`. The uniform doubled-width theorem already
follows from nonnegativity, while the sharper inequality remains available
for further signed comparisons.

## Remaining global task

The edge width still decreases logarithmically with height. This theorem
does not exclude zeros throughout the interior `1/2<beta<1`, establish the
independent finite-prime-band bound there, or control the full positive
reflected Suzuki source. The goal remains an independent source-beating
signed inequality for every hypothetical right-half zero.

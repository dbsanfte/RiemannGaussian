# Phase energy and the actual prime scale

The binomial return argument now keeps both the evaluation point and the
energy of every frequency. It gives a larger independent arithmetic floor
and a phase-sensitive exclusion test for the literal zeta function near
the right edge. The global signed bound needed for RH remains open.

## General identities and doubling

Write `K(t) = sum_n a_n cos(omega_n*t)` and `A = sum_n a_n`, for any
summable nonnegative real-frequency spectrum. For the binomial return test
`c_j = choose(N,j)`, let `R_k` be its complete ordered autocorrelation.
The new exact identity is

```text
sum_{k=1}^N R_k K(k*theta)
  = sum_n a_n (2+2*cos(omega_n*theta))^N - choose(2N,N)*A.
```

`hasSum_zetaPhase_binomial_energy` proves convergence and the identity;
`zetaPhase_binomial_return_identity` removes the diagonal explicitly.
Both are in [ZetaPhaseAutocorrelation.lean](../RiemannGaussian/ZetaPhaseAutocorrelation.lean).
The proof uses the existing Gram identity from the hybrid eta phase
machinery, through `hasSum_zetaPhase_gramEnergy`. Both sine and cosine
squares are retained before the trigonometric power is evaluated.

There is also a degree-independent coupling bound, proved in
`binomial_trig_double_reserve`:

```text
min(u,v) <= u*(2+2*cos(theta))^N + v*(2+2*cos(2*theta))^N  (u,v >= 0).
```

If `cos(theta) >= -1/2`, the first base is at least one. Otherwise
`cos(2*theta) = 2*cos(theta)^2-1` makes the second base at least one.
Thus these two frequency energies cannot disappear together.
`zetaPhase_binomial_doubled_source` carries this into the general return
bound: whenever distinct indices `r,i,j` have `omega_r=0` and
`omega_j=2*omega_i`, the source is at least

```text
4^N*a_r + min(a_i,a_j) - choose(2N,N)*A.
```

This generalizes the idea behind the repository's contact-doubling
argument to binomial energies. It does not require the exact optimizer,
integer frequencies, finite support, or nonnegativity of `K` itself.
Nonnegativity of `K` is required in the subsequent arithmetic comparison.

## Arithmetic bound with scale retained

For degree ten and prime two, throughout `1 < sigma <= 5/4`, put

```text
v(sigma) = log(2)*exp(-4*sigma*log(2))/77520.
E(theta) = sum_n a_n*(2+2*cos(omega_n*theta))^10.
W(sigma,y) = sum_m Lambda(m)*m^(-sigma)*K(y*log(m)).
```

The two endpoint cost checks prove
`v(sigma)*R_k <= log(2)*2^(-sigma*k)` for all ten retained lags.
For each lag, its cost relative to the fourth lag is monotone in `sigma`;
this is why endpoint checks control the entire interval. The actual prime
coefficients are preserved.

`zetaPhase_binomial_scaled_energy_le` in
[ZetaPhaseBinomialScale.lean](../RiemannGaussian/ZetaPhaseBinomialScale.lean)
then proves, for every admissible spectrum and every real `y`,

```text
v(sigma) * (E(y*log(2)) - 184756*A) <= W(sigma,y).
```

For the existing exact optimizer, the full source is at least `46790`.
Its energy is exactly the finite sum over the nine already proved
coefficients; no phase coefficients are fitted or changed.
The compiled comparison `phaseContactExact_binomial_energy_reserve_ge_scaled`
and arithmetic theorem `phaseContactExact_binomial_scaled_arithmetic_floor`
give

```text
(1/40)*exp(-4*(sigma-1)*log(2))
  <= v(sigma)*(E(y*log(2))-184756*A) <= W(sigma,y).
```

The left side is always at least `1/80` on the stated interval and tends
to `1/40` as `sigma` decreases to one. This concerns the lower bound, not
a claim that the arithmetic work itself has that limit.

## Literal zero exclusion

Let `d=1-Re(s)` and `L=log(abs(Im(s))+22)`. For `Re(s)>=15/16` and
`abs(Im(s))>=1`, `phaseContactExact_binomial_scaled_exclusion` proves
`zeta(s) != 0` when

```text
448*d*((61/100)*L+83/100) + (793/400)*d^2/Im(s)^2
  < 11/625 + (d/40)*exp(-13*d*log(2)).
```

`phaseContactExact_binomial_energy_exclusion` retains more information:
replace the last reserve by

```text
d*log(2)/1240320 * exp(-13*d*log(2))
  * (E(Im(s)*log(2))-184756*A).
```

Its threshold depends on the actual linked phases of the tested height.
For `d>=0` the proved energy comparison recovers the uniform reserve.
The intermediate budget theorems also keep the exact efficiency,
multiplicity and true weighted height sum before their explicit bounds.

These are stronger near-edge exclusions. A larger arithmetic reserve is
not an equal proportional increase in the width of a zero-free region.
The logarithmic height allowance remains, and the missing global Suzuki
inequality has not been established. These binomial and doubling
identities are classical mathematics; no historical novelty claim is made.

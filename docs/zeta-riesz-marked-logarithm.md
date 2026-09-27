# Paid logarithmic-derivative bridge and exact joint cancellation ledger

This local continuation starts from `34ee00fd155545435ffbd5c2543cc10d1a9e2590`.
That snapshot passed GitHub Actions run `36258001944`, deployed to Pages,
and passed the published README and RH-explorer browser checks.

The new arithmetic estimate is in `ZetaRieszMarkedLogDerivative`.
It pays the **whole coupled proper-prime-power difference**, including
the ordered cofactor and both Fourier frequencies. The main signed packet
and the complementary carrier still have no independent floor.

## Exact replacement

Write `M_k(s)=zetaPrimeLogMoment k s`, the signed factorial moment of
`-zeta'/zeta`, and `P_j(s)=ordinaryPrimeMoment j s`. At every selected
marked order `j>0`,

\[
 \frac{M_{j-1}(s)-M_{j-1}(s+i\xi)}j
 =P_j(s)-P_j(s+i\xi)+E_j(s,\xi).
\]

Here `E_j=properDifference j` is exactly the corresponding proper-prime-power
series divided by `j`. `logDifference_split` proves the identity and
`properDifference_series` supplies its convergent arithmetic expansion.
The unused marked order zero keeps its original definition; no low
cofactor or least-prime order is deleted.

The proper-power series converges beyond real part `1/2`. At the safe
center `3/2+i*y`, its factorial radius can therefore be `3/4`, whereas
the cofactor retains `R=1/2-1/262144`. The literal rectangle has
`j>=21N/40`. `proper_radius_saving` and `proper_marked_bound` turn this
radius difference into `exp(-N/10)` relative to `R^(-j)`.

`properSymbol_bound` retains the full ordered cofactor and its correlated
order `N+1-j-h`. The two marked phases give a quadratic Fourier zero.
`properPair_profile` bounds the actual paired integrand by a constant
multiple of `1/(1+xi^2)`, proving genuine integrability over all positive
frequencies. No frequency endpoint is omitted.

`norm_scaled_properResponse_le`, `properRate_bounds` and
`tendsto_properResponse` prove

\[
 |u^{N+1}E_N|\le C(N+2)^3r_{\rm pp}^{N},\qquad
 r_{\rm pp}=\frac{10001/20000}{1/2-1/262144}e^{-1/10}
 <\frac{91}{100}.
\]

The rate is approximately `0.9049348059`; the rational upper bound is
proved in Lean. The constant is defined by convergent arithmetic majorants
and is not a small-order numerical bound. This estimate is uniform in
arbitrary moving heights and finite cofactor prime sets above 16.
`tendsto_log_sub_current` connects the resulting `logMain` to the unchanged
dyadic target, lower-threshold counts 3–55 minus short-overflow counts 3–13.
It is source equivalence, not a bound on `logMain`.

## What the joint identity actually cancels

`ZetaRieszOrderedWard.logarithmic_convolution` proves the exact signed law

\[
 \sum_{j=0}^{n}[-\partial_s]^j(-F'/F)/j!
                   \;[-\partial_s]^{n-j}F/(n-j)!
 =(n+1)\,[-\partial_s]^{n+1}F/(n+1)!.
\]

The theorem uses the same function in the logarithmic derivative and the
cofactor. `neg_logDeriv_quotient` instantiates its slope as the actual finite
Euler sum, with both shifted frequencies. `ordered_quotient_convolution`
keeps the literal tail `q>r`.

For the present carrier there are two further terms. The complete marked
prime range differs from the finite ordered tail, and the marked order is
restricted to the rectangle. `marked_ordered_ledger` retains both terms:

\[
 \text{selected complete-slope convolution}
 =\text{derivative of the same quotient}
  -\text{omitted-order convolution}
  +\text{selected prime-range mismatch}.
\]

`rangeMismatch_eq` identifies the last input exactly as the complete zeta
logarithmic difference minus the finite Euler slope. No norm or completion
of that term is silently supplied. Also, `moment_completeSlope` retains
the marked factor `j`: using this derivative identity on the original
unlogged marked kernel requires keeping its reciprocal `1/j` weight.

These identities do not remove the least-prime order window, replace the
cofactor by a complete zeta quotient, or assert cancellation of each
frequency separately. The follow-on below pays the range mismatch while
preserving the window. The old completion/source and masked-phase no-gos
still apply.

## The prime-range mismatch is now paid

`ZetaRieszMatchedSlope` matches the high marked logarithmic derivative to
the cofactor's **own finite ordered Euler product**. For
`Q_r={p in A | r<p}`, the remaining symbol is exactly

\[
 \sum_{j,h}\sum_{r\in A}
 \frac{[-\partial_s]^{j-1}(-\partial_s\log Q_r)}{j!}
 (1-r^{-i\xi})K_h(s,r)
 \frac{[-\partial_s]^{N+1-j-h}Q_r}{(N+1-j-h)!},
\]

where `Q_r` in this formula denotes its Euler quotient, and `(j,h)` still
runs over the literal `rectangleOrders`. Equivalently, the first factor
is `signedTaylorMoment (j-1) (-logDeriv Q_r) / j`.
`slopeMark_eq_logDeriv` justifies this identification as a neighborhood
identity before differentiation. The least-prime leg, total order, two
Fourier signs, physical length and reciprocal `1/j` are all unchanged.

`mismatchAtom_split` separates its difference from the already paid
`separatedSymbol` into exactly two errors:

1. Extra local prime powers in the finite Euler logarithmic derivative.
   `local_power_identity` factors their entire two-frequency difference
   as `q^2(1-z)(1+z-q*z)/((1-q)(1-q*z))`. The quadratic amplitude admits
   Cauchy radius `3/4`; the Fourier factor `1-z` remains present.
2. Ordinary marked primes `p<=r`, which have the forbidden ordering for
   the high and low factorial slots. The existing unequal-radius
   `wrong_order_atom` bound pays these terms by `exp(-N/10)`.

`matchedSymbol_bound` sums both errors over the literal least-prime set
and entire rectangle. `matchedPair_profile` retains both Fourier zeros
and pays the full integral with the majorant `1/(1+xi^2)`.
`norm_scaled_mismatchResponse_le` and `tendsto_mismatchResponse` give
`C(N+2)^3*r_pp^N`, using the same proved `r_pp<91/100`. This bound contains
no zero hypothesis and is uniform in arbitrary moving heights and finite
prime sets. No cofactor completion is used.

`tendsto_matched_sub_current` connects this matched symbol to the unchanged
dyadic packet. `symbol_difference_eq_rangeMismatch` identifies the exact
complete-minus-matched input as the earlier `rangeMismatch` moment **inside
the original factorial rectangle**, and `tendsto_log_sub_matched` proves
its full response tends to zero at source scale by combining the paid
bridges. The latter also includes the preceding high-prime completion rate;
do not attribute the stronger `r_pp` rate to that entire combined bridge.

The prime-range mismatch is therefore no longer an unpaid term. What
remains is the signed restricted-order convolution of a finite ordered
Euler quotient with its own logarithmic derivative, with the reciprocal
`1/j` weight. Applying the full derivative identity still introduces its
explicit complementary order sum. Neither that window nor the whole
matched main response has an independent bound yet. The final
complementary carrier also still needs its independent signed floor.

The optional `N=262144`, `64/160/256` coupled refinement completed its rows
but failed its requested final precision gate. Its
[checkpoint audit](zeta-riesz-owner-integration-audit.md) recovers a wider
finite-grid enclosure consistent with the earlier radial rule. It is a
model diagnostic, not the prime-sum bound proved or needed here.

The subsequent [marked saturation estimate](zeta-riesz-marked-saturation.md)
pays the entire unshifted Riesz cofactor branch of the same literal
arithmetic packet by `C*(N+1)*r^N`, with `r<991/1000`. Its exact remaining
profile is `R_(L-log p)(n/p)`, with all marked factorial weights retained.
`tendsto_matched_sub_reflected` connects that profile to `matchedMain`.
Neither retained main term has been bounded.

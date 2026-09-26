# Paid nonlinear correction in the ordered marked Euler response

The remaining signed arithmetic target has not changed. On the original
dyadic schedule it is the source-normalized `lowerThresholdPacket`
(counts 3–55) minus `shortOverflowPacket` (counts 3–13), for
`1/2 < u <= 10001/20000`. No signed floor or new zero exclusion is proved
in this slice.

The [subsequent marked-prime separation](zeta-riesz-marked-separation.md)
pays both the wrong-order incidences and the marked-prime collision. It
isolates a finite two-frequency high-prime difference while retaining the
ordered cofactor Euler response; their joint signed integral remains open.

The new result is an independent, quantitative bound on the **full**
nonlinear Euler correction after the original marked factorial operator,
ordered prime-pair sums and paired Fourier integral. Its leading quotient
is included in that bound.

## Exact object and bound

For a finite middle prime set `Q`, put

\[
A_Q(s,\xi)=\prod_{p\in Q}\bigl(1+p^{-s}(1-p^{-i\xi})\bigr),\qquad
V_Q(s,\xi)=\prod_{p\in Q}\frac{1-p^{-s-i\xi}}{1-p^{-s}}.
\]

`ZetaRieszMarkedEulerError.error_eq` keeps the identity
`A_Q - V_Q = V_Q * (correctionProduct - 1)` intact.
On `Re s >= sigma > 1`, with every `log p >= N/110`,
`norm_error_le` proves

\[
|A_Q(s,\xi)-V_Q(s,\xi)|\le C_\sigma e^{-N/220}.
\]

The constant is an explicit finite expression in absolutely convergent
arithmetic masses and is independent of `Q`, height and frequency.
It is not intended as a practical small-order numerical constant.

`coeff_character` identifies every analytic factorial moment with the
existing formal prime-product coefficient, including order zero.
`rectangle_split` therefore decomposes the existing finite rectangle
exactly. For its correlated orders `j`, `h` and `N+1-j-h`, one common
Cauchy radius costs `R^(-(N+1))`, with at most `(N+2)^2` terms.

The two marked factors retain the integrable frequency bound

\[
|1-p^{-i\xi}|\,|1-r^{-i\xi}|
\le (1-\cos(\xi\log p))+(1-\cos(\xi\log r)).
\]

`integral_norm_rectanglePairError_div_le` proves ordinary integrability
and pays the complete two-frequency correction using the exact cosine
integral. Its marked logarithmic cost is `log p + log r`.
`ZetaRieszOrderedEulerBound.norm_errorIntegral_le` then pays every
ordered pair `r < p` by convergent arithmetic mass and log-mass sums.

At

\[
R=\frac32-\left(1+\frac1{262144}\right),\qquad
U=\frac{10001}{20000},\qquad
r_*=\frac{U}{R}e^{-1/220}<\frac{249}{250},
\]

`norm_scaled_errorResponse_le` bounds the original normalized response by

\[
\bigl|u^{N+1}\,\mathrm{errorResponse}_N\bigr|
\le C(N+2)^3 r_*^N.
\]

The diagnostic decimal for `r_*` is approximately `0.9955720`; the rational
upper bound above is the Lean-checked assertion. `tendsto_errorResponse`
proves decay for arbitrary moving finite prime sets and heights, retaining
the original normalization `(N+1)/(2*pi*L)` for every `L >= 1`.

## Connection to the actual carrier

`ZetaRieszMarkedPrimeHead` independently pays every label containing a
prime `p <= exp(N/110)`. On the existing radial core, such a label lies
outside the already-controlled least-share interior. The same radial and
unrestricted-count share bounds pay the entire head, without a zero
hypothesis or prime-phase approximation.

`ZetaRieszRoughEulerTransfer` retains the original physical prime universe
after removing this paid head. `complete_sub_rough` is the exact arithmetic
ledger. `roughPacket_split` is the exact integral ledger. Finally,
`tendsto_main_sub_current` proves that the leading ordered quotient differs
from the unchanged current signed packet by source-scale `o(1)`.

Thus the live task is a signed estimate for `mainQuotient`, including its
least-prime ordering, both marked factorial coordinates, original moving
Riesz length and both Fourier frequencies. The nonlinear factor no longer
carries an unpaid mixed error. Neither this main quotient nor the
complementary carrier has acquired the required independent floor.

More explicitly, for each marked pair `r < p`, the middle set is exactly
`Q = {q in roughPrimes : r < q and q != p}`. For each original rectangle
order `(j,h)`, the remaining order is `k = N+1-j-h`. The surviving summand
inside the Fourier integral is

\[
(1-p^{-i\xi})K_j(s,p)\,(1-r^{-i\xi})K_h(s,r)\,
\frac{(-\partial_s)^k}{k!}
\prod_{q\in Q}\frac{1-q^{-s-i\xi}}{1-q^{-s}}.
\]

This is summed over the exact rectangle and ordered pairs, then paired
with `exp(i*xi*L)` at `xi` and `exp(-i*xi*L)` at `-xi`, divided by `xi^2`
and integrated. It is not an unmarked global Euler product. Any next
estimate must control this joint signed quantity; a bound on a relative
factor or a separately completed prime leg would not supply the missing
arithmetic estimate.

No low orders were discarded; no separate complete-leg phase limit,
generic prime-density transport or infinite zero-divisor inverse was used.
The existing no-go audits remain in force. The optional long numerical
renewal integration is a separate diagnostic and is not an input to any
theorem above.

## Paid frequency exteriors of the remaining main term

`ZetaRieszMainFrequency` now bounds the two exterior frequency integrals of
the actual main quotient. It does not replace the quotient or separate its
prime phases. The exact marked factors give

\[
|1-p^{-i\xi}|\le \min(2,|\xi|\log p).
\]

After the full middle quotient is differentiated and the exact rectangle
and ordered marked pairs are summed, write

\[
B_N=\frac{(N+2)^2\exp(4M_\sigma)}{R^{N+1}},
\qquad M_\sigma=\sum_{n\ge0}e^{-\sigma\log n},
\qquad H_\sigma=\frac{2}{\sigma-1}M_{(\sigma+1)/2}.
\]

The repository's totalized natural logarithm is used also at `n=0`;
this adds only a finite harmless term to these majorants. For the original
paired numerator `quotientPair`, the checked bounds are

\[
\left|\frac{\mathrm{quotientPair}_N(\xi)}{\xi^2}\right|
\le 2B_NH_\sigma^2,
\qquad
\left|\frac{\mathrm{quotientPair}_N(\xi)}{\xi^2}\right|
\le \frac{8B_NM_\sigma^2}{\xi^2}.
\]

`norm_small_integral_le` and `norm_large_integral_le` integrate these
bounds on `0..epsilon` and `X..infinity`. With
`epsilon=exp(-N/220)` and `X=exp(N/220)`,
`norm_scaled_exterior_le` restores the original physical length and proves

\[
|u^{N+1}\,\mathrm{exteriorResponse}_N|
\le C_{\sigma,R,U}(N+2)^3r_*^N,
\qquad r_*<249/250.
\]

`response_split_frequency` is the exact integral ledger.
`tendsto_central_sub_current` connects the central response to the
**unchanged** signed counts `3..55` minus short overflow `3..13`, with
source-scale difference tending to zero. The conclusion holds without a
hypothetical zero; the exterior estimate is uniform in moving heights.

The open term is now exactly `centralMain`: the same coupled ordered prime
quotient and factorial rectangle, integrated over
`exp(-N/220)..exp(N/220)`. This interval still grows with `N`; these
estimates do **not** provide a bound for its signed integral. No arithmetic
floor or zero exclusion follows yet.

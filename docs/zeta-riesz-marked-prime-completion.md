# Paid completion of the separated marked prime

`ZetaRieszMarkedPrimeCompletion` proves an independent error estimate for
the next step after [marked-prime separation](zeta-riesz-marked-separation.md).
It completes only the high-order marked prime. The least prime and the
ordered cofactor Euler product remain at their literal cutoffs.

The fixed signed target remains `lowerThresholdPacket` (counts 3–55)
minus `shortOverflowPacket` (counts 3–13) on the original dyadic schedule.
Neither that signed sum nor its complementary carrier has an independent
floor yet. This result pays a specific error; it is not packet decay or a
zero exclusion.

## Exact object

With `A=roughPrimes u N`, write

\[
 D_j(s,\xi)=P_j(s)-P_j(s+i\xi),\qquad
 P_j(s)=\sum_{p\text{ prime}}\frac{(\log p)^j}{j!}p^{-s}.
\]

The new `completedSymbol` is exactly

\[
 \sum_j\sum_{h\in\operatorname{rectangleOrders}(N,j)}
 D_j(s,\xi)
 \sum_{r\in A}(1-r^{-i\xi})K_h(s,r)
 \frac{(-\partial_s)^{N+1-j-h}}{(N+1-j-h)!}
 \prod_{q\in A,\ q>r}\frac{1-q^{-s-i\xi}}{1-q^{-s}}.
\]

It is integrated with both original Riesz phases, division by `xi^2`,
the original moving length and prefactor `(N+1)/(2*pi*L)`.
`difference_split`, `completedSymbol_split` and `completedResponse_split`
are exact signed identities, with genuine series convergence and Fourier
integrability. No prime phase is replaced by an exposed-zero limit.
No composite cofactor is completed.

## Independently bounded errors

`eventually_rough_support` proves that every omitted prime eventually has
either `log p <= N/110` or `log p >= 11N/8`. This includes both the fixed
floor and polynomial lower cutoff. The upper claim uses the actual moving
physical length for `0<u<=10001/20000`.

Set `R=1/2-1/262144` and `sigma=3/2-R`. On the exact rectangle,
`omitted_kernel_bound` proves for both omitted ranges

\[
 |K_j(s,p)|\le e^{-N/160}R^{-j}p^{-\sigma}
 \quad (\Re s=3/2).
\]

The lower range uses the marked radius `2R`, together with `j>=21N/40`.
The upper range uses `5R/6`, `j<=23N/40`, the physical slope `11/8`, and
the checked enclosure `log(6/5)<=3/16`. The cofactor keeps radius `R`,
so the full correlated order is still `N+1`.

The missing difference retains `1-p^(-i*xi)`. Along with the least-prime
factor `1-r^(-i*xi)`, it gives a quadratic zero at the Fourier origin.
`completionError_small` and `completionError_large` prove the corresponding
quadratic and uniform bounds. `completionPair_profile` combines them into
an integrable multiple of `1/(1+xi^2)` on the entire frequency axis.
`norm_integral_completionPair_le` pays that complete integral; no moving
frequency boundary or hidden division by a small frequency is omitted.

## Terminal source-scale estimate

`norm_scaled_errorResponse_le` and `tendsto_errorResponse` prove

\[
 \left|u^{N+1}\bigl(\operatorname{completedMain}_N-
          \operatorname{separatedMain}_N\bigr)\right|
 \le C(N+2)^3r_*^N,
 \qquad
 r_*=\frac{10001/20000}{1/2-1/262144}e^{-1/220}<249/250
\]

eventually, uniformly in arbitrary moving evaluation heights. The raw
`exp(-N/160)` saving is relaxed to the already checked `r_*` only at this
last step. The constant is explicit in convergent prime-weight majorants;
it is not asserted to be a useful small-order numerical constant.

`tendsto_completed_sub_current` connects this operator to the unchanged
dyadic signed target for `1/2<u<=10001/20000`. No zero hypothesis enters
any completion-error bound.

The open arithmetic estimate is the joint Fourier pairing of the complete
difference `P_j(s)-P_j(s+i*xi)` with the **finite ordered cofactor** above.
In particular, the shifted frequency cannot be discarded, and a bound or
limit for a separate complete prime leg does not estimate this product.
The independent signed main estimate and complementary floor remain open.

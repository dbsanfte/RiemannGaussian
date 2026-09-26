# Paid separation of the high-order marked prime

`ZetaRieszMarkedSeparation` removes two specific restrictions from the
remaining signed Euler response with a proved source-scale error. The
unchanged arithmetic target is still `lowerThresholdPacket` (counts 3–55)
minus `shortOverflowPacket` (counts 3–13), on its original dyadic schedule.
The new theorem is a paid separation, **not** a bound on that signed target.

## Exact surviving operator

Let `A=roughPrimes u N` be the original finite physical prime set after the
already-paid exponential head. Define

\[
D_{A,j}(s,\xi)=\sum_{p\in A}\bigl(K_j(s,p)-K_j(s+i\xi,p)\bigr),
\qquad
V_{A,r}(s,\xi)=\prod_{q\in A,\ q>r}
\frac{1-q^{-s-i\xi}}{1-q^{-s}}.
\]

`coeff_leg_difference` proves the exact two-frequency prime identity.
`separatedSymbol_factor` proves that the new symbol is

\[
\sum_j\sum_{h\in\operatorname{rectangleOrders}(N,j)}
D_{A,j}(s,\xi)
\sum_{r\in A}(1-r^{-i\xi})K_h(s,r)
\frac{(-\partial_s)^{N+1-j-h}}{(N+1-j-h)!}V_{A,r}(s,\xi).
\]

The rectangle is unchanged: the high order satisfies
`21N <= 40j <= 23N`, the low order satisfies
`N <= 100(h+1) <= 4N`, and the existing `ownerOrders` condition remains.
Every middle factorial order, including zero, is present. The two original
Fourier signs, the factor `1/xi^2`, moving Riesz length and prefactor
`(N+1)/(2*pi*L)` are retained in `separatedResponse`.

The high-prime sum now runs independently over `A`. The least-prime tail
still has its exact ordering `q>r`. This is a finite arithmetic identity
and error estimate; no complete-leg phase limit has been inserted.

## Two independently paid errors

The original symbol permits only `r<p` and excludes `p` from the cofactor
Euler product. The new symbol permits every `p in A` and retains that
factor if `p>r`.

For the newly admitted `p<=r` incidences, the unequal marked Cauchy radii
`3R/2` and `R/2` have no extra arithmetic weight cost:

\[
p^{-\sigma+R/2}r^{-\sigma-R/2}\le p^{-\sigma}r^{-\sigma}.
\]

`rectangle_tilt` proves, on the exact order box,

\[
(2/3)^j2^h\le e^{-N/10}.
\]

`wrong_order_rectangle` carries this saving through the entire correlated
middle moment. The bound is uniform in height and Fourier frequency.

For `p>r`, restoring `p` in the cofactor product creates the explicit
`collision` difference. Its local factor has norm at most `4*p^(-Re s)`.
Since every prime in `A` has `log p>N/110`,
`collision_rectangle_bound` pays this extra prime occurrence by
`exp(-N/220)` through the same full rectangle. It does not silently allow
repeated primes in the literal carrier.

The signed error ledger is `symbol_difference_ledger`. Both errors retain
the two marked phase zeros. The cosine integral therefore pays their
complete Fourier integral, including frequency zero; ordinary integrability
is proved before subtracting the responses.

## Source-scale conclusion and open estimate

`norm_scaled_response_difference_le` proves

\[
\left|u^{N+1}
  (\operatorname{mainQuotient}_N-\operatorname{separatedMain}_N)\right|
\le C(N+2)^3r_*^N,
\qquad
r_*=\frac{10001/20000}{1/2-1/262144}e^{-1/220}<249/250.
\]

The constant is explicit in the previously defined convergent mass and
log-mass sums. It is independent of the finite prime cutoffs and height,
but is not intended as a practical small-order numerical constant.
`tendsto_separated_sub_current` connects this response to the unchanged
signed arithmetic target, with source-scale difference tending to zero.
No zero hypothesis or independent signed-bound premise is used.

The subsequent [marked-prime completion](zeta-riesz-marked-prime-completion.md)
pays replacement of `D_{A,j}` by the complete ordinary-prime difference,
including the full Fourier integral. The cofactor remains finite and ordered.

The open estimate is the **joint Fourier pairing** of that difference with
the ordered cofactor factor in the displayed formula. Its two frequencies
must stay coupled with the Riesz phase and correlated total order. The
least-prime Euler tail is not bounded by this separation, and separate
prime-phase convergence would still not bound the whole integral. The
complementary carrier also still needs its independent one-sided floor.
No zero exclusion is claimed.

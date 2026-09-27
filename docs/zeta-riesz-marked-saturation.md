# The unshifted marked-cofactor branch is paid

`ZetaRieszMarkedSaturation` proves an independent geometric bound for one
whole cutoff branch of the current literal marked packet. The other branch
remains signed and unbounded. This is component control, not packet decay,
an independent floor, or a zero exclusion.

For every squarefree label with at least three prime factors and every
marked prime `p|n`, prime deletion gives the exact identity

\[
 -R_L(n)=-R_L(n/p)+R_{L-\log p}(n/p).
\]

`unshiftedAtom` and `reflectedAtom` retain the original `markedWeight`,
including its full factorial rectangle and canonical least-prime order.
Both have total kernel order `N+1`, full phase `n^(-i*y)`, and the exact
prefactor `(N+1)/L`. `atom_split` proves their sum equals the existing
`ZetaRieszPhysicalCompletion.atom`. `completePacket_split` applies this
identity on the unchanged finite physical prime-subset universe.

## The proved saving

The cofactor `n/p` is squarefree, nonunit and composite. When
`log(n/p)<=L`, the unshifted Riesz response is exactly zero: its saturated
divisor sum equals the von Mangoldt function of that composite.
`cofactor_data` and `riesz_cofactor_eq_zero` discharge those arithmetic
conditions. Prime cofactors are not silently included.

On the remaining side `log(n/p)>=L`, the exact rectangle gives
`j>=21N/40` on the marked prime. `markedWeight_tilt` sums the correlated
multinomial weights first, tilting only that coordinate by `5/4`.
With

\[
 R=\frac12-\frac1{262144},\qquad v=\frac45R,
\]

the marked prime uses factorial radius `R` and its entire cofactor uses
`v`. The same observed logarithms satisfy
`log(n)=log(p)+log(n/p)`; no independent prime or cofactor model is used.
For the actual eventual length bound `L>=11N/8`, `saturation_tilt` proves

\[
 e^{-(21/40)N\log(5/4)}v^{-(N+1)}e^{-(R/5)L}
 \le \frac54 R^{-(N+1)}e^{-N/100}.
\]

This estimate follows from the rational margin
`(19/40)*log(5/4)-11R/40 < -1/100`. A numerical tilt scan motivated
the choice; Lean proves the displayed inequality without numerical trust.
Only the error estimate enlarges the positive allocation sum. The retained
reflected response still has its original rectangle.

`marked_kernel_cofactor_tail` inserts the actual factorial kernel.
`unshifted_incidence_bound` combines the two cofactor cases before summing
marked incidences. The complete signed divisor sum is retained until its
saturation cancellation has been used. The remaining divisor cost is bounded
by the existing `zetaMoebiusLogMajorant`. The prime-factor count costs at most
`2*log(n)` and is absorbed by a slightly smaller, still convergent arithmetic
abscissa. No fixed count ceiling is assumed.

For every finite label selection `T`, every real height `y`,
`0<=u<=U=10001/20000`, `L>=1`, and `L>=11N/8`,
`norm_scaled_unshiftedPacket_le` proves

\[
 \left|u^{N+1}U_N(T,L,y)\right|
 \le C(N+1)r^N,
 \qquad
 r=\frac UR e^{-1/100}<\frac{991}{1000},
\]

where

\[
 C=1310720\frac UR\,
   \operatorname{zetaMoebiusLogMajorantMass}\!\left(1+\frac1{524288}\right).
\]

The rate enclosure is `saturationRate_bounds`. The constant is a genuinely
convergent arithmetic mass, not a small finite-order numerical bound.
`tendsto_unshiftedPacket` gives decay with the original moving physical
length, arbitrary moving finite label masks, and arbitrary moving heights.

## What remains

`tendsto_reflected_sub_current` connects `reflectedMain` to the unchanged
dyadic target: lower-threshold counts 3–55 minus short-overflow counts 3–13.
Its exact retained input is

\[
 \frac{N+1}{L_N}
 \sum_n\sum_{p\mid n}
  R_{L_N-\log p}(n/p)\,
  \operatorname{markedWeight}(N,n,p)\,
  K_{N+1}(3/2+i y,n).
\]

The sums use the original finite physical subset universe; all least-prime
and factorial restrictions remain in `markedWeight`.
`tendsto_matched_sub_reflected` also connects this retained arithmetic
profile to the matched ordered-Euler logarithmic-derivative response from
the preceding slice. These are two rigorously equivalent views of the
same open signed target.

The remaining work is cancellation in the reflected cofactor profile across
prime incidences and counts. The full unmasked logarithmic-derivative identity
still does not bound the selected order window or justify dropping its `1/j`
weight. The final complementary carrier still needs its independent floor.
No cofactor completion, separate prime-phase transfer, or zero hypothesis is
used in the new bound.

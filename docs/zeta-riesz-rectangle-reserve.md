# Literal allocation-safe rectangle: reserve and remaining ledger

The requested rectangle supplies a **proved eventual reserve of at least
`1/160`**, with its original finite masks and old unassigned factor. This
holds under the original **simple exposed-zero** hypotheses and
`1/2 < u <= 10001/20000`. The sign is the one confirmed by the user:
the reserve is **minus** the rectangle's contribution to
`ownerCompletionCorrection`.

This is a quantitative signed estimate on the literal selected carrier.
It is **not a restricted contradiction or a new zero-free region**. The
comparison with the whole carrier exposes an unestimated complement and
a matching negative owned copy. In particular, the numerical gap between
the known source and the desired floor was never an independently proved
budget for all remaining arithmetic terms. The strict whole-carrier pass
criterion remains unmet; the geometric and literal-reserve tests pass.

## Exact selection

Write `n=p*q*r` with `p>q>r`, distinguish the second prime `q`, and retain
the existing `secondIncidences`, `tripleBand`, narrow window, reflected
threshold `log p >= log n - L`, nondominant support, physical prime set,
squarefreeness, coprimality, full product phase and `1-boundedShare`.
All three primes belong to the original physical set and exceed `N^2`.
The finite orders are exactly

$$
21N\le40j\le23N,\qquad N\le100(h+1)\le4N,
\qquad j+\ell+h+1=N+2,
$$

with `j+h` in the existing `ownerOrders`. On this incidence the existing
exact coefficient is `-R_L(n)=log r`. The selected factorial atom is

$$
\frac{N+1}{L}(1-\theta_N(n))
\sum_{j,h\text{ in the rectangle}}
(h+1)K_j(p)K_{N+1-j-h}(q)K_{h+1}(r).
$$

`rectangleAtom_eq_factorials` proves this identity, and
`rectangleResponse_eq_nonowner_rows` reindexes it into the actual second
prime's rows of the original correction. The incidence is unique; no
average over marked pairs is used. No composite cofactor is completed.

## Independently paid errors

Let `U=10001/20000` and `d=131071/262144`. The joint binomial estimate
`boundedShare_mul_rectangleMass` proves

$$
\theta_N(n)\,\operatorname{rectangleMass}_N(n)
\le 3e^{-N/3200}.
$$

It includes **every prime incidence** in the old allocation, not only
the largest one. The normalized allocated response has geometric rate

$$
r_{\rm alloc}=\frac U d e^{-1/3200}<1.
$$

The five separate prime-log cuts used to verify the literal masks are

$$
N<\log p\le\frac54N,\qquad
\frac7{10}N<\log q\le N,\qquad
\log r\le\frac1{10}N.
$$

Together with the original total window
`39N/20 < log n <= 41N/20`, they imply strict ordering, exactly two
reflected-large primes, and all the original integer masks. Failures of
these cuts are paid with exact exponential tilts. The total-window proof
retains the correlated total order `N+2`. The aggregate error is bounded
by a fixed summable majorant times a polynomial in `N` and

$$
r_{\rm mask}^{N},\qquad
r_{\rm mask}=\frac U d e^{-1/4000}<1.
$$

Both rates are proved strictly below one in Lean. The allocation and
mask-decay theorems hold uniformly for **arbitrary moving heights**, with
no hypothetical-zero premise. The finite separate-prime comparison keeps
the exact rectangle of orders; it is not a global all-order prime product.
`tendsto_separate_sub_rectangle` proves that its difference from the
literal unassigned rectangle is source-scale `o(1)`.

## Signed reserve

The completion estimate extends to each of the three separate prime
orders, including the derivative order `h+1 >= N/100`, without completing
`p*r`. Its error is bounded by a fixed convergent majorant times
`(N+1)^3 exp(-N/25000)`. Each normalized prime phase tends uniformly to
`-m` under the original exposed-zero hypotheses.

The three-leg product therefore has **negative** source phase. For a
simple zero, exact finite lattice counting gives the source-weight bound

$$
\sum_{j,h}\frac{N+1}{uL\,j\,(N+1-j-h)}\ge\frac1{147}
\quad(N\ge1000).
$$

No continuum integral or numerical quadrature is used. Uniform phase
control gives real part at most `-1/150` before the literal comparison;
the comparison error is eventually smaller than `1/2400`. Hence
`eventually_rectangleReserve_ge` proves, on the original dyadic schedule,

$$
\operatorname{Re}\bigl(u^{N+1}S_N\bigr)\ge\frac1{160},
\qquad S_N=-\operatorname{rectangleResponse}_N.
$$

The starting dyadic index is existential. No claim is made that the
numerically sampled orders already satisfy the eventual theorem.

## Exact whole-carrier ledger

Let `C` be the existing `wideComplete`, `E` the original correction,
`U_3` the already paid unallocated triples, and `H` the signed nontriple
part of the narrowed carrier. Let `E_rest` be the **explicit original
correction sums with only the rectangle's factorial terms removed**.
`correction_eq_rectangle_rest` and
`narrow_rectangle_completion_ledger` prove

$$
E=E_{\rm rest}-S,\qquad
R_{\rm narrow}=H+C-E_{\rm rest}+S+U_3.
$$

No estimate for `E_rest` is assumed. It still contains the original
completion/off-mask/allocation differences, the other nonowner incidences,
and all unselected factorial orders of the second incidence. The errors
paid above compare **this rectangle** with its separate prime legs; they
do not pay the remainder of the original global correction.

The rectangle also belongs to the original largest-prime owner's band:
its complementary cofactor order `N+1-j` is in `ownerOrders`.
`ownedRectangleWeight_bounds` proves it is a genuine suballocation of
that owner. If `O_rest` is the explicit remaining owned finite sum, then

$$
O=O_{\rm rest}-S,\qquad
T_3=O_{\rm rest}+U_3-S,\qquad
C-E_{\rm rest}=O_{\rm rest}-2S.
$$

The last equality is `completion_rest_rectangle_ledger`. Thus the
positive correction removes a duplicate negative incidence; it does not
make the original owned copy positive. `not_tendsto_owned_rectangle_zero`
proves that matching copy cannot be discarded as a vanishing error.

The reserve is real progress on one signed component. Closing the
contradiction still requires a joint independent lower bound on
`H+C-E_rest`, or equivalently on the remaining direct finite carrier with
its surviving negative rectangle. No such bound is proved here. The
`1/160` reserve alone is not a proof of the `-3/40` whole-carrier floor.
This is an obstruction to double counting or discarding the matching
owned copy, **not** an impossibility theorem for all rank-two cancellation.
The original `LocalizedTypeIIBound`, earlier quarter-gap no-go, and all
public zero-free/certificate frontiers are unchanged.

## Lean sources

- [Exact rectangle](../RiemannGaussian/ZetaRieszRectangle.lean)
- [Joint allocation bound](../RiemannGaussian/ZetaRieszRectangleAllocation.lean)
  and [allocated response](../RiemannGaussian/ZetaRieszRectangleError.lean)
- [Literal geometry](../RiemannGaussian/ZetaRieszRectangleGeometry.lean),
  [exact finite comparison](../RiemannGaussian/ZetaRieszRectangleCube.lean),
  [tail rates](../RiemannGaussian/ZetaRieszRectangleTailRates.lean),
  [kernel tails](../RiemannGaussian/ZetaRieszRectangleTails.lean), and
  [complete mask error](../RiemannGaussian/ZetaRieszRectangleMaskError.lean)
- [Separate prime phases](../RiemannGaussian/ZetaRieszRectanglePhase.lean),
  [discrete density](../RiemannGaussian/ZetaRieszRectangleWeights.lean), and
  [literal reserve](../RiemannGaussian/ZetaRieszRectangleReserve.lean)
- [Matching owned copy](../RiemannGaussian/ZetaRieszRectangleLedger.lean) and
  [original correction ledger](../RiemannGaussian/ZetaRieszRectangleCorrection.lean)

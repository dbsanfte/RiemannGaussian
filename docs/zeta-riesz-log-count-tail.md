# A logarithmic prime-count tail is paid in both directions

The literal joint carrier now has a checked payment for **all sufficiently
high prime counts together**, including both radial boundaries. The
[multiplicity-safe endgame](zeta-riesz-joint-floor.md) still needs its
whole-sum floor and ceiling; neither is proved by this component payment.

Define the explicit integer threshold and relative cost

\[
\kappa_N=8\lceil\log_2(N+1)\rceil,\qquad
b_N=\frac{512e^4}{(N+1)^4}\longrightarrow0.
\]

`Nat.clog` implements the rounded logarithm exactly. For any finite
selection of squarefree labels with

\[
2M\le\log n\le2M+2,\qquad
N\le2M,\quad M\le2N,\quad \omega(n)\ge\kappa_N,
\]

[`logarithmic_count_norm_upper`](../RiemannGaussian/ZetaRieszLogCountBudget.lean)
proves, for every positive length `L`, height and allocation set,

\[
\left\|\sum_n c_{A,L,N}(n)
 \mathcal K_N(3/2+iy,n)\right\|
\le b_N\,
\frac{M e^{2M}}{M+1}\,
\frac{e^{-3M}(2M)^N}{N!}.
\]

The kernel is the existing `zetaPrimeLogKernel`.
The coefficient is the original `residualCoefficient`, including
`1-boundedShare`. No phase, coprimality, support or factorial mask is
replaced by a density model. Any further finite selection is allowed.

## Why the count tail is cheap enough

For a squarefree label, the divisor count is exactly
`tau(n)=2^omega(n)`. Thus for any selected set below `X` with
`omega(n)>=K`,

\[
\sum_n2^{\omega(n)}
\le2^{-K}\sum_{n\le X}\tau(n)^2
\le2^{-K}X(1+\log X)^3.
\]

The last inequality is the repo's existing, complete second-divisor-moment
theorem. There is no averaging assumption about primes. The original
coefficient costs at most `log(n)*2^omega(n)`. Combining this with the
literal factorial envelope costs four powers of `N+1`, whereas
`2^countThreshold(N)>=(N+1)^8` supplies eight. This gives the explicit
`b_N` above. The count sum includes every parity and every frequency.

Crucially, the comparison is to the **same signed four-prime supply**
already present in the ledger. Its magnitude is bounded below by a fixed
positive multiple of the displayed radial scale. Hence the whole count
tail costs at most one sixty-fourth of that supply eventually. The
starting order depends on the existing supply constant and height and
has not been numerically certified.

## The exact signed ledger

[`ZetaRieszLogCountTail.eventually_core_full_floor`](../RiemannGaussian/ZetaRieszLogCountTail.lean)
and `eventually_core_full_ceiling` retain the previous radial payments:

| Selected charge | Fraction of the same supply |
| --- | ---: |
| Narrow balanced triples | 1/2 |
| Other selected small-prime triples | 1/8 |
| Selected small-prime four-prime labels | 1/8 |
| Positive-coefficient five-prime head | 1/8 |
| Six-prime and negative-five-prime heads | 3/32 |
| **All counts at least `countThreshold(N)`** | **1/64** |
| **Supply retained** | **1/64** |

The high-count labels have at least eight factors and are disjoint from
every older charge and supply. Positive and negative phase orientations
use separate comparisons; their supplies are not added. Every favorable
group observation and the full signed complement remain.

`exists_missed_tail_bound` pays all high-count labels missed by the
half-open radial union with a source-normalized geometric error
`r^N*C`, `0<=r<1`. It reuses the checked exterior bounds at
`244N/125` and `2029N/1000`; it does not discard the original core edges.
The older complete-boundary payments for counts 3--6 remain available
in `ZetaRieszFiveNegativeHead`; the new terminal comparisons explicitly
retain their radial versions and keep any other low-count labels in the
signed rest.

`remaining_count_lt` now proves that every squarefree label in that rest
has **strictly fewer than `8*clog(2,N+1)` factors**. This is a logarithmic
count reduction using actual arithmetic supply, rather than an estimate
for each fixed count separately. It is not a uniform fixed count ceiling.

The tail itself is **not asserted to be `o(1)` at source scale**. Its
relative cost tends to zero, and a portion of the existing supply pays
it. Multiplying a polynomial saving by the old absolute source envelope
would not justify a separate decay claim. The opposing signed rest must
still acquire the independent cofinal floor `-79/1000-o(1)` and ceiling
`3/2+o(1)` needed by the multiplicity-safe criterion.

## Literature check and next obstruction

Polymath's Proposition 4.2 gives almost-prime concentration for smooth
divisor weights, including a small least-prime estimate. Its smoothness
assumption does not match our positive-part hinge; it has not been
imported as a bound for this carrier. [Primary paper, Section 4.4](https://arxiv.org/pdf/1407.4897).

Granville, Koukoulopoulos and Maynard quantify how divisor-weight moments
depend on smoothing and factor counts. Their results help distinguish
which moment estimates are applicable, but do not supply the present
masked signed floor. [Authors' paper, Theorems 1.1--1.3](https://dms.umontreal.ca/~andrew/PDF/sieveweights.pdf).

The new payment instead uses only the already proved finite divisor
moment. The remaining difficulty is the signed population below the
logarithmic threshold, including the unpaid triple shapes and the
intermediate counts. Neither smooth-cutoff concentration nor generic
prime-density replacement may be assumed for those labels.

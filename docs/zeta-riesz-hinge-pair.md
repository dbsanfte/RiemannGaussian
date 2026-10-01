# Signed pairing across the surviving Riesz hinge

The new bounds apply to original unpaid divisor incidences in the current
central carrier. They join two adjacent four-member blocks before taking
a norm or real part. On the specified middle-half geometry, their allowance
is half the old separate ramp allowance. The whole `-79/1000` floor, ceiling
and restricted zero exclusion remain open.

The [Lean module](../RiemannGaussian/ZetaRieszHingePairCancellation.lean)
uses the original factorial kernel, allocation and complex phase. It does
not complete a prime/cofactor sum or assume a bilinear cancellation estimate.

## The exact paired response

Fix a squarefree original cofactor `a`, its prime owner `p`, and three distinct
cofactor primes `r < s < q <= p`, with `rsq | a`. A base `e | a/(rsq)` selects
the eight original incidences

\[
 (d,b)=(e\delta,a/(e\delta)),\qquad \delta\mid rsq.
\]

They are exactly the two disjoint old four-member orbits with block `rs`
and bases `e` and `eq`. Every incidence is observed at the **same original
label** `pa`; the observation is never evaluated at `p(a/e)` instead.

Put

\[
 \alpha=\log r,\quad \beta=\log s,\quad v=\log q,\quad
 P=\log p,\quad D=\log(a/e)-L,\quad S=\alpha+\beta+v.
\]

On the overlapping crossing ramps `v <= D <= alpha+beta`, the exact
two-hinge response is

\[
 \boxed{\quad
 \sum_{(d,b)}w(pa)\mu(b)
   \bigl[(\log(pb)-L)_+-(\log b-L)_+\bigr]
 =-w(pa)\mu(a/e)\,[S-2D+(S-P-D)_+].
 \quad}
\]

The last positive-part term is the **other original hinge**. It cannot be
dropped simply because the second-hinge ramps meet at their midpoint.
`weighted_paired_crossing_eq` proves this formula with all eight signs.

If `S <= P+D`, that term is zero. The old separate second-hinge ramps then
have total allowance `W = alpha+beta-v`. On

\[
 |D-S/2|\le W/4,
\]

the new independent bound is `norm(w) * W/2`. This is a factor-two saving
on this matched sector's separate ramp allowance, not on the whole floor.

## Keep the close-owner hinge too

When the owner is close to `q`, the true cancellation point moves to

\[
 \boxed{D_*(P)=S/2+(S-2P)_+/6.}
\]

`two_hinge_cancellation_center` proves that the **full** coefficient is zero
at this point. `two_hinge_cancellation_le_half` and
`norm_paired_two_hinges_le_half` prove

\[
 |D-D_*(P)|\le W/6
 \quad\Longrightarrow\quad
 |S-2D+(S-P-D)_+|\le W/2.
\]

There is no first-hinge saturation premise in this bound. Its price is half
the overlap width; the factor-two comparison above applies specifically to
the saturated case. An exact midpoint identity does not assert that many
arithmetic labels lie at that point.

## Keep the prime moments and cofactor parities joined

For the **literal** retained prime set `Pset`, set `H=S-D` and keep its actual
clipped subset `B={p in Pset : log p < H}`. The complete prime-row sum is

\[
 -\mu(a/e)\,[
   (S-2D)M_0(Pset)+H M_0(B)-M_{\log}(B)],
 \qquad
 M_0(V)=\sum_{p\in V}w(pa),\quad
 M_{\log}(V)=\sum_{p\in V}\log p\,w(pa).
\]

`re_source_scaled_literal_two_hinge_floor` gives a direct one-sided estimate
using a **single absolute value after those three signed moments are joined**.
The original allocation, factorial weight and source scaling are inside the
moments. It neither norm-pays primes individually nor assigns a separate
positive first-hinge debit. The aggregate numerical price remains unpaid.

In the saturated case, a common prime set permits a further exact
factorization across every selected base:

\[
 -M_0(Pset)\,Q_E,\qquad
 Q_E=\sum_{e\in E}\mu(a/e)[S-2(\log(a/e)-L)].
\]

The scalar also equals

\[
 [S-2(\log a-L)]\sum_{e\in E}\mu(a/e)
       +2\sum_{e\in E}\mu(a/e)\log e.
\]

Keep those two Möbius moments together. Cofactor-dependent prime endpoints
and holes do **not** justify that common-set factorization.
`correlated_paired_sum_eq` and `re_source_scaled_correlated_literal_floor`
retain the actual prime set `Pset(e)` instead. The latter proves the sector
floor with cost

\[
 \frac W2\sum_{e\in E}
   \left|\operatorname{Re}\!\left(u^{N+1}M_0(Pset(e))\right)\right|.
\]

No theorem here bounds that total by a numerical constant or proves its decay.

## Where these incidences sit in the existing ledger

`paired_crossing_subset_retained_of_overlap` proves that strict overlap puts
all eight incidences inside the **actual** original antidiagonal after the
old interior and affine zero-block deletions. Both the saturated middle-half
and adaptive two-hinge bands imply that strict overlap.

Squarefreeness makes the two old orbits disjoint. The failed based-owner gap
keeps every member outside the earlier owner-gap rows. The original owner
ceiling keeps the label outside the whole-large-owner credit. The polynomial
cutoff packet has the opposite canonical based-owner gap, so it cannot spend
these same incidences. These statements prevent double counting; they do
not remove unselected labels or change any old payment budget.

The authoritative whole carrier is still `polynomialCentralRemaining`,
source-equivalent to `joinedPhysical`. No new scalar carrier is defined.

## Optional quantitative probes and limits

[The optional probe](../scripts/probe_riesz_hinge_pair.py) stays outside
ordinary builds and CI:

```bash
../.venv/bin/python scripts/probe_riesz_hinge_pair.py --dyadic-index 1
../.venv/bin/python scripts/probe_riesz_hinge_pair.py --dyadic-index 2
```

These use the literal dyadic schedule `(N,K)=(640,16),(1536,32)`, actual
distinct primes and the original core masks. Saturated samples reproduce the
half-width saving. Close-owner samples with 15 and 28 prime factors have
nonzero first-hinge terms but cancel at the **adaptive** centre to floating
roundoff. At `N=1536` the separate blocks are approximately `+36.45458` and
`-36.45458`; ignoring the other hinge instead predicts `-36.45458`.

The all-base probe also sums every selected base of individual original
rough labels, including every cofactor parity. At `N=1536`, one spread-log
example retains 3,842 bases across four cofactor counts; its signed profile
has about 3.88% of its absolute-displacement sum. A clustered-log example
retains 42,504 bases all of the same cofactor count and has **no** such profile
saving. These are diagnostics of two geometries, not a population comparison,
starting-order certificate or proportion of the whole deficit paid.

Source-scaled observations for these individual labels underflow. The probe
reports the log amplitude and an underflow flag; it does not treat a floating
zero as cancellation evidence. A separate small-prime kernel regression
retains the other hinge and both signed clipped moments; it is explicitly
not an original core sample.

`middle_half_no_prime_shift` proves why one cannot simply iterate another
prime insertion **inside** the selected middle-half interval: its width is
smaller than the next prime log, so both endpoints cannot lie in it. An
additional pairing must retain its exterior boundary. This is a restriction
on that local selector, not a no-go for cancellation across all labels.

The remaining target is an independent source-scale bound for the **joint
signed prime/cofactor moments and their literal boundaries**, plus the
unselected surviving sectors. None of the diagnostics establishes the
`-79/1000` floor or an RH contradiction.

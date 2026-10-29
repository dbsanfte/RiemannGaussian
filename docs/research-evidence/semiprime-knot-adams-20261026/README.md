# Knot cabling, common roots, and complete skein normalization

26 October 2026. This continuation supplies constructive preparation results
and removes an extra-zero defect in the skein representation. It does **not**
improve the complete collision-query exponent. The guaranteed all-semiprime
sixth-exponent goal remains active and unproved.

For the scalar native family, put (k\asymp N^{1/6}), (H=k^2), with
(L=\widetilde O(k)) acquired reciprocal rows and physical horizon
(m=O(k^{3/2})). The original target is

\[
 K(T)=\prod_{j=1}^{L}\frac{(v_j-T)(v_j-T^{-1})}{(v_j-1)^2},
 \qquad P_m=\prod_{i=1}^{m}K(\eta^{2i+1}),\quad \eta^2=q.
\]

A zero/nonunit-only prefix oracle suffices, with the retained original labels
and decoder. The current evaluator costs
\(\widetilde O(L+\sqrt{Lm})\), or \(\widetilde O(k^{5/4})\) at this scale.
The desired \(\widetilde O(L+\sqrt m)\) evaluator is still missing.
These are costs of this route, not a claim to improve the general factoring
baseline. The quadratic supplier has its own conductor-dependent controlled
(k); its existing contract is preserved separately.

## Constructive results

| Result | Complete acquired output | Cost and limit |
|---|---|---|
| Arbitrary short-label roots | A factor, or a common base (b) and all β_j with β_j^{e_j}=b, retaining large odd local orders | \(\widetilde O(L+k)\); the common-target long query remains open |
| Separated root alphabet | A factor, or unit-separated root/clock nodes and their coefficient polynomials | \(\widetilde O(L+k)\); no free long resultant |
| Inverse to (N)-powering on the acquired alphabet | An explicit interpolation polynomial and inverse quotient-algebra maps | Continuing work \(\widetilde O(L)\), including factor branches \(\widetilde O(L+k)\); no inverse on unlisted clock points |
| Norm-one (N)-power screen | A factor, or order-coprimality with (N) on both supplied torus groups | \(\widetilde O(k)\), with unknown split orientation handled |
| Complete skein correction | A zero-equivalent skein polynomial with no extra physical zeros, and its entire scalar unit correction | \(\widetilde O(L+\sqrt m)\) for the correction; its interaction norm remains unacquired at that cost |

The first result extends the existing small-coindex shared-root construction.
For arbitrary acquired nonzero signed labels (e_j) of (O(\log N)) bits,
set (M=\prod_j|e_j|), (T=\lceil\log_2N\rceil), and (R=M^T).
The product tree acquires

\[
 b=\beta^R,\qquad \beta_j=\beta^{R/e_j},\qquad \beta_j^{e_j}=b
\]

without forming a separate wide exponent for every row. If this projection
loses the required orders, binary search finds the first short-label power
causing the loss. The previous projected clock has that single short label
as a global annihilator, so the existing extractor returns a factor.
No factorization of (M) is assumed.

With native labels (e_j=E_j), original collisions survive as
(b=q_j^i), where (q_j=\beta_j^H). A saturated accidental collision gives
the original **short**, nonzero gap (E_j-Hi) on the new large-order base.
The associated label relation is (q_j^{E_j}=b^H), **not** (b).
The conversion is therefore safe. Its raw expression has different row
bases, but equality of the retained local orders proves, at each hidden prime,

\[
 q_j^i=b \quad\Longleftrightarrow\quad (b^H)^i=b^{E_j}.
\]

Thus an explicit change back to one shared base retains the existing
\(\widetilde O(L+\sqrt{Lm})\) zero/nonunit oracle. This is predicate
equivalence, not equality of the numerical products. See
[construction](shared-label-roots.md), [independent review](shared-roots-review.md)
and [cyclic-resultant follow-up](cyclic-resultant-followup.md).

For the skein result, three fixed twist states span the required quadratics
with unit pivots. Choosing (H_v(B)=B(B-w_v)) makes the extra factor the same
known unit at every physical clock. Both orientations give exactly

\[
 H_{\rm native}(B)=B^{2L}D^{-1}P_{\rm native}(B).
\]

The complete correction is (D^{-n}U_{\rm clock}^{2L}), where

\[
 U_{\rm clock}=(\eta^3;q^2)_n(\eta^{-5};q^{-2})_n,
 \qquad n=\lfloor m/2\rfloor.
\]

Two scalar q-factorials acquire this correction in the target budget. This
settles its numerical acquisition as well as its unit status; evaluating the
remaining interaction norm still costs the original bound. The actual
opposite row transports the apparent positive endpoint (m+1) to the legal
negative index (-m). See [identity](extra-divisor-elimination.md) and
[decoder review](extra-divisor-review.md). This uses finite linear skein
combinations; it does not assert that each combination is one ordinary knot.

## What the literature supplies

Morton–Manchon connect annular power-sum operations to torus cabling;
Ohtsuki records the Alexander cabling substitution. They motivated the
common-root and powered-alphabet tests. Their identities do not themselves
acquire a product over all shorter physical windings. See
[Adams audit](adams-contraction.md) and [review](adams-review.md).

Hillar–Levine's rank-one theorem gives an algebraic relation between two
successive cyclic-resultant values in a characteristic-zero lift. The
explicit eliminant here can have enormous exponent support; the theorem
does not select an efficiently computable next value or advance the prefix
product. Silver–Williams supplies the cyclic-cover torsion interpretation,
whose non-pure cases also require Betti-number information. The
[follow-up](cyclic-resultant-followup.md) checks these hypotheses and the
common-base fallback. These are applicability findings, not general
algorithmic impossibility results. Kohli's fixed twist formulas supply the
skein states used in the constructive correction above. Primary links and
exact source locations are recorded in [sources.json](sources.json).

The torus extension of the preceding scalar screen computes, for
(A=16k^2+1), (B=\lfloor(N+A)/A^2\rfloor),

\[
 \gcd\!\left(\operatorname{Norm}\prod_{j=1}^{B}(W^{Nj}-1),N\right).
\]

It returns the larger prime exactly when the smaller prime divides the
larger-side order of (W), and otherwise returns 1; it never saturates on
the supplied contract. Combined with the scalar screen, this preserves the
local norm-zero pattern under (N)-powering of the coupled family. The
second-power identity π^{N²+1}=π^{P²+Q²} does not acquire its unknown
right-hand exponent or shorten the clock. See [proof](torus-adams.md) and
[review](torus-review.md).

A numerical Frobenius-deflated unit correction is **optional** for a
zero/nonunit-only query: subgroup injectivity already proves equivalence.
The unresolved work is the whole-clock contraction, not acquisition of that
optional unit. Multiplicative (N)-powering is not an additive ring
automorphism, so the cited skew-polynomial algorithms cannot be applied with
that map as their automorphism input.

## Scope and preservation

All mathematical claims here are paper proofs with independent review,
not Lean certificates. No new numerical campaign, implementation, Lean
module, public asset, commit or push is included. Scratch-origin reports are
archived with their review qualifications. The source ledger and manifest
record the exact archive; prior packets and journal/agent prefixes are
preserved. Existing concurrent engineering work is untouched.
See the [integration review](integration-review.md),
[validation record](review.json), and [file manifest](manifest.json).

Further work needs a complete scalar contraction or a coverage-preserving
smaller query. These acquired representations are available inputs to that
work; their construction alone does not establish the requested scaling.

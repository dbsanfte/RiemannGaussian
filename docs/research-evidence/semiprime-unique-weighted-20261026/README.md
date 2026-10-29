# Exactly one collision in the short weighted family

26 October 2026. **A public, softly linear selection algorithm now gives
exactly one good-field collision in the ENTIRE correct bin**, while keeping
the weighted clock `h=O(K^(3/2))`. This combines short weighted coverage
with global uniqueness, including nonprimitive rows and axes.

**The acquisition exponent has not improved.** The completed query still
costs `soft O(K^(5/4))`; whole-family soft-K acquisition and the complete
deterministic all-semiprime sixth-rate bit proof remain open. The new result
is a uniform paper theorem about the actual family, not a numerical
coverage claim or a Lean theorem.

## 1. The constructive selection

Use the existing prepared beta-coupled family with `K=2*3^e`, `e>=3`,
`H=K^2`, `N=PQ<=K^6`, and both primes above `16H`. For each public
factor-size bin B, complete its weighted coefficient ellipse

    a^2 B^4+b^2 N^2 <= (2/sqrt(3))*K*B^2*N

to every compatible unit colour `a*j^2=b*N mod K`. Retain only the four
shortest-axis pairs that pass the SAME bound. This input has fewer than
`23K` rows, with every phase, root and colour acquired in soft K.
Every added row retains the original clock bound and exact hit provenance
in a correct bin.

For a row define its public hypothetical hit support

    S_(a,b,j)={unit r mod K: a*r^2+ell_j*r+b*N=0 mod H}.

In a correct bin, that row hits precisely when `R mod K` belongs to its
support. Three arithmetic facts make selection possible:

1. Within one coefficient pair, these supports are exactly its equal-phase
   classes. They partition its compatible colours.
2. Along a primitive integer direction `(a0,b0)`, compatible-colour domains
   grow with the 3-adic valuation of the multiplier. Choose an existing
   pair with the largest valuation in that direction.
3. Two different directions with positive 3-adic valuation have disjoint
   domains. Otherwise their determinant would be a nonzero multiple of
   `3K`, while the ellipse bounds its absolute value by `2K/sqrt(3)`.

For each such direction, choose one actual row per maximal pair's phase
class. For every still-uncovered colour, choose one row with no 3-part in
its content, or a filtered axis. Such a row exists by the original Gauss
coverage theorem, and its support is a singleton.

The selected supports therefore **partition all unit colours modulo K**.
There are at most `phi(K)=K/3` selected rows. Their actual roots are
acquired in soft K, and their physical clock is unchanged. Since exactly
one support contains the true factor colour, exactly one selected leaf
vanishes at the nonsplit prime in a correct bin.

The [complete construction](unique-cover.md) and
[independent proof review](review-unique-cover.md) include signs, parity,
axes, all contents, wrong-bin scope and acquisition of the selection data.
The [ellipse/source proof](completed-source.md) and
[incidence review](review-incidence.md) establish the underlying arithmetic.
No nesting assertion about arbitrary phase classes is needed.

## 2. What this removes from the query

Let `u_j=[j^2]_n` be canonical integers, `n=3^ceil(e/2)`, and let `(j*,I)`
be the unique good hit. Its tag is `u=[R^2]_n`.

The selected constant-weight moment has good value **u**, without an
unknown count. More substantially, for ANY correctly supplied nonzero
clock amplitude at that hit, the whole-bin residue pair is

    (V,U)=(A,A*u), A!=0.

Thus finite Lambert weights are now allowed on the whole bank. Their
amplitudes cannot cancel between different good hits. The earlier
O(sqrt K) singleton-block partition is unnecessary for this NEW family.
A single marked arbitrary-amplitude value `A*u` is still not a bounded
integer; the two-scalar ratio and the one-scalar constant-weight moment
remain different interfaces.

Two particularly small sufficient outputs now need no separately acquired
empty-bin gate:

* The two first variations of the whole physical product,
  `P_delta(0,0), P_epsilon(0,0)` for
  `P=product(1+delta-T_j*rho^i+epsilon*u_j)`.
* The two coefficients of the first subresultant of
  `product_j(X-T_j)` and `product_(i<h)(X-rho^(-i))`.

In the correct bin their needed denominator is nonzero at the good field.
Norm/coordinate gates and the existing restricted-HH consumer give a
verified factor or bounded failure. A wrong bin may give a meaningless
ratio; it must not stop later attempts. This does not claim an exact
wrong-bin residue or permit division by unclassified nonunits. The
[readout derivation](unique-lambert.md) spells out both consumers.

## 3. The executed acquisition test

We tested a direct modified-moment approach to the one-pole readout.
Its short row polynomials, O(K) ordinary finite-Lambert moments, recurrence
coefficients and regular solution prefix are all acquired in soft K.

The missing condition is now explicit. The short equations admit a
rank-one pole attached to ANY supplied row, with that row's tag. Requiring
the pole to lie on the actual finite clock selects the correct one.
The tested way of imposing that condition still computes an implicit
q-factorial remainder at the old K^(5/4) cost. This is a failure of that
specific closure, not a lower bound on a direct first-subresultant or
selected-pole algorithm.

The regular coefficient-rectangle experiment and literal-overlap test are
in [completed-qsum.md](completed-qsum.md) and
[native-overlap.md](native-overlap.md). A genuine cubic character factors
across coefficients, but is constant inside each colour-lift fibre;
its finite Fourier fusion keeps the long clock. See
[character-source.md](character-source.md).

The immediate acquisition target is therefore ONE whole-bin projective
readout on this selected family, or its constant-weight moment. A successful
algorithm must acquire that output in soft K; the public partition itself
does not do so.

## 4. Prior credit, validation and scope

The original weighted coverage, fixed-pair chirp contraction, per-block
singletons, monic-family uniqueness and moment consumers retain their
credit. The new combination is global uniqueness at the SHORT weighted
clock, obtained by the public ellipse/domain selection. This is not a
literature-wide novelty claim.

The [public constructor and replay](validation-unique-cover.md) passed all
18 fixtures, with 442,080 catalogue support checks and 167,544 independent
selected-support checks. Root replay reproduces the metadata and counters.
These are structural diagnostics of this selection algorithm. The uniform theorem is the paper argument above,
independently reviewed; finite fixtures do not establish it. Source pins,
review scope, replay results and preservation are recorded in
[review.json](review.json), [sources.json](sources.json) and
[manifest.json](manifest.json). Earlier frozen packets and concurrent files
are preserved. No commit, push or Lean proof is included.

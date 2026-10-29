# Collective colour-query tests and exact lifting filters

26 October 2026. This pass executed three candidate ways to exploit the
stationary-colour construction: shifted polynomial overlaps, three-adic
colour lifting, and coarse Farey/factor-interval covers. **None supplies a
faster guaranteed complete query.** The strongest new operation is a
deterministic factor-or-exact-overlap test, including hidden modular aliases,
in softly linear time for each supplied clock shift. A complete index-mask
algorithm is also derived and costed; its bound remains the old one.

The objective remains guaranteed deterministic classical all-semiprime
\(\widetilde O(N^{1/6})\) factorization, including the full bit-cost
argument and eventual formal proof. It is active and unproved. In the
current route, \(k\asymp N^{1/6}\), \(J=\widetilde O(k)\), and
the common signed window has length \(h=O(k^{3/2})\). The complete
query still costs \(\widetilde O(J+\sqrt{Jh})\), rather than the
required \(\widetilde O(J+\sqrt h)\).

All constructions use the [existing prepared contract and colour family](../semiprime-knot-trace-20261026/README.md).
They do not replace the original collision with an arbitrary trace zero.

## A cheap supplied-shift test covers modular aliases too

Retain the original integer labels \(E_j\), roots \(y_j=\beta^{E_j}\),
and \(q=\beta^H\), \(H=k^2\). Deduplicate exact integer labels while
keeping their source metadata. The existing derivative/separation routine
either factors N or certifies that all node differences are units.

For a supplied nonzero shift s of the permitted size, acquire
\(F(X)=\prod_j(X-y_j)\) and evaluate \(F(q^s y_j)\) at every node.
Monic multipoint evaluation costs \(\widetilde O(J)\). Proper gcds
give factors. At a saturated value, an exact global-node lookup distinguishes:

* a literal edge \(E_\ell-E_j=Hs\);
* a global nonliteral equality, giving a nonzero short beta-annihilator;
* different matches at the two hidden primes, exposed by one O(J) scan.

The latter two cases factor through the inherited consumers. The continued
certificate costs \(\widetilde O(J)\); a terminating saturated branch
also pays the inherited extractor \(T_{\rm ext}=\widetilde
O(N^{31/192})\). Thus the general bound is
\(\widetilde O(J+T_{\rm ext})\), and the whole family fits
\(\widetilde O(k)\). Only one extractor call occurs before termination.
Thus the
continuing branch certifies, at both primes,
\[
 q^s y_j=y_\ell\quad\Longleftrightarrow\quad E_\ell-E_j=Hs
 \text{ as integers}.
\]
It also constructs the corresponding monic shifted gcd without assuming
a field-gcd oracle over the composite ring. For s=1 the native literal
components have at most two nodes, so hidden longer local chains would
already produce a factor. This strengthens the previous integer-only
overlap analysis for this executed test.

The missing implication is coverage: the guaranteed witness is a clock
point matching one row at P and its partner at Q. It need not force a
same-field edge at any of a supplied short list of shifts. Testing
O(log h) shifts is cheap, but no such list is proved sufficient. See
[algorithm and accounting](colour-selector.md) and [review](colour-selector-review.md).

## Colour lifts give exact filters, with their full query cost

For a parent scale K, colour j and row (a,b), put
\(D=(aj^2-bN)/K\). Of the three children \(j+Kt\), a child is
stationary precisely when
\[
 D+2ajt\equiv0\pmod3.
\]
If a is a 3-adic unit, there is exactly one such child. In the ramified
case there are zero or three. The canonical child phases are computed
using the exact rational identity
\[
 F(j+Kt)-F(j)=K^2\frac{t(D+ajt)}{j(j+Kt)},
 \qquad F(x)=ax+bN/x.
\]
The denominator matters at the bottom level K=6. With
\(\lambda_t=\lambda+HL_t\), the positive child index i corresponds
to the parent index \(9i-L_t\). The negative convention gives
\(-9i-L_t\). When three phases form a complete coset they interlace
to a stride-three string of length 3m; the endpoints and mass remain.

At the final scale, the actual factor in colour j gives an explicit
quadratic image for its original index modulo \(R=3^e=k/2\).
Completing the square, or reducing common coefficient valuations, describes
every such image by O(log k) arithmetic progressions. The unit-quadratic
case is a translated, scaled set of squares. Its limiting density is 3/8;
higher powers of three do not impose independent half-density restrictions.
Axis rows have the full index image. For unit rows this is exactly the existing intrinsic conic-square mask, with centre (lambda²-4abN)/(2*lambda*H) computed by integer division before modular inversion. Colour tags add no independent filtering condition there.

These masks preserve the original witnesses and original leaf decoder.
Grouping by progression stride d and residue, within one common original
window or prefix, costs
\[
 \widetilde O\!\left(J_d+\sqrt{J_d(h+d)}\right).
\]
Summing the logarithmically many stride levels retains
\(\widetilde O(J+\sqrt{Jh})\). The construction therefore has a
complete cost argument, without an exponent improvement. See
[exact lift, filter and decoder](colour-lift.md) and [review](colour-lift-review.md).

## Coarse slopes still require their phases and windows

A fixed primitive native vector with its fixed phase determines at most
one public unit colour. Identifying the lattices for j and -j saves a
constant factor but does not identify their phases.

There is a more substantial shared-slope candidate: take \(d=3^r\),
\(d^2\mid k\), and scale an admitted coarse vector by d. Across its
d colour lifts the phases follow an explicitly computed quadratic modulo d.
For a primitive core with 3-adic unit coordinates, that quadratic has at
least d/3 distinct values. Native axes, treated separately, have exactly
d phases. Counting one common slope as one row would omit these phases.
This is a bound for this particular completed coarse-cell construction,
not a lower bound for all covers.

Public factor-interval subdivision also has explicit rational endpoints
and a legal clipped-window implementation. Its straightforward T-cell
construction acquires O(kT) row/cell descriptions and has upper interval
budget O(kh+kT). A sparse critical-point cover could improve this; no
uniform sparse-cover theorem was obtained. See [cover tests](farey-cover.md)
and [review](farey-cover-review.md).

## Correction and next mathematical requirement

The previous mixed-trace discussion was too broad about quadratic
exponent acquisition. A formal map is available:
\[
 \beta^{(aP-bQ)^2}
 =\beta^{-N(a+b)^2}
   \gamma^{(N+1)(a^2+b^2)}
   \delta^{(N+1)(a^2-b^2)}.
\]
Here \(\gamma=\beta^{(N+1)/2}\) is acquired, while the mixed
orientation \(\delta\) remains formal. The equation follows from
\(\beta^{P^2}=\beta^{(N+1)P-N}\) and its Q counterpart.
Its quadratic comparison is already implied, branch by branch, by the
existing linear hit. Thus it corrects an acquisition statement without
providing a new selector. The [standalone correction](quadratic-orientation.md)
supersedes that passage; the frozen earlier report is preserved.

The most concrete next target is a coverage theorem for a cheaply acquired
family of shift/colour tests, or a joint contraction of the filtered query
over its varying residue centres. A supplied-shift test alone, a known-node
Farey recurrence, and further phase preparation do not prove either one.

The Farey/skein sources remain those of the preceding packet. The further
search checked [Manin's quantum-theta functional equations](https://arxiv.org/abs/math/0307393)
and [Bostan–Yurkevich's q-holonomic algorithms](https://arxiv.org/abs/2012.08656).
This pass supplies no specialization of the former to the finite native
collision product and no improvement on the latter's existing recurrence
cost. Source scope and input hashes are recorded in [sources.json](sources.json).

All claims are paper derivations with independent reviews. There is no
numerical coverage campaign, new factoring implementation, Lean/public-asset
change, commit, or push. All 821 prior protected files, both existing
journal/agent prefixes, and 22 concurrent engineering files are preserved.
See [validation](review.json) and [manifest](manifest.json).

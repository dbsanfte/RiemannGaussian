
## Shared triangles fold to the universal factorial cover, 2026-10-24

**No new whole-query or factoring exponent.** This pass executed the
suggested cross-row sharing investigation. It found a denominator-free
gap cancellation with a complete coverage proof, but the completed family
contracts to the old integer factorial channel. The canonical query stays
soft m^1.5; this is not an improvement to the separate N^1/5 factoring
benchmark or the requested all-semiprime N^1/6 goal. Full bit/Lean
composition remains open.

Reports, exact-byte independent reviews and preservation validator:
`/tmp/semiprime-shared-triangles-20261024/`. The preceding recurrence
packet and all270 frozen entries were revalidated. No finite examples or
backend expansion were substituted for an all-input theorem.

For coprime a,m>1, write g=(a-1)(m-1)/2 and F=am-a-m=2g-1. If S(z) is
the product of z+r over positive gaps of <a,m>, Sylvester gap symmetry
partitions [0,F] into the gaps and their reflections. Hence, over Z,

    S(z) S(-z-F)=(-1)^g B_(2g)(z),
    B_d(z)=product_(0<=r<d)(z+r).

This is a product identity, with no inversion of a possibly hit-bearing
factor. Native opposite tags have the same a and
`c_(m-j)=-c_j+ma+m²*tau`, tau in {-2,-1,0}. For
`z_j(K)=c_j/m+mK`, the partner lift `K'=1-a-tau-K` realizes precisely
the reflected gap argument. Closing the public K interval under this
reflection costs only O(m) endpoint metadata over all row pairs.

For one opposite-tag pair, the resulting factorials have integer index
intervals [mK,mK+d-1]. For a>=3 they merge by exact zero support into
one interval of length O(m²). This recomputes the union product; it does
not divide out overlaps. For a=2 the one-index holes can be safely filled;
a=1 has an empty gap set and receives a separate ordinary progression.
The added physical leaves stay nonzero and have absolute value below N.

The completed family has a direct, stronger coverage statement: it covers
EVERY integer 1<=n<=m³ prime to m, up to sign. Indeed c_j modm=-N/j
permutes nonzero residues, opposite tags pair their signs, and each merged
progression includes all indices |t|<=m²+2m. The bound |c_j|<1.5m²
puts whichever of n,-n has the representative residue into that interval.
Thus P is covered independently of any quotient formula. This is a
universal integer cover, not an N-dependent arithmetic selector.

Shared factorial blocking actually acquires the O(m) progressions, each
of length O(m²), in soft(B+m³/B+m); B~m^1.5 gives the old bound.
Gcd localization is lawful on every retained physical leaf. More sharply,
clip to 16m²<|leaf|<=W=floor sqrt N. Each positive n in that interval
with m not dividing n appears exactly once up to sign. The clipped norm
is exactly `(-1)^nu product_(16m²<n<=W,m∤n)n`, with nu acquired from
the interval endpoints. The short m-multiple correction is a certified
unit. This recovers the old factorial norm, not a smaller covered union.

Other executed sharing attempts have their full costs recorded. Common
binary factorials give soft(s+r) for r supplied arithmetic progressions
of length at most s, but the literal native Euclidean triangles emit
Theta(m²) such starts. Transposing gives common step m; reflection tiles
two triangles into a rectangle. Neither removes that target count.
Recent composition/MPE theorems examined take explicit points or
coefficient arrays and do not supply their compressed product for free;
composite modulus alone is not a valid exclusion of ring-general methods.

Reciprocal tags j*=[N/j]_m give inverse a-slopes and an exact leaf
transport. Every transported lift enters one normalizable class in the
partner row, but its lift range expands. The normalized leaf is the
ORIGINAL integer leaf, still O(m³), rather than an O(m²) integer known
to be below P and Q. The unit screen applies only to its verified smaller
submenu; a full original-menu sufficient condition is partner slope>=m/4.
The enlarged transported menu does not inherit that screen. A carry-sign
error in an early scratch version was corrected before the pinned PASS
review; the exact carry is `(b_j*j+(N-a_j*j²)/m)/m`.

These identities close the proposed reflection/reciprocal simplifications
at their actual costs. Reorganizing this completed linear-lift cover alone
has not produced new arithmetic selection. A further advance must either
accelerate its actual long scalar product, or retain additional native
information in the original q-recurrence while acquiring its endpoint.
Small label orbits, shorter metadata and formal quotient cancellation do
not establish that operation. The full sixth-rate objective stays active.

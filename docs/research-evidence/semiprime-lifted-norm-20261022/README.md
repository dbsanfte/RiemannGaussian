# Lifted norm cancellation and a complete pair screen

22 October 2026. The retained quadratic colour has an additional exact
integer consequence: all native rows supply short descriptions of
v_j²-m³z_j=4a_jN. This packet acquires every useful singleton m*z_j square
relation or two-row positive-integer-square-product relation in that
supplied family in soft O(m) bit work. It also
proves that negative equal-squareclass rows with different rational
invariants v_j²/a_j necessarily yield proper factors, for m>=17. Their
local square-root signs need no additional assumption.

**The screen does not give uniform coverage.** A subsequent counting
argument proves that most balanced semiprimes in a broad fixed-modulus
window have no useful singleton or pair of this kind, even among inputs
admitting the prepared order promises. This does not settle the literal
least-prime modulus selector or adaptive choices. No theorem here forces
a useful relation for every input of the actual algorithm. The missing
whole-input acquisition theorem and complete Lean bit-complexity proof
remain open.
The covered long-product query still costs soft O(J+sqrt(JL)); the
simultaneous soft-O(m) H-value interface from the
[previous packet](../semiprime-colour-retention-20261022/README.md)
remains a separate sufficient constructive target. No Lean source,
implementation, success campaign, commit or push is part of this packet.

## Exact information extracted from the colour

Retain N=P Q with distinct odd primes, an odd public prime m coprime to N,
the original canonical nonzero tags j, and the paid large-factor branch
P,Q>16m². The native data satisfy

    m²c-jmb+j²a=N,  0<a<m,
    ell=mb-2aj,  Delta=b²-4ac,
    kappa=-Delta/(4aj) mod m,  0<=kappa<m.

Put M=m³ and v=ell-m²kappa. Then

    ell²-4aN=m²Delta,
    v²-4aN=m²(Delta-2ell*kappa+m²kappa²).

The last bracket is zero modulo m, since ell=-2aj modulo m and
Delta+4aj*kappa=0 modulo m. Consequently

    z=(v²-4aN)/M

is an EXACT integer. All O(m) descriptors have O(log N) bits and are
acquired in soft O(m) work. The native bounds give |v|<=m³+3m² and
|z|=O(m⁴) when N<=m⁶. Also m does not divide v. As
N>256m⁴, one has 0<|v|<N; a nonunit gcd(v,N) is therefore a proper
factor. On the remaining branch z is nonzero and a unit modulo N, because

    v²=M z modulo N.

The root v modulo the PUBLIC modulus m³ is not an acquired residue of a
hidden factor or an approximation to its integer trace. The
[relation report](reports/lifted-norm-consumer.md) and two independent
[cost](reviews/all-pairs-review.md) and
[arithmetic](reviews/all-pairs-arithmetic-review.md) reviews make that
distinction explicit.

## All square-product pairs are acquired without a matrix

Acquire a pairwise-coprime integer base B and sparse exponent
decompositions of the distinct absolute norm values:

    |z_j|=product_(b in B) b^(e_jb).

Retain signs and row pointers when deduplicating. Bernstein's
[coprime-base algorithm](https://cr.yp.to/lineartime/dcba-20040404.pdf),
Algorithms 18.1 and 21.2 with Theorems 18.2 and 21.3, supplies BOTH the
base and all these decompositions at soft total-input-bit cost. Prime
factorization of z_j is not needed. The independent review checks the
explicit logarithmic bounds, rather than replacing a general
input-size-to-the-1+o(1) bound by soft-linear notation without justification.

Test which base elements are integer squares. Give each row the signature
consisting of its sign and the IDs of nonsquare base elements occurring
to odd exponent. Pairwise coprimality proves exactly:

    signatures agree iff z_i*z_j is a positive integer square.

A nonsquare base element may have internal square factors; it still has
an odd prime valuation unavailable in any other base element. Thus the
test does not require the base to be squarefree. Total sparse incidence
size is O(sum_j log|z_j|), so deterministic grouping is soft O(m).

For each class form D from its odd nonsquare base elements and acquire
the positive exact integers s_j with

    z_j=sigma*D*s_j²,  r_j=v_j/s_j modulo N.

D need not be squarefree. It divides each class member, so all displayed
integers have O(log N) bits. The s_j are units, and every r_j satisfies
r_j²=M*sigma*D modulo N. Compare each r_j with one representative r_0
using gcd(r_j-r_0,N) and gcd(r_j+r_0,N).

These O(m) comparisons are COMPLETE for all pairs: if none returns a
proper factor, every r_j is globally r_0 or -r_0, and every pair is
globally equal up to sign. Conversely any useful pair forces a useful
representative comparison. This is a proof of completeness, not a
random-representative heuristic. Saturated comparisons are handled as
trivial global signs. No m-by-m table or general binary nullspace is used.

## Negative square classes have a public nontriviality criterion

Suppose two class members have negative norms. Write

    z_i=-D*s_i², z_j=-D*s_j², T=M D.

Their EXACT integer relations give

    v_i²+T*s_i²=4a_iN,  v_j²+T*s_j²=4a_jN.

For A_plus=v_i*s_j+v_j*s_i and A_minus=v_i*s_j-v_j*s_i,

    16a_i*a_j*N²-T*A_plus²=(v_i*v_j-T*s_i*s_j)²,
    16a_i*a_j*N²-T*A_minus²=(v_i*v_j+T*s_i*s_j)².

Since a_i,a_j<m and D>=1, both A values have square less than
(16/m)*N². For m>=17 this proves |A_plus|,|A_minus|<N without a balance
assumption. Further,

    A_plus*A_minus=4N*(a_i*s_j²-a_j*s_i²),
    4N*(a_i*v_j²-a_j*v_i²)
      =T*(v_j²*s_i²-v_i²*s_j²).

Thus the PUBLIC integer condition

    a_i*v_j² != a_j*v_i²

is equivalent to both A values being nonzero. N divides their product,
neither can contain all of N, and no hidden prime can divide both because
2v_i*s_j and 2v_j*s_i are units. Hence their two gcds are the two proper
complementary factors. If the condition fails, one A is zero and the other
is a unit; that pair is provably trivial.

The [independent integer proof](reviews/negative-pair-size-review.md)
therefore removes the previous separate local-sign premise on this
branch. Within each acquired negative class it suffices to compare
v_j²/a_j with one representative, using cross multiplication. The
[initial existence question](reports/negative-pair-existence.md) was
whether the canonical family, or a fully paid extension, must have one
negative square class containing two different such rational invariants.
The counting result below now rules out the uniform version over arbitrary
admissible supplied moduli; it leaves the actual selector and adaptive
extensions open. The retained native promises
already discharge the lemma's threshold: m⁶>=N>256m⁴ implies m²>256,
hence m>=17. There is no additional small-modulus branch under these
simultaneous promises.

## Positive singleton relations are also sufficient

If z=m*s² with s>0, put w=m²s. Then

    (v-w)(v+w)=4aN>0.

So 0<w<|v|, and both absolute factors lie strictly between zero and
2|v|<N in the native large branch. Since N divides their product, both
gcds with N are proper factors. This uses the integer size bound and needs
no extra Jacobi mismatch. Acquisition is just exact division and integer
square-root testing for every row.

Equivalently append one explicit sentinel (v_*,z_*,a_*)=(m²,m,0).
It satisfies v_*²=M*z_* and is a unit; its square-product pairs are exactly
the native singleton cases. It is not claimed to be a canonical row.
The general pair controller on this augmented list covers ALL singleton
and two-row square dependencies in the same soft-O(m) budget. See the
[singleton and character proof](reports/singleton-and-character.md).

This proof also checks the public character information. Every native
unit norm has Jacobi(z_j,N)=Jacobi(m,N), so these values do not separate
rows. A Jacobi mismatch of normalized roots is sufficient for useful
separation only with the stated Jacobi(-1,N)=1 guard; it is a subcase of
the complete gcd test, not an existence theorem.

## A uniform pair-existence claim fails for fixed admissible moduli

The [counting proof](reports/fixed-modulus-density.md) fixes a public prime
m and varies balanced semiprimes N in a constant-width box inside
[c*m⁶,m⁶], for fixed 0<c<1. Holding N_0=N modulo M=m³ fixed also fixes
all a_j and v_j. The norms are affine functions of the higher digit t:

    N=N_0+M*t,  z_j=Z0_j-4a_j*t.

A pair with z_i*z_j=W² gives

    X²-a_i*a_j*Y²=C²,
    X=8a_i*a_j*t-(a_j*Z0_i+a_i*Z0_j),
    Y=2W, C=a_j*Z0_i-a_i*Z0_j.

Here |X|=O(m⁵) and |C|=O(m⁴). When C=0 the normalized roots are
globally proportional, so the pair is trivial after the unit screen.
For C!=0, the [uniform Pell count](reports/pell-count.md) bounds the
number of possible t by tau(C²)*O(log m)=m^{o(1)}. The proof works in
the maximal quadratic order: at most tau(C²) integral ideals have that
norm, and successive same-sign generators differ by a norm-one unit
at least (3+sqrt(5))/2. Polynomial height leaves only O(log m)
generators per ideal. Square coefficients use ordinary divisor pairs.
Imprimitive solutions and varying discriminants are included. This is a
counting proof, not an efficient Pell-solving algorithm; m^{o(1)} is not
silently called polylogarithmic.

There are O(m³) residues and O(m²) pairs. Hence only m^{5+o(1)} integer
inputs in the box can have a useful pair. All initial gcd(v,N) successes
contribute O(m⁴), and all singleton-square cases contribute O(m³).
These branches are included, not discarded. The box contains
Omega(m⁶/log²m) distinct balanced semiprimes. Thus the proportion on
which this fixed-modulus singleton/pair consumer succeeds tends to zero.

The [prepared-order addendum](reports/prepared-order-density-addendum.md)
retains Omega(m⁶/log²m) examples admitting ALL relevant scalar order
promises. It restricts to P,Q=3 modulo 4 with coprime half-orders, and
excludes P or Q=1 modulo m. Fixed-modulus PNT and Brun--Titchmarsh pay the
density argument; the sum of small common-prime probabilities is bounded
by pi²/24<1, with uniform tails. Local odd-subgroup generators and CRT
then give existence of gamma with coprime odd orders >16m², unchanged
under q=gamma^(m²), and global order >256m⁴. It does not claim an
algorithm for acquiring that gamma from N. The analytic input statements
are recorded in [Lenstra--Pomerance, section 11](https://math.dartmouth.edu/~carlp/aks240817.pdf).

The [independent density review](reviews/density-review.md) checks the
success branches, prime counts and prepared-order refinement. This is
strictly a fixed-admissible-modulus consumer limitation. The actual
least-prime selector has the narrower bin
(previousprime(m)⁶,m⁶]; the argument does not transfer to that bin.
It also does not show that earlier preparation would fail, exclude an
adaptive modulus menu or higher dependencies, or bound a different
factoring algorithm. In particular it is not a reason to abandon the
shared-H query, whose native collision coverage is already proved.

## What the other cancellations do, and what remains

The [antipodal calculation](reports/antipodal-shared-blocks.md) pays all
bounded carries and exposes geometrically related paired H targets. The
[finite character calculation](reports/finite-character-products.md)
reduces the two H palettes to one when m=3 modulo 4, with paid endpoint
recovery. These constant-factor reductions leave the dominant evaluator
cost unchanged. The [endpoint jets](reports/endpoint-jet-interface.md)
are acquired in soft O(m), using the earlier q-integration mechanism;
their truncated coefficients do not give H at native nonzero unit points.
The root-of-unity and infinite-product literature audits state the exact
specializations missing from that proposed shortcut.

[Bounded public twists](reports/bounded-twists.md) v->v+tM and
z->z+2tv+t²M preserve the norm relation and fit the budget for a
polylogarithmic supplied set of polynomial-size t. A rational conic
parametrization that forces matching square classes, however, produces
only the globally opposite normalized root on its unit-denominator branch.
The [higher-cancellation audit](reports/higher-cancellation.md) proves
zz'=(z+uv)²-4aNu² for antipodal carries. It also classifies literal fixed
subset square identities valid for every higher input digit: those
identities give globally trivial roots. These are precise statements
about those constructions, not lower bounds for adaptive integer relations
or for character methods generally.

The [small smooth-base analysis](reports/small-smooth-base-consumer.md)
is retained only as a conditional side investigation; it proves neither
enough smooth relations nor useful dependencies. It is not evidence for
the all-input goal and is not the next implementation task.

A separate [rational-invariant screen](reports/rational-invariant-screen.md)
acquires all one-sided local collisions among v_j²/a_j in soft O(m),
using a monic root polynomial, its derivative values, public deduplication
and one selected product-tree descent. This uses no square-class
assumption. No identity was found forcing such a collision from the
covered long query, or computing H on the screen's no-collision branch.
It is retained as a precise conditional interface, not an acquisition
solution for the original query.

The constructive advance is a paid complete singleton/pair screen and an
arithmetic nontriviality theorem for negative equal-squareclass rows.
The subsequent count prevents using these facts as a uniform relation
existence claim over arbitrary admissible moduli. A different arithmetic
input, a selector-specific theorem, or a sufficient soft-m observable
would be needed to complete this route. The original shared-H query
already has a coverage and recovery proof and still needs its fast
simultaneous evaluator. That remains the central constructive target;
the full sixth-rate algorithm and Lean proof remain unfinished.

Reports and reviews are copied verbatim; archive-provenance.json maps the
historical scratch paths. source-pins.json fingerprints inspected primary
papers, without copying them into the repository. validation.json records
the proof reviews and archive checks. manifest.json freezes this packet;
the three earlier twist/colour packets are unchanged. The
[consolidated review](reviews/consolidated-review.md) independently checks
the acquisition costs, nontriviality identities and native threshold;
the later density review covers the subsequent counting argument.

# Colour sharing: an explicit common-character query

26 October 2026. **The complete query rate is unchanged.** This pass
constructs an actual shared-coordinate representation of the colour
queries, including their finite domains and clock shifts. It tests
colour exchange and boundary coverage as scalar algorithms. The full
guaranteed deterministic classical soft O(N^(1/6)) factoring goal
remains active and unproved.

With k of order N^(1/6), the retained original query costs
soft O(k^(5/4)). The new Cartesian-family completions still cost
soft O(k^2). Neither rate is claimed to be the best general factoring
algorithm. A representation or an initialized descriptor is not counted
as the desired soft-k whole-family scalar acquisition.

## An acquired common-character basis

The prior exact phase image is G Z/H, where

    H=k^2, G=gcd(j-1,k)^2, L=H/G.

For every colour, explicit Bezout matrices give a unimodular basis
whose two native generator exponents are

    G+H*f, H*c.

Thus colours in the same G-class share the two scalar directions
beta^G and q; there are only O(log k) possible G-classes. The construction and all integer lifts cost polylog N
per cell, hence soft k across the family. It also gives an explicit
isomorphism between equal-G colour lattices that preserves the native
character modulo H. Its ambient matrix can be rational while mapping
the supplied lattice integrally; it is not asserted to be a DAHA operator.

The actual Gauss-grid query is transported exactly. If z is its
original coefficient difference and n=P_j*z its new integer coordinate,
the normalized factors are

    q^[h-F_j*n1-C_j^clock*n2]-(beta^G)^n1,
    |z1|<A, |z2|<B, z!=0, h=0..4k.

The acquired F_j and C_j^clock include the difference between the
canonical phases on the two bases. Dropping that correction would
change the query. The transformed finite parallelogram and omitted
origin are retained, so every original nonliteral certificate survives.

We executed slicing in the common q direction. For each attained n1,
the allowed n2 form an integer interval, possibly split by the origin.
Its clock intervals merge exactly when adjacent intervals overlap or
touch, in particular when |C_j^clock|<=4k+1. Their source labels remain
available for recovery. Enumerating the actual slices still acquires
soft k^2 incidences; a huge coordinate range is never scanned. The
completed scalar bound remains soft k^2. See [construction and paid
readout](common-character.md) and [review](common-character-review.md).

This is a concrete common-coordinate input for the next collective
algorithm. The common beta^G direction was already known; the new work
is its explicit unimodular basis, actual finite-domain transport, and
executed interval-union readout.

## What the colour symmetries really preserve

The involution j -> N/j permits retaining one colour from each orbit
if the public factor-size scales cover both orientations. Either P or
Q then supplies the guaranteed nonunit. The enlarged scale range is
[8H,N/(8H)]. It halves the number of colour families, but approximately
doubles the logarithmic scale range, so it does not establish a net
factor-two saving in total cell work. All leaves remain recoverable;
their enlarged labels have O(log N) bits.

The sign change j -> -j needs the signed baseline

    -a-bN+lambda_(-j)=-E_j+H*epsilon.

Its character is -chi_j and has the same phase index. Keeping the
ordinary baseline at -j would be a different arithmetic query. Thus
the sign fold does not turn high-index colours into the apparently
cheaper ordinary -j states. See [symmetry proof](colour-symmetry.md)
and [review](colour-symmetry-review.md).

## Literature specializations and boundary coverage were tested

[Cherednik's DAHA colour exchange](https://arxiv.org/abs/1406.3959),
Theorem 1.2(ii), specializes in A1 to a weight resonance pairing j
and k-j at a specified parameter. An actual admitted row shows that
the corresponding native nodes have a unit difference. The source
equality therefore does not directly identify these native leaf inputs.
This leaves transformed whole-product identities open.

We also derived the exact lattice and character congruences required
by an ambient integer slope operator. For an ordinary Dehn shear,
literal q-covariance forces the same arithmetic colour and a shear
step divisible by H/gcd(j-1,k). These conditions are for that specified
pointwise action; the common-character construction above uses a broader
lattice isomorphism. See [specialization](colour-recurrence.md) and
[review](colour-recurrence-review.md).

For the cheap corner screen, a useful true-cell hit must satisfy the
integer equation r*I_u+s*I_w=h, 0<=h<=4k. The local-order guard rules
out a hidden alias in that range. Equivalently it satisfies an acquired
quadratic equation in the unknown factor. The existing coverage proof
places a hit somewhere in the interior difference box; it does not
force one of the few corners. Homothetic scaling preserves its ray
and scales h, so it supplies no such selection theorem.

Both complete boundary alternatives were charged: generator strings
with the old O(k^(3/2)) clock recover the old soft k^(5/4) cost; every
interior start with the short clock costs soft k^2. The former is prior
Gauss coverage, not a new rate. See [boundary analysis](boundary-cover.md)
and [review](boundary-cover-review.md).

The remaining target is a soft-k scalar/nonunit-prefix algorithm for
the actual collective slice domains, or a smaller uniformly covered
family. All factor branches include at most one terminating
T_ext=soft N^(31/192). The full bit-complexity theorem and eventual
Lean verification remain open.

Validation is independent symbolic paper review, not kernel checking.
All 861 prior protected files, both document prefixes and 23 concurrent
files are preserved. No numerical campaign, new factoring implementation,
Lean/public-asset change, commit or push was performed. See
[sources](sources.json), [validation](review.json), and
[manifest](manifest.json).

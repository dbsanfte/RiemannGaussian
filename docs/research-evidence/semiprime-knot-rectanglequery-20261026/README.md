# Rectangle acquisition: a carry-free query and the native phase index

26 October 2026. **The complete query bound has not improved.** This
continuation simplifies the new uniformly covered family to a finite
Cartesian product with no per-point phase carry, executes its scalar
evaluation, and proves why a proposed small cyclic closure cannot apply.
The full guaranteed deterministic classical soft O(N^(1/6)) factoring
goal remains active and unproved, including acquisition, recovery, full
bit complexity and eventual formal verification.

At k of order N^(1/6), the retained original route still has complete
query cost soft O(k^(5/4)). The new explicit completions below cost
soft O(k^2), so they are research alternatives rather than improvements
to that route. Neither is claimed to be the best general factoring
algorithm.

## A complete Cartesian query without phase carries

For each unit colour j and a public dyadic factor-size scale p0, acquire
an exact weighted Gauss basis u,w of the stationary lattice Lambda_j.
Let ell1,ell2 be its lengths and choose

    A=ceil(2k*sqrt(N)/ell1), B=ceil(2k*sqrt(N)/ell2).

The weighted covolume is kN, and A*B is of order k. Acquire the two
generator labels E_u,E_w and units X=beta^E_u, Y=beta^E_w. The nodes
X^r Y^s, 0<=r<A,0<=s<B, now use their unwrapped generator phases.
There is no canonical carry to compute for every grid point.

At the true colour and scale, their integer stationary indices span
less than 8*sqrt(2)*k^2+4k. Pigeonholing gives a collision at some
shift h between 0 and 4k. A public coordinate-span filter excludes
every literal comparison while preserving a guaranteed cell. Pair
multiplicities can then be removed exactly, leaving the predicate

    product_(retained cells) product_(h=0..4k)
      product_(|r|<A,|s|<B,(r,s)!=(0,0))
                       (q^h-X^r Y^s).

This product is guaranteed NONUNIT at the smaller prime; a global-zero
claim at both primes is unnecessary and is not made. Every leaf has a
nonzero short integer exponent gap and the existing factor decoder.
The origin line is omitted directly, before specialization.

Descriptions and generator values cost soft O(k) for the whole family.
The represented difference rows still have soft O(k^2) incidences. Thus
the construction removes a complication from the actual target input;
it does not pay for the collective scalar. See [proof](sparse-projection.md)
and [independent review](sparse-projection-review.md).

## A simpler difference overset, and its completed cost

The preceding rectangle pair query also admits a direct canonical-row
version. A pair's canonical phase difference changes its clock index
by only zero or one. All pairs can therefore be overcovered by O(k)
lattice differences per cell, with clock 0..6k+1.

The guaranteed close pair cannot have either coordinate difference
zero. Removing axis differences makes every added comparison legally
recoverable and lets this particular overset discard the old cell
filter altogether. Transposes remain safe in this version and give
global-zero coverage. See [derivation and algorithm](difference-query.md)
and [review](difference-query-review.md).

We executed the geometric-string alternative too. A safe common clock
envelope absorbs the varying carry; a shared polynomial kernel batches
all strings of one cell. Its initialized cost is soft O(k) per cell.
The Cartesian query has the same paid per-cell bound. Across the
soft-k cells both give soft O(k^2), including localization and at most
one terminating extractor. See [scalar accounting](recursive-products.md)
and [review](recursive-products-review.md).

## An exact arithmetic obstruction to small cyclic wraps

The native exponent character on Lambda_j, reduced modulo H=k^2, has
the exact image

    g^2 Z/H Z,  g=gcd(j-1,k),
    image size L_j=(k/g)^2.

Consequently any lattice basis with two literal q-periodic wrap lengths
C,D must satisfy L_j divides C*D. Exactly k/6 colours have g=2 and
L_j=k^2/4. For sufficiently large k, their new O(k)-point grids cannot
have those literal wraps at the proposed size. This rules out that replacement by a
small periodic grid, regardless of a change of lattice basis.

It does not rule out implicit evaluation, numerical modular aliases,
shared work between colours, or a different nonperiodic contraction.
The exact calculation and its limits are in [phase-index.md](phase-index.md)
and [its review](phase-index-review.md).

## The finite corner identity has been specialized and checked

The protected concurrent string-theory proposal suggested a rectangle
corner cancellation related to [Nekrasov's boundary observables](https://arxiv.org/html/1512.05388).
The new Cartesian input permits an exact finite specialization. The
omitted origin line must be retained in its accounting: at the requested
endpoint the naive cleared identity is identically 0=0, because the
translated auxiliary products introduce known literal zeros.

Formal regularization is valid, but leaves three other bulk product
values unacquired. The displayed boundary strings themselves can be
screened in soft O(k), after removing their known literal factors;
no theorem guarantees that this screen finds the useful collision.
This rejects the direct endpoint readout, not all recursive uses of
the identity. See [calculation](corner-query.md) and
[review](corner-query-review.md).

The next substantive step remains an actual joint scalar algorithm for
the finite Cartesian products, or another uniformly covered query that
fits soft O(k). Cell and shift prefixes with gcd/nonunit status suffice
for recovery; once localized, only one O(k)-point cell needs expansion.
Further formal descriptors or corner identities alone do not establish
that acquisition bound.

All results received symbolic paper review, not kernel verification.
All 847 prior protected files, both existing document prefixes and 23
concurrent files are preserved. No numerical campaign, factoring
implementation, Lean/public-asset change, commit or push was performed.
See [validation](review.json), [sources](sources.json) and
[manifest](manifest.json).

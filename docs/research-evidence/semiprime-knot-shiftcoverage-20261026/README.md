# Knot-inspired shift coverage and weighted rectangle products

26 October 2026. **No faster complete query or sixth-exponent factoring
algorithm is proved.** This continuation establishes two concrete
same-field coverage constructions, executes the proposed linear
cancellation route, and tests a continued-fraction product algorithm.
The full goal remains active: guaranteed deterministic classical
all-semiprime soft O(N^(1/6)) factorization, including acquisition and
the full bit-complexity argument.

For the existing route k is of order N^(1/6), J=soft O(k), and the
negative horizon m=O(k^(3/2)). Its complete query remains
soft O(J+sqrt(Jm)), or soft O(k^(5/4)) at that scale. The desired
soft O(k) acquisition has not been obtained. These are bounds for this
route, not a claim about the best factoring algorithms generally.

## Guaranteed row overlaps, with a valid decoder

For the original opposite-closed family, an original hit y=q^(-i)
forces a row-to-row overlap at the odd shift s=1+2i:

    q^(1+2i)*y = q/y = y_opposite.

The swapped witness forces the same shift at the other prime. Odd local
orders make this matched opposite comparison equivalent to the original
collision, up to a unit. All edges at shifts 3,5,...,2m+1 have nonzero
integer exponent gaps, so accidental extra overlaps are also recoverable.
This proves collective coverage; the matched subproduct is exactly the
old hard query up to units. See [proof](joint-shifts.md) and
[independent review](joint-shifts-review.md).

A separate congruence Dehn shear supplies a same-field edge from two
actually admitted b=1 rows for every public colour. Its forced shift is
the unknown factor quotient (P-j)/k, up to a public carry. Completing
that range gives an ordinary soft O(N^(1/4)) cover, with no improvement.
The short-shift failure is proved for this specific pair under an
explicit size condition, not for arbitrary knot-based algorithms.
See [mutation calculation](mutation-coverage.md) and
[review](normalization-mutation-review.md).

## A new uniform short-shift cover, using implicit rectangles

The strongest new coverage statement uses a larger auxiliary family.
For every public unit colour j and dyadic B<=k, set

    A=ceil(2k^2/B),
    S_(j,B)={(a,b): 0<=a<A, 0<=b<B, a*j^2=b*N mod k}.

Each rectangle has between k and 3k stationary points. At the true colour
and a public scale approximating k*sqrt(P/Q), their physical indices
all lie below 5k^2+1. Pigeonholing therefore forces a nonliteral
same-field edge at an integer shift 0<=s<=6k. This holds for every
prepared semiprime, including unbalanced factors. Its nonzero gap has
the inherited proper-gcd or saturated-annihilator decoder.

There are only soft O(k) rectangle descriptions, but soft O(k^2) point
incidences. Materializing them exceeds the target budget. A cheap public gcd filter removes cells with literal edges while
preserving the guaranteed cell. Transposing retained cells gives the
same shift at the other prime, so the collective product is globally
zero and every leaf is recoverable. Canonical phase carries and the
finite rectangle endpoints still belong to the query. Thus this theorem supplies coverage for a new implicit query;
it does not supply that query's cheap acquisition. See
[complete proof and cost ledger](dense-box-coverage.md) and
[independent review](dense-box-review.md).

## What the literature contributes

The continued-fraction connection suggests encoding lattice points by
Christoffel words. The [Berstel–Lauve–Reutenauer–Saliola text](https://webpages.math.luc.edu/~lauve/papers/wordsbook.pdf)
provides the relevant word factorizations. For the modular graph product

    P_theta(z;U,V)=product_(0<=a<k)(1-z*U^a*V^[a*theta mod k]),

we derive a finite quotient-block split. Combining it with the inherited
joint geometric-product evaluator gives an initialized scalar cost
soft O(tau+sqrt(k)), where tau is the minimum of theta, k-theta,
theta^(-1) mod k, and its complement. Reflection is performed by omitting
the transformed initial factor and restoring the original one; no
possibly zero boundary is divided out.

This is a paid algorithm for the specified unwrapped product. Its
materialized block starts still have quadratic total size across all
colours. The word representation alone does not compute products over
all prefixes. [Barvinok–Woods](https://arxiv.org/abs/math/0211146)
supplies short additive generating functions, which do not directly
evaluate this multiplicative scalar. See [derivation and source scope](christoffel-products.md)
and [review](christoffel-review.md).

The [staircase Macdonald/q-discriminant identity](https://arxiv.org/abs/0801.2443)
was already audited in the journal and is credited there. The new
supplied-shift certificate does allow its literal zeros to be removed
by taking a specified regularized coefficient, without dividing by
zero. That coefficient is still unacquired; this is an exact interface,
not a fast evaluation. See [normalization note](q-discriminant-literature.md).

## What cancellation does and what remains

Any integer combination of stationary rows that cancels both coefficient
coordinates also cancels the unknown factor direction. Its forced index
relation is then the identical global exponent relation: it supplies a
literal overlap, not useful new factor information. A noncancelling
combination with a supplied index s instead gives the directly testable
quadratic A*P^2+(L-Hs)*P+B*N=0. Acquiring a guaranteed candidate set for s
remains the arithmetic task. See [proof](lattice-shifts.md) and
[review](lattice-shifts-review.md).

The next constructive target is an actual joint evaluator: either for
the original long query or for the weighted rectangles with their short
shifts, canonical carries and public cell filter. Recursive
continued-fraction batching must pay the changing product normalizations;
short words, further trace identities, and finite successful examples
do not establish that bound.

Validation is symbolic paper review, not a Lean proof. All 832 prior
protected files, both existing document prefixes, and 22 concurrent
engineering files are preserved. No numerical campaign, factoring
implementation, Lean/public-asset change, commit, or push was performed.
See [review ledger](review.json), [sources](sources.json), and
[file manifest](manifest.json).

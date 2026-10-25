# Original-query continuation: exact status and recovery refinements

2026-10-22. **No new whole-family soft-O(m) collision query or sixth-rate
factorization theorem was obtained in this pass.** This checkpoint records
the attempted constructions, the useful recovery refinement, and a
provenance correction. It must not be counted as another acquisition win.

The target remains the restriction-stable original scalar product

    V(A,I) = product_(j in A, i in I) (beta^(N+delta_j) - q^i),
    q = beta^(m^2),  |A| <= m,  |I| = O(m^2).

The existing general cost is soft O(J+sqrt(J L)); the desired cost at the
native scale is soft O(m). A valid factor/support query can replace the
exact value, provided its restrictions and recovery are proved. The full
family's guaranteed nonunit status alone does not locate a factor.

## Findings that affect the next construction

**Centered lattice rows have a sound short-interval recovery rule.**
The public lattice is

    Lambda_j = {(A,K): A*j^2 = K*N mod m}.

Weighted Gauss reduction and a public integer centering shift give a
quotient interval of width

    O(1 + Delta/(m*T) + T*N*Delta^2/(m^2*P0^3)).

For a balanced window, P0 is comparable to m^3 and choosing
Delta comparable to m^(8/3) gives width O(m). This pays one window's
O(m)-sized explicit collision problem. Covering the balanced range by
these windows still acquires O(m^(4/3)) row/window targets. Optimizing
the complete explicit-list cost recovers the N^(1/5) tradeoff. No bound
reducing the total window work to soft O(m) was proved.

For a true covered row, suppose its integer quotient is sigma and a
full-N match supplies sigma' in the same short candidate interval. The
source identity implies q^(sigma-sigma')=1 modulo the hidden prime P.
An interval diameter below ord_P(q) forces sigma=sigma'; an exact
quadratic then recovers P. **The giant exponent need not be smaller than
the global order.** The same argument extends to fixed-degree relations
after checking that the recovery polynomial is nonzero. Reusing targets
across windows must retain bounded intervals and their witnesses; a
match in an unrelated distant window cannot justify discarding a true
target.

Reports: [lattice source](reports/lattice-route.md),
[public centered construction](reports/quotient-centering.md),
[reuse and saturated recovery](reports/shared-centering-recovery.md),
[higher-degree geometry and recovery](reports/higher-degree-quotient.md).
The projected higher-degree lattice can be small while its integer lift
is large. Its determinant mean is not a proved bound on the actual
integer quotient. This is a limitation of the inspected guarantee, not
an impossibility theorem for higher-degree methods.

**Squaring preserves exactly the original collision support, but has
not shortened either query dimension.** Odd local orders make all
additional factors x_j+q^i units. Consequently replacing every root by
its square retains the same row/seed hits. A degree-J resultant
deformation needs only J+1 deformation coefficients, but its direction
still contains the unacquired length-L geometric factorial. Reversing
the resultant exchanges that cost for deformation degree L.

The sparse norm's interpolation cap also remains valid for a larger
dyadic ambient rank M: for prefix h and direction degree L_U at most m,
the exponent span is at most 4h^2+14h+5+3L_U < 16m^2. The complexity
includes the log M levels. No embedding of the geometric seed interval
into this cyclic norm was found. See the [direct attempt](reports/direct-product.md)
and [squaring/prefix analysis](reports/squaring-query-prefix.md).

**The inspected Cauchy determinant shortcut erases the desired support.**
For P(T)=product_r(T-z_r), clearing a square Cauchy matrix gives

    det[product_(s != r)(x_j-z_s)] = sign * Delta(x) * Delta(z).

The right side is a unit under the prepared within-set separation
promises, even at a cross collision. Long shifted-factorial determinant
variants keep the original unpaid product as a row normalization.
This disproves that particular denominator-clearing replacement; it
does not rule out other determinant algorithms. See the
[determinant report](reports/q-cauchy-determinant.md), using
[Chu--Wang--Zhang, Theorem 1](https://www.scielo.cl/pdf/cubo/v12n3/art01.pdf).

## Provenance correction: the order/root family was already paid

Smooth-order removal, factor recovery on collapse, and shared
outside-product roots were already recorded in the
[October 16 constructive-frontier index](../semiprime-acquisition-checkpoint-20261016/sources/constructive-frontier-index.json).
The prime/semiprime shape of the smaller rough order was already proved
in the October 2 work. This pass revalidated their compatibility with
the newer unconditional prepared-base contract. It did not discover a
new solution of the retained rough-order branch.

The [independent review](reports/order-cleaning-independent-review.md)
checks the total bit cost, saturated quotient-exponent tree, valuation
margin after division by a small index, and uniqueness inside the rough
subgroup. The archived [cleaning](reports/rough-order-cleaning.md),
[shared roots](reports/shared-coindex-roots.md), and
[optional high-power normalization](reports/strong-order-route.md)
reports carry that correction. All candidate small-index roots exist
on both hidden components; acquiring them does not identify the true
coindex or supply the other roots in the full fields.

## Review and next obligation

The [root review](root-review.md) records the algebraic checks and their
scope. Eleven reports are archived with hashes and source paths. The
169 preceding frozen manifest entries are preserved. No examples,
new Lean backend, factor-engine build, or timing claim is used as
evidence of a better rate.

The next advance still needs a charged shared contraction of the
actual rows and long geometric interval, or an independently proved
all-input factor algorithm. Neither one paid norm nor one paid factor
window supplies that contraction. The sixth-rate goal remains active
and unproved.

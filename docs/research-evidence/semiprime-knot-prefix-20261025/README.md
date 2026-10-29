# Half-center cancellation and the one-sided collision query

Research of 25 October 2026, archived on 26 October after the interrupted
turn resumed. The previous turn made progress: it derived and independently
reviewed the uniform reductions below and executed their small exact
checks. Archiving preserves that work; it does not supply the still-missing
fast prefix algorithm.

The complete native query can be reduced to **one half of the seed
interval**, with a one-sided final scan. A correctly recentered ordinary
Alexander representation also needs only half as many trace nodes. These
are constant-factor improvements across the whole allowed family. The
paid bound remains soft O(k^(5/4)); the guaranteed sixth-exponent objective
and complete executable/Lean bit-complexity proof remain open.

## Exact cancellation and what it saves

The original catalogue is not inverse closed. For nonzero uncentered
lambda, opposite labels have E'=H-E, so their points are x and q/x.
The only lambda=0 rows are the four axes: H|4abN would otherwise force
k^2/4 to divide a nonzero |ab|<k, impossible on the hard branch k>16.
Their complete query costs soft O(sqrt(M)); either it factors N, or its
unit certificate permits removing these rows at every prefix.

The actual public deletion and complete-swap pruning preserve opposite
closure. After the existing central screen, each remaining pair has both
x-1 and x-q certified units. Acquire

    G_h(W)=prod_pairs(W-x-q/x),
    D(t)=G_h(t+q/t)/G_h(1+q).

This polynomial has degree J/2 for J remaining original rows, including
duplicate numerical nodes. D(q/t)=D(t) and D(1)=D(q)=1. If Delta_old is
the earlier centered Alexander normalization, then exactly

    Delta_old(t)=D(t)D(qt).

Writing A_m=prod_(i=1)^m Delta_old(q^i) and
B_m=prod_(i=2)^(m+1)D(q^i), we get A_m=B_m*B_(m-1). Hence A_m and B_m
have the same nonunit predicate; modulo the actual squarefree semiprime,
they also have the same zero predicate. Interior collision factors have
been retained once, not divided out. The scalar values generally differ.

For F(t)=prod_remaining_rows(t-x_j), this further gives

    B_m=q^[(J/2)*m*(m+1)/2] / F(1)^m
           *prod_(i=1)^m F(q^-i).

The prefactor is a known unit. We therefore need only the negative seed
prefix. At its first zero, the new F(q^-m) must be a nonunit because a unit
cannot annihilate the preceding nonzero product. Scan only x_j-q^-m over
the remaining original rows. Saturated leaves retain the original nonzero
integer exponent E_j+Hm and the existing extractor applies. Earlier
prefixes may be nonzero zero divisors; no unit assumption is made for them.

The established geometric block algorithm now uses m seed positions
instead of about 2m, with cost soft O(J+d+Jm/d). Optimizing d still gives
soft O(J+sqrt(Jm)). No additive soft O(J+sqrt(m)) bound is proved.

## A smaller ordinary knot representation

Acquire eta=beta^(H/2), so eta^2=q. Screen x-eta. Proper gcds factor, and
global equality with nonzero E-H/2 feeds the licensed extractor. Exact
integer E=H/2 is a separate harmless horizontal-axis pair: all its original
signed clock differences are units under the odd local-order promise, so
it can be deleted. Do not use the zero exponent as an annihilator.

Now v=x/eta has v-1 a unit and the opposite is v^-1. The ordinary Alexander
normalization from these paired trace nodes has a Seifert matrix of size
2L, where L is half the remaining row count. Its coefficients and at most
4L-1 nonzeros are acquired in soft O(J). Its values on
eta^3,eta^5,...,eta^(2m+1) give the same prefix predicate up to a known
unit. This reduces representation size; the long odd-stride product
remains the open operation.

The [full algorithm and proof](halfcenter-algorithm.md) includes every
special branch and cost. The [independent review](halfcenter-review.md)
checks the native pruning, exact normalization, squarefree condition,
and one-sided recovery. The [row investigation](row-cancellation.md)
also tracks the changed finite hypergeometric parameters. Its q-Euler
identity retains the boundary, and direct decimation still grows the
parameter lists.

## Other concrete knot leads tested

- [Satellite and surgery construction](satellite-transfer.md): Cimasoni's
  exact splice identity represents the full prefix by an actual knotted
  keychain, with a certified unit boundary factor. Its explicit description
  still has m leaves. Morton's four-component twist formula really is
  evaluable in O(log m), but produces a geometric sum and endpoint terms.
  Harper's colored cabling collapses to one aggregate-color evaluation,
  which differs from the required product of evaluations.
- [Loop-rationality investigation](loop-rationality.md): a logarithmic
  residue gives a bounded local collision count and therefore another
  exact prefix-decision target. A direct rational antidifference is
  impossible because the occupied q-orbits have positive, nonzero total
  residues. This excludes that endpoint telescope, not all fast residue
  projections. MMR rationality supplies the already acquired inverse
  Alexander polynomial, with no cheap pole-selection theorem.

The cited primary papers, theorem locations, finite-ring hypotheses and
input costs are in the individual reports. The constructive next work is
a fast contraction of the one-sided or odd-stride prefix, using the native
arithmetic where necessary. More representation identities alone do not
meet the sixth-rate objective.

## Validation and preservation

[check_halfcenter.py](check_halfcenter.py) performs five small exact-ring
fixtures, 95 identity/predicate checks, and four one-sided recovery checks,
including mixed CRT witnesses and repeated roots. The
[captured result](halfcenter-validation.txt) passes. This is reference
arithmetic, not a fast oracle, coverage experiment, or scaling benchmark.

The earlier [literature](../semiprime-knot-literature-20261025/README.md),
[advancement](../semiprime-knot-advancement-20261025/README.md), and archived
recurrence packets remain unchanged. Source scratch paths in reports have
their historical counterparts under
`../semiprime-recurrence-checkpoint-20261025/evidence/` where applicable.
Only our reports and small checks are archived; external PDFs remain in
scratch. See [review.json](review.json) and [manifest.json](manifest.json).
No Lean/public assets, commit or push; concurrent engineering work is
preserved.

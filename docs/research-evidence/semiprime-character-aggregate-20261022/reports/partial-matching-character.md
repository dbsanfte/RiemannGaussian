# Partial-matching character matrix: exact graph simplification and its input charge

22 October2026. No newly acquired soft O(J+sqrt L) character moment or factor observable was found. The partial-matching premise yields an exact degree-two graph, bounded positive trace and explicit component determinants, but their data are collision degrees/adjacency rather than the already paid geometric moments. This report does not promote those unacquired entries to a new evaluator.

Read first: rh_transfer/report.md's existing character-deficit criterion; structured_matrix/report.md's paid geometric moments, Hankel/selected-coefficient audit and Pfaffian Schur complement; weighted-cauchy-continuation.md's exact Rogers/3phi2 reduction; and the current twist-palette packet. None of those unknown transforms is restated here as an acquired object. No new literature theorem or finite example is used.

## Exact support graph and a saturation caveat

Let x_j be integer-offset-deduplicated native targets and y_i=q^i,0<=i<L. Suppose target differences are units and L is less than both local q orders. At each hidden field, x_j=y_i defines a partial matching: a row hits at most one seed and a column hits at most one target. Let P and Q denote these two0/1 incidence matrices as proof-side INTEGER matrices; they are not acquired local field inputs. Let C be their entrywise intersection and

    B=P+Q−C.

This is the union mask retained by the normalized full quartic chord character. Its row and column degrees are at most2, and it has at most2J nonzero entries. A saturated edge in C is isolated: neither hidden matching can have another edge incident at either endpoint. Every other component is an alternating path or alternating even cycle, in addition to isolated vertices. This validates the graph simplification over the INTEGER mask, not a supplied hidden graph.

For normalized character matrix A, the full-phase proof gives exactly

    A=1_J 1_L^T−B.

This is an integer equality after dividing by the acquired unit row/column phase labels. It includes saturated collisions because their character is0, just as for single-local collisions. One must NOT replace B by P+Q: that would count a saturated edge twice.

## Exact low-degree relations actually supplied by matching

Over the integers,

    tr(B B^T)=sum_(j,i)B_(j,i)=D_union,
    1<=D_union<=2J

under the retained coverage promise. Per row, sum_i B_(j,i) is0,1 or2. Thus the useful deficit is only O(log J) bits, even though its argument has J L entries. This sharpens its output-size/precision ledger; it does not compute it. An approximation error strictly below1/2 would suffice after rounding, but no such approximation theorem is supplied for these native inputs.

The local matrices satisfy P P^T=diag(rowdegrees_P), Q Q^T=diag(rowdegrees_Q). Cross terms P Q^T and Q P^T encode the alternating paths/cycles. They do not vanish merely because EACH local matrix is a matching. After saturation isolation, B B^T is a diagonal row-degree matrix plus an adjacency matrix of a graph of maximum degree2 on the row vertices (a length-four alternating cycle may produce off-diagonal multiplicity2). In particular B need not have rank1, bounded rank, or bounded-degree characteristic polynomial independent of J.

At the character level,

    D_union=tr[(1_J1_L^T−A)(1_J1_L^T−A)^T].

Since A entries are0 or1, this is also J L−sum A_(j,i)². It is EXACTLY the old nonnegative character deficit in a Gram/trace notation. Computing it by the already paid geometric monomial moments would require an acquired map from those moments to A, which is absent. Multiplying A or B by a vector is not a supplied primitive.

## Component determinants are explicit, but require the hidden components

For the full bipartite adjacency matrix

    T_B=[[0,B],[B^T,0]],

one has det(I−z T_B)=det(I−z² B B^T), omitting the trivial isolated-vertex factors. The determinant factors across graph components. For a simple path on n vertices its factor p_n obeys

    p_0=p_1=1, p_n=p_(n−1)−z² p_(n−2).

For an even cycle on n>=4 vertices its factor is

    p_n−z² p_(n−2)−2 z^n.

These follow by the determinant expansion into disjoint edge transpositions plus the two oriented cycle permutations. Saturated isolated edges are just the path case n=2. The total nonisolated graph size is O(J), so IF component sizes or adjacency were supplied, all determinant factors could be constructed in soft O(J) work by ordinary recurrences/product trees. Their z² coefficient is−D_union and would immediately give the positive collision count.

But the input does NOT supply the component sizes, row degrees, or alternating partners. Ordinary target/seed power sums are not those graph descriptors. Thus the small determinant cannot be claimed paid from the original geometric descriptors. This is the precise input charge for this component calculation, not a generic lower bound for implicit graph methods.

## What is already paid and what would be genuinely new

The full row/column PHASE products of the nonlinear chord palette are acquired at soft O(J+sqrt L). They give the gauge of A, not its zero entries or a B-vector product. The geometric moments sum_i y_i^k for O(J) supplied k and the stronger selected-qbinomial coefficient stream are also already paid. The old weighted Cauchy identity expresses a rational collision detector with safe denominators, but its native-parameter batch remains uncomputed. Partial matching does not turn any of those acquired arrays into tr(B B^T) by an identity derived here.

A direct formal equality indicator over F_P would use1−(x−y)^(P−1); P is not known and is not replaced by N. A complete-period orthogonality sum over the hidden field/order would require a new input and an incorrect large clock. Neither is used to infer an acquired moment from the matching promise.

The graph perspective does remove potential unnecessary recovery requirements: any exact positive D_union, any nonzero acquired B-row moment, or an actually acquired nonconstant component determinant would select a row by a uniform restricted-target controller and then use the already paid unmasked scalar descent. But existence of a sparse graph does not supply those outputs. The old deficit/moment/Hankel criterion remains unimplemented; this report makes no claim that renaming it as a trace helps acquisition.

## Outcome

The rigorous new simplification checked here is the exact degree-two UNION graph, including isolated saturated edges and its explicit path/cycle determinant formulas. It gives an O(J)-size proof-side object and an O(log J)-bit sufficient trace. No construction from the public native descriptors to those graph invariants at soft O(J+sqrt L) was obtained. Therefore there is no acquisition advance or factoring-rate claim from this pass, and no new selected norm class is offered in its place.

Only this new scratch report was written. No repository edits, new agents, backend, finite success campaign, or hidden-field calls.

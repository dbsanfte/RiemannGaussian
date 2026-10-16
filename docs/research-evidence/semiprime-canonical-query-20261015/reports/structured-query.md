# Structured determinant and adaptive gcd follow-up

Research date 2026-10-15. No repository edits or builds. Goal: soft O(J+sqrt L) ring/nearlinear-bit acquisition in the balanced J~sqrt L regime, preserving ANY hidden-field collision. This report does not demand J*polylog L for all J and makes no universal complexity lower-bound claim.

## 1. Exact Cauchy identity and the collision-domain problem

Put x_j=Y_j and y_i=u q^i. The long product is S=prod_(j,i)(y_i-x_j). Whenever all cross differences are invertible, C_ji=1/(x_j-y_i) satisfies

    diag(x) C - C diag(y) = 1_J 1_L^T.

Thus it has displacement rank one. In the square J=L=n case,

    det C = [prod_(j<k)(x_k-x_j) prod_(i<l)(y_i-y_l)]
            / prod_(j,i)(x_j-y_i).

The signs shown agree with C_ji=1/(x_j-y_i). This identity gives a cross product from a Cauchy determinant only when the displayed denominators and normalization factors can be handled. It is rationally valid but is not a division-free collision query.

A particularly precise problem occurs BEFORE determinant computation. Over a hidden field, the displacement map A->diag(x)A-A diag(y) is entrywise multiplication by x_j-y_i. At a collision it is singular, and the generator equation with all-ones right side is inconsistent at that entry: 0*A_ji=1. Therefore the abstract rank-one displacement generator does not describe any Cauchy matrix on the desired yes-instance. Over Z/N, every requested inverse cross difference needs a gcd check; proper gcd solves factoring, gcd=N does not, and checking JL differences individually is over budget. Assuming existence of C is already assuming no collision in either field.

The rectangular matrix JxL has no determinant whose denominator simply consists of all JL factors. A JxJ minor uses J selected columns, hence covers J² selected residuals, not the complete interval. Completing the lists to square size L raises the matrix dimension to L. This is an interface/accounting statement, not a theorem ruling out a different low-dimensional determinantal identity.

## 2. Current 2026 structured solver checked directly

Khichane–Neiger, *Matrices with displacement structure: a deterministic approach for linear systems and nullspace bases*, arXiv:2603.02425, gives deterministic algorithms over an effective field for arbitrary rectangular m×n structured systems/nullspaces in soft O(alpha^(omega-1)(m+n)) field operations. The downloaded v1 PDF is dated March 4, 2026. Its Algorithm 5 explicitly requires **disjoint and repetition-free lists x,y** for the Cauchy-like input. It does not offer a succinct-list determinant oracle or a composite-ring factor-or-query theorem. Applied literally here, m=J,n=L,alpha=1 still charges soft O(J+L), plus the domain issue above. Primary: https://arxiv.org/pdf/2603.02425 ; https://arxiv.org/html/2603.02425 . Local PDF/text saved. The HTML currently displays a later manuscript date; use the saved PDF hash for the reviewed version.

This is a useful genuinely current deterministic theorem, but removing random generic rank profiles does not remove dimension or input-disjointness costs.

## 3. Displacement rank is not quasiseparable rank

When x rows and y columns are pairwise distinct and cross-disjoint over a field, every square submatrix of C has nonzero Cauchy determinant. Hence any r×r off-diagonal submatrix has rank r. A Cauchy matrix can have displacement rank one while its exact off-diagonal/quasiseparable ranks can grow as Theta(min(J,L)), subject to the available off-diagonal block sizes. The fact that x_j and y_i are gamma powers does not change this determinant identity. The actual family would need a separately proved repeated-node or special ordering relation to lower those ranks; no such relation is supplied merely by the common gamma base.

This observation does not assert that all actual rows are pairwise distinct in both hidden fields. If local repetitions occur, their handling itself must preserve possible factor information. It rules out conflating two different rank notions on the collision-free distinct-node branch.

## 4. A low-dimensional division-free norm matrix really exists

Let H(X)=X^J+h_(J-1)X^(J-1)+...+h_0, A=R[X]/H, and let C_H be multiplication by X in basis 1,X,...,X^(J-1). Then

    M_L = prod_(i<L)(C_H-u q^i I) = G_L(C_H),
    det M_L = Res(H,G_L) = (-1)^(JL) S.

This is a valid J×J division-free determinantal representation. Constant displacement rank is available too: write C_H=Z-h e_last^T, where Z is the subdiagonal shift and h=(h_0,...,h_(J-1))^T. Because C_H commutes with M_L,

    Z M_L - M_L Z
       = h e_last^T M_L - M_L h e_last^T,

whose rank is at most two over each hidden field. This identity is exact over R as a sum of two outer products.

The key information has not been acquired: the generators contain e_last^T M_L and M_L h, and the first column M_L e_0 is exactly the coefficient vector of G_L mod H. For every polynomial g of degree<J, the matrix g(C_H) has the same commuting/low-displacement property; knowing only that property does not identify g. Thus a constant-rank statement is fully compatible with an unresolved J-coefficient generator acquisition problem. The commutator displacement operator itself is singular (identity matrices lie in its kernel), so the displayed rank-two equation is not by itself a unique structured representation. Replacing it by a standard invertible displacement adds boundary data, which again includes unknown entries of M_L.

This is a more specific reason that “find a constant-displacement determinant” alone is insufficient. It leaves open an algorithm that evolves these generators cheaply by a genuine new q-difference identity. Naively multiplying L structured factors, each with J-scale state, costs too much; the known optimized block method gives soft O(J+sqrt(JL)).

## 5. Denominator clearing is correct but reacquires the answer

Define E_ji=G_L(x_j)/(x_j-y_i)=prod_(k!=i)(x_j-y_k). These are polynomials, so the matrix remains defined at collisions. Its displacement is

    diag(x) E-E diag(y) = g 1_L^T,
    g_j=G_L(x_j).

It therefore has a rank-one displacement description with a valid RHS at colliding entries, because then g_j=0 in that field. But the needed generator g consists exactly of the desired long products per target. Declaring this generator available circularly assumes the missing batch q-Pochhammer evaluation. A minor of E may be useful after those values exist; it supplies no cheap acquisition of them.

## 6. Adaptive gcd and rectangle subdivision

A proper gcd may stop the computation early, so exact-scalar complexity is not a universal bound on factor-or-query complexity. Still, the elementary adaptive subdivisions do not yield the target worst-case guarantee. A subrectangle of j targets and ell exponents costs soft O(j+sqrt(j ell)) by the verified evaluator. Partitioning J targets into K equal groups and processing every group yields the summed upper estimate soft O(J+sqrt(KJL)); subdividing a horizon into K blocks gives the analogous sqrt K growth in this direct accounting. This is not a matching lower bound, but it provides no improved guarantee. Early success can improve actual runtime, but a sole colliding target in the last processed group, or two hidden-field collisions that initially saturate a combined gcd, requires the unresolved acquisition/refinement costs to be charged.

This does not exclude adaptive algorithms with a different oracle, a new range-product data structure, or stronger source collision-density promises. It says that plain recursive use of the existing evaluator offers no proved soft O(J+sqrt L) worst-case theorem.

## 7. What arbitrary-target generality does and does not imply

A soft O(J+sqrt L) theorem would improve **this special rectangular resultant** Res(H,G_L), where H is arbitrary split degree J and G_L has geometric roots. It would also give fast batch geometric-orbit incidence and diagonal q-difference product evaluation. It does not immediately imply a faster general resultant of two arbitrary dense polynomials: replacing an arbitrary root list by q^i would require an unjustified representation/discrete-log step, and generic resultant inputs already carry L coefficients. No general-resultant hardness reduction is claimed here.

A useful sufficient next contract is: acquire a valid displacement generator plus boundary data for M_L=G_L(C_H), or decide its singularity separately in each hidden field with proper-factor refinement, in soft O(J+sqrt L) total cost. This targets the exact unresolved state while allowing richer representations, numerical q-squaring, and adaptive factor-or-query outcomes. No examined identity currently proves that contract.

## 8. Canonical-family strengthening from independent coverage input

The root/coverage investigation reports the following inherited native source theorem: for the original canonical seeds Y_j=gamma^(N+delta_j), j=1,...,m-1, q=gamma^(m²), and common interval length L=2m²+2, the rectangle contains a forced collision modulo the hidden prime p whenever p>=m² and N<=m^6. The source is `SemiprimeWideWrapCoverage.seed_index_bounds`; this report uses that coverage assertion as an external input and does not independently reconstruct it.

Conditional on that input, the Cauchy domain defect is present on **every canonical target instance**, not merely a possible yes-instance. For the colliding pair (j,i), the residual Y_j-q^i is zero modulo p and is therefore a nonunit in Z/N. Consequently the canonical displacement equation

    (Y_j-q^i) C_ji = 1

has no solution in Z/N: reducing modulo p would give 0=1. No matrix C exists over the base ring with the proposed all-ones rank-one generator. A standard Cauchy solver whose input promises disjoint point lists cannot be called on this canonical rectangle. A factor-aware front end that actually identifies a proper nonunit residual has already acquired the desired arithmetic certificate; obtaining it cheaply is the open query task rather than a free normalization step.

The full canonical coverage and global-leaf sum recovery are already compiled in SemiprimeSeedSumAcquisition.lean: common_seed_sum_exact and long_public_route_seed_batch_succeeds handle the padded range 2m²+2<=L<=4m². Although the earlier SemiprimePhaseSumRecovery theorem has a smaller signed z-range, this later native file already supplies the needed range. The independently supplied coverage report restates the known arithmetic mechanism and bounds; it is not a new range extension or new arithmetic advance. This removes a separate proper-factor-recovery ambiguity for the canonical long-branch query using existing compiled arithmetic. The distinct current contribution is the restriction-stable scalar-oracle bisection interface and the actual-instance Cauchy-domain obstruction. It does not alter the Cauchy inconsistency: a residual zero modulo N is also noninvertible and still makes the displayed equation impossible. Thus the clean rectangular acquisition problem can be retained without adding an artificial ragged-family prerequisite to its core oracle contract.


Coverage/recovery provenance used in section 8: `/tmp/semiprime-query-followup-20261015/coverage/first-current-coverage-and-recovery.md`, reviewed 2026-10-15. The canonical coverage and global-leaf recovery arithmetic are existing compiled results; no new recovery arithmetic or Lean endpoint is claimed.

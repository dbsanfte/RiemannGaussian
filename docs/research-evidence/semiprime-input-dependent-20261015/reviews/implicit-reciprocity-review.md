# Independent algebra/scope review: implicit q-Weyl, transforms and reciprocity

2026-10-15. Independent derivation of displayed algebra and scope. Fresh primary-literature attribution is being reviewed separately by another investigator; this review does not claim to verify those new papers' full bibliographic/theorem contents.

## q-Weyl boundary report

The companion convention C=Z-h e_last^T and D=diag(1,q,...,q^(J-1)) gives DC-qCD=(q^J I-D)h e_last^T exactly. This follows directly from DZ=qZD and e_last^T D=q^(J-1)e_last^T; no inversion or genericity is needed.

For T=(I-C)D, T^n e_0=P_n(C)e_0 is valid through n=J inclusive. Up to the preceding step the polynomial has degree below J, so diagonal scaling acts on the true polynomial before the first reduction. The remainder/quotient boundary correction (3) follows from P_(n+1)=(1-X)P_n(qX), and the first discrepancy (4) uses rem_H H(qX)=-(q^J I-D)h. Both signs check. The J=1 discrepancy a(1-a)(1-q) checks explicitly. The time-dependent recurrence (5) is exact because every polynomial in C commutes with C.

One wording correction was requested: over an arbitrary commutative ring with q not explicitly assumed a unit, the quotient degree is AT MOST n-J. Equality requires the usual unit-q/nonzero-ring assumption; q=0 is an elementary exception. This affects neither the exact boundary identity nor the actual unit-q setting.

The finite-horizon constant-linear-state proof is rigorous in K=Q(a,q). Dividing by nonzero u_n produces a polynomial R(z) of degree at most r with r+1 distinct roots q^n. Its basis polynomials have distinct degrees and nonzero leading coefficients, forcing all recurrence coefficients zero. A constant s-dimensional realization of all prefixes through L, with 2s<=L, contradicts its nonzero Cayley--Hamilton recurrence on n=0,...,s. Thus s>L/2 is valid for that specific generic rational-parameter prefix-realization model, even if the matrix is chosen for a fixed L.

The report correctly excludes horizon-only outputs, nonlinear or n-dependent state, moving carriers, actual finite-field numeric specializations and scalar identities with extra acquired data. No generic recurrence theorem is promoted to an actual-family lower bound. The determinant formula det(T^L)=H(1)^L q^(LJ(J-1)/2) is correct and differs from the desired q-product determinant.

## Transform interface

The sparse-moment generating function has unit constant denominator, so balanced rational-function assembly and truncated expansion work over the composite ring without inverse node differences. The soft O(J+K) arithmetic bound is legitimate for this explicit moment task. The reverse explicit-polynomial evaluation cost still pays its coefficient length L. The report correctly distinguishes a linear weighted sum of values from the nonlinear product needed for collision support.

One notation correction was requested: the condition 1-q^(k+1) being a unit does NOT make c_k invertible. The displayed q-binomial update should be written as c_(k+1)=-q^k(1-q^(L-k))(1-q^(k+1))^(-1)c_k, rather than c_(k+1)/c_k. For example at q of order R with L=R, c_1=0 while a later denominator can still be a unit. The intended update only needs the stated geometric denominator inversion; this is a notation/domain correction, not failure of the transform proposal.

The bounded q-stride shift identity, source low-digit fibers of size at most two, and resulting Omega(J) residue sectors are correct. They are properly separated from hidden-field orbit disjointness. The generic gamma-step numerator and denominator have no common root when q=gamma^d over Q(gamma), d>1: an equality would force 1+d(i-j)=0. Hence both reduced degrees are L in that generic rational model. The report explicitly allows finite-field numerical cancellations and does not claim an actual-source lower bound from this degree calculation.

The stride-d recurrence and complete d-sector distribution identity are exact. Completing a sparse J-sector mask to all d sectors genuinely changes the explicit task size. No claim that every possible implicit completion must pay that materialization cost is made.

## Cyclic reciprocity report

The phase extraction identity (1), finite reciprocal reversal (2), and full residue-class distribution (3) all check exactly, with inverses only of supplied units. In (1) the interval start moves by h_j while its length stays L; no known remote zero is imported into the original search interval.

On the actual retained family, prime local R>m makes q=gamma^(m^2) have the same order R and subgroup as gamma. Every normalized target lies in that subgroup, so its complete orbit product is 1-z^R=0. A nowhere-zero cyclic W satisfying W(qz)=c(1-z)W(z), with c nonzero, is impossible: multiplying recurrence ratios gives 1=c^R(1-z^R)=0. This applies to arbitrary functions on that actual finite orbit, not just rational functions, and remains true over extension fields. The report's obstruction is therefore actual-source and mathematically stronger than a generic rational-telescoping observation, but only for the specified globally invertible cyclic primitive.

The off-orbit necessary normalization c^R(1-z^R)=1 is correct. At the actual singular orbit, granting root extraction cannot repair it. Noncyclic paths, singular regularization, extra divisors and general scalar algorithms are expressly outside the obstruction. The remote j=1 zero has exponent E_1 divisible by m^2; its index is Theta(m^4), so the stated large-input separation from the native Theta(m^2) interval is correct.

No algebraic correction to the cyclic reciprocity report is requested. Primary-literature scope is left to the separate fresh-source review.

## Final reviewed artifact pins and disposition

The two minor wording/domain corrections above were applied and re-read. The final algebra/scope verdict is PASS on these exact bytes:

- implicit/q-weyl-boundary.md SHA256 ac4172ffe1e3f98748e6a9de26bfc9a020cc0e8a705ee56b1770ce506dd1f44c.
- implicit/transform-interface.md SHA256 5c8b4d56f2ee00e59b608fb1a15ae7baefee8af02acaba4655f5aa930c0505ae.
- reciprocity/cyclic-reciprocity-audit.md SHA256 48fb0580a1c90631215c7481ba8833637758ff15cf8c1d8f245cc3f6e067b3c1.

No substantive correction remains requested. The generic constant-state prefix obstruction is not an actual semiprime complexity lower bound. The cyclic nowhere-zero primitive obstruction does apply to the retained actual family, with the exact limited contract stated in that report. Neither result pays the core long-query acquisition.

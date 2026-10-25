# Rational mixture: exact telescoping residue and paid evaluator

24 October 2026. Scratch only. No soft-k query improvement is established.

Input: native acquired units y_i, arbitrary supplied weights omega_i, and q with both local orders >16H. The horizon h<16H is the actual shorter scalar horizon. Set

    P_h(X)=prod_(r<h)(1-q^r X)=sum c_n X^n,
    U(t)=sum_i omega_i/(1-y_i t)=sum_n mu_n t^n,
    K(X)=U(1/X).

The desired scalar is S=CT_(X=infinity)(P_h(X)K(X))=sum_n c_n mu_n. The numerator and constant-one denominator of U are acquired by weighted product trees in soft J, even with repeated y_i. No target separation or weight inversion is needed.

## Rational creative telescoping tested explicitly

The actual q-functional equation is

    (1-X)P_h(qX)=(1-q^h X)P_h(X).

Its adjoint under the constant-term pairing is

    T_h V=(1-q^h X)V(X)-(1-q^-1 X)V(q^-1 X).

For every rational V expanded at infinity, CT(P_h T_h V)=0. More strongly, with W=P_(h+1)*V,

    P_h(X)T_h V(X)=W(X)-W(q^-1 X).             (1)

Thus seeking a rational certificate T_h V=K-kappa, with a constant remainder kappa, is exactly ordinary rational q-summability of P_h(K-kappa). It does not bypass multiplication by the long q-binomial polynomial: the pole residues of this right side already contain its desired evaluations.

For example, at a distinct simple native pole y,

    Res_(X=y) P_h(X)K(X) dX/X=omega*P_h(y).

For an entire multiplicative q-orbit, the sum of such differential residues of W(X)-W(q^-1 X) is zero: q-substitution permutes the orbit and preserves dX/X. Over a finite local field the orbit is finite, and this cancellation is exact. Over an infinite q-orbit only finitely many poles of a rational W occur, so the same telescoping cancellation holds. A constant kappa introduces no nonzero finite pole and cannot alter this orbit residue.

Consequently a q-orbit containing just one distinct simple native pole with omega*P_h(y) nonzero cannot be eliminated by any such rational certificate. With several poles on an orbit, the retained invariant is their sum of weighted P_h values. This is a conditional obstruction to THIS certificate reduction, not a complexity lower bound or a claim that every native instance has separate pole orbits. Repeated poles require the corresponding higher principal-part invariants; no decomposition by nonunit target differences is licensed over Z/N.

The native special collision makes P_h(y)=0 at a local factor for at least one covered row. Identifying which residues vanish is precisely the original locator, rather than a cheap precondition for rational reduction. Grouping public integer-exponent coincidences or actual full root cosets is allowed and already paid in preceding reports; it does not justify collapsing all remaining native pole orbits.

The general rational-q-difference solution literature does provide denominator-bound algorithms, e.g. Abramov, *A direct algorithm to compute rational solutions of first order linear q-difference systems* (Discrete Mathematics 246, 2002), primary preprint https://fpsac-archive.github.io/FPSAC99/ARTICLES/abramov.pdf . Such a rational-solution existence algorithm is not a soft-(J+sqrt h) evaluation algorithm for these retained orbit invariants. No additional complexity claim from that source is used.

## Paid complete scalar evaluation currently obtained

A direct rational-series execution acquires mu_0,...,mu_h from U in soft(J+h). Acquire all q powers and q-binomial coefficients using the ratio

    c_(n+1)/c_n=(q^h-q^n)/(1-q^(n+1)),

with certified unit denominator through n+1<=h, and return their literal weighted dot product. This costs soft(J+h), includes zero/nonunit weights and outputs, and does not divide c_n. It exceeds the target.

The existing block evaluator improves this to soft(J+sqrt(Jh)): choose d approximately sqrt(Jh), acquire P_d by its linear-factor product tree, evaluate at all q^(dg)y_i using monic multipoint trees, multiply the block values per target, and handle the one residual block separately. Then sum omega_i times the acquired P_h(y_i). All polynomial divisions are monic; all bases are acquired units. No output, target difference or collision product is inverted. This is exactly the paid baseline, not a new rate.

The whole weighted rational mixture does not currently permit a faster implementation than that baseline. Equation (1) pinpoints why replacing q-difference reduction with ordinary rational coefficient extraction would be circular: its unreduced finite-pole invariant is already the weighted P_h evaluation. No shared/frozen file, numerical campaign, backend theorem or constant-coefficient reinterpretation of the known Ore recurrence was used.

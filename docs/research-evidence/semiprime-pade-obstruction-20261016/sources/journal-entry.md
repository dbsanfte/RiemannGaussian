

## 2026-10-16: a Padé certificate closes the nearlinear constant-recurrence escape

Evidence: [quadratic constant-recurrence obstruction](research-evidence/semiprime-pade-obstruction-20261016/README.md). The preceding goal turn was progress: it removed balance from the paid short-annihilator extractor and all-semiprime setup, and justified the remaining canonical query for that base. The present advance is a rigorous obstruction to one proposed whole-query compression route, not an acquired evaluator or a new factoring exponent.

Let d=m², L=2m²+2, q=g^d, F(T)=product_(i<L)(1-q^i T)=sum c_k T^k and A_k=c_k g^(-binom(k,2)). In either hidden field, assume the already certified local q-order exceeds16m². Any nontrivial constant-coefficient recurrence for the COMPLETE finite stream A_0,...,A_L has effective order greater than floor(L/4), hence Omega(m²). Arbitrary input-dependent/advised field coefficients are allowed. This closes the earlier order2m and O(m polylog m) escape, which the order-at-most-m frequency argument had left open.

The new proof uses C(X)=sum A_k X^k and its exact TWO-CLOCK functional equation

 C(gX)-C(gqX)=gX[q^L C(X)-C(qX)].

An order-r recurrence throughout k=0,...,L-r yields a reversed denominator Q with Q(0)!=0, degQ<=r and a numerator P of degree<r, such that G=P/Q agrees with C through degree L. Substitute G into the equation and clear its four shifted denominator factors. The resulting numerator has degree<=4r but vanishes to order>=L+1. For4r<=L it is identically zero. The exact equation then determines G's coefficients uniquely through L+r, since q has no period there. They equal C's coefficients, followed by r zeros at the terminating endpoint. Therefore P-QC has degree<=L+r and vanishes to greater order, forcing P=QC and an impossible degree inequality.

A companion full-stream rational-approximation theorem gives the weighted bound u+3v>=L for numerator degree u<L and denominator degree v under its explicit q-order condition. It excludes a softly linear rational generating-function representation of this entire stream. It does not exclude an interpolant matching only the O(m) selected values, nor independently pay for their acquisition.

The proof works in arbitrary characteristic and needs no g-node distinctness, prime orders, alias screen or additional family deletion. It applies to the old qualified source and the NEW all-semiprime prepared beta/q base on the certified no-factor branch. The old coefficient ratio/chirp and order-at-most-m result are credited. Padé approximation and polynomial degree clearing are standard; this exact finite-stream application and its quadratic order consequence are the new result. Targeted repository searches found no prior matching argument; no absolute literature-priority claim is made.

This is a representation obstruction, NOT an operation lower bound. General q-dependent recurrences, vector/multivariate methods, sparse or nonlinear representations, selected convolution and scalar norms remain open. The existing soft-O(m^(3/2)) general query bound is unchanged. A whole-family soft-O(m) sufficient query and complete all-input Lean bit-complexity proof remain the objective. Independent exact-file reviews check the argument and source scope; no native edit, new Lean declaration, examples, broad build, commit or push is included. Every prior evidence packet and journal entry is retained.

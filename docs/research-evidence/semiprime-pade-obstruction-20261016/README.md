# Quadratic state is necessary for a constant recurrence of the chirped stream

This packet closes the constant-recurrence loophole left by the preceding chirp obstruction. It does not acquire the long collision query. The result is an exact finite-segment representation theorem, with arbitrary advised coefficients in either hidden field, rather than an arithmetic-operation lower bound.

For d=m², q=g^d and L=2m²+2, write

 F(T)=product_(i<L)(1-q^i T)=sum c_k T^k,
 A_k=c_k g^(-binom(k,2)),
 C(X)=sum_(k=0)^L A_k X^k.

Whenever the local q-order exceeds16m², NO nontrivial constant-coefficient recurrence of order r<=floor(L/4) holds throughout k=0,...,L-r. Thus any such recurrence for the entire finite chirped stream needs Omega(m²) order. This excludes the previously open order2m and every O(m polylog m) order eventually. Both the original qualified source and the paid all-semiprime setup satisfy the required local order condition, on its no-factor branch; no extra exceptional inputs are deleted.

The proof uses the exact two-clock equation

 C(gX)-C(gqX)=gX(q^L C(X)-C(qX)).

A finite order-r recurrence would supply a rational approximant P/Q matching C through degree L, with degP<r and degQ<=r. Substitution into the equation and clearing four shifted denominators gives a numerator of degree at most4r, vanishing through degree L. For4r<=L it must vanish identically. The resulting exact equation forces agreement for a further r coefficients, all zero beyond the polynomial endpoint. The rational approximant must then equal C, contradicting its degree bounds.

A companion statement excludes general low-degree rational generating-function approximants to the full finite coefficient stream: under the stated q-order condition, numerator degree u<L and denominator degree v must satisfy u+3v>=L. This does not exclude low-degree interpolants that match only the selected query values.

The coefficient ratio, chirp and prior order-at-most-m obstruction are inherited. The new argument uses a standard Padé/denominator-clearing technique on this exact finite sequence, replacing the earlier frequency-count restriction with a bound linear in L. It needs neither prime local orders, frequency distinctness nor the extra alias screen. No literature-priority claim is made.

- [Complete constant-recurrence proof](reports/pade-constant-recurrence.md).
- [General rational-approximation barrier](reports/rational-approximation-barrier.md).
- [Independent exact-file reviews](reviews/).

General q-dependent recurrences, vector or multivariate state methods, selected convolution and direct scalar norms remain possible routes. The general long-query clock remains soft O(m^(3/2)); a restriction-stable soft O(m) product/witness query and the complete Lean sixth-rate bit proof are still missing. No native changes, examples, broad builds, commit or push are included. All prior evidence is preserved.

# Focused Nogneng–Schost check and independent LCM review

2026-10-15. Primary PDF fetched fresh from https://cs.uwaterloo.ca/~eschost/publications/SparseEvaluation.pdf ; saved as nogneng-schost.pdf and extracted nogneng-schost.txt.

Nogneng–Schost, *On the evaluation of some sparse polynomials*, Math. Comp. 87 (310), 2018, studies

    P(X)=sum_(0<=i<T) p_i X^(a i²+b i),

where (a,b) is admissible (a+b and 2a are nonnegative integers), and a,b are fixed in its main cost bounds. This is a SUM with quadratic exponent support, not the q-Pochhammer PRODUCT.

Section 2 / Proposition 1 gives soft O(sqrt(T)) arithmetic operations over the base ring to evaluate at ONE supplied point when p_i=p^i for a fixed p. The fast step internally evaluates a degree sqrt(T) polynomial at sqrt(T) geometric points; these internal points should not be mistaken for free external evaluation points.

Section 3 / Proposition 2, for arbitrary coefficients, gives reduction modulo any supplied monic degree-T M, or evaluation at T arbitrary supplied points, in O(T^((omega+2)/4) M(T^(3/4)))=soft O(T^((omega+5)/4)) ring operations. This is subquadratic, not soft O(T). The theorem explicitly allows any base ring A, so it avoids a blanket field-transfer problem, but it does not state a soft O(J+sqrt(L)) algorithm for the desired q-Pochhammer at J points. Taking A itself to be a quotient algebra incurs the cost of operations in that algebra; they are not free base-ring operations.

The introduction cites Canny–Kaltofen–Lakshman for quasi-linear evaluation of an arbitrary T-term sparse polynomial on a geometric progression, via transposed Vandermonde structure. That algorithm still acquires all T coefficients/exponents. The q-Pochhammer polynomial has L+1 generally nonzero coefficients; its compact coefficient recurrence is not the input contract of this sparse-evaluation theorem.

Bostan–Yurkevich §2.2 discusses precisely the ONE-point quadratic-exponent sum and its first-order summand recurrence, then an order-two recurrence for partial sums. Its citation to Nogneng–Schost is not an arbitrary-external-points q-Pochhammer theorem. In particular, fixing numerical q and varying Y_j changes the recurrence parameter, rather than producing different indices of one fixed recurrence.

## What a genuine geometric target grid would allow

If targets are Y_j=z q^(e_j) with supplied integer e_j and a common z, then each desired q-product is an interval on the same orbit. All-positive adjacent intervals can merge, and overlapping intervals can be represented by their integer coverage multiplicities. A demonstrably short collection of ranges could give an improvement. Quotients of prefix products require unit checks; a division-free interval decomposition is needed when collisions are the point of the computation. Merely writing all Y_j as powers of a common gamma is insufficient: arbitrary exponents of gamma do not form a short consecutive grid for q=gamma^(m²).

The source relation a_j=N j^(-2) mod m is not the integer identity E_j=alpha j²+beta j+delta or a geometric-grid identity for Y_j. Reindexing j by its inverse makes a_j quadratic MODULO m, but E_j includes lifts, carries, and the additional ell_j term; a congruence modulo m does not become an exponent identity modulo the unknown local orders of gamma. No such bridge was found in this focused check. This identifies the exact missing theorem without claiming no source-specific grid decomposition exists.

## Independent review of durable LCM note

Reviewed /home/dbsanfte/riemann/formal/docs/research-evidence/semiprime-long-query-20261015/lcm-exponent-obstruction.md in full. No mathematical bug found in the stated scope.

* For distinct prime factors and prime local orders, exact LCM preserves whether either local order divides at least one nonzero exponent, hence the claimed gcd equality. Composite local orders and arbitrary common multiples are properly excluded.
* The prime-valuation argument for product/LCM dividing (n-1)! is valid, including equal maximal valuations. Primitive growing step causes no hidden fixed-step assumption.
* A signed progression with no zero has a consecutive same-sign subprogression of at least ceil(L/2), retaining primitive step m².
* Substitution of the stated historical source identities gives j² k=N(j-1)²-vj² modulo m. The polynomial has nonzero linear coefficient -2N, so at most two exceptional tags. Original v=0 has only j=1.
* The explicit exponent size and formal addition/subtraction-chain bound are correctly scoped. They do not exclude other ring operations, known annihilators, or smaller congruent exponents.

The historical source formulas and existence/population of long rows remain explicit upstream inputs; I did not reproduce their full upstream proof closure.

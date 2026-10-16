# Rational certificates expose the row products; two shared computations are cheap

2026-10-15. Three Sol 6.1 investigations and a joint cyclic-trace proof.
The long-query acquisition bound remains soft O(m^(3/2)); no soft O(m)
evaluator or new Lean endpoint was obtained.

## The rational-certificate escape is classified exactly

The preceding actual adjoint obstruction concerned finite Laurent
certificates. This continuation allows arbitrary rational functions,
including poles, for the SAME operator

    T(p)=(1-x^d)p(x/gamma)-u(q^L-x^d)p(x),
    d=m^2, q=gamma^d, u=gamma^(-N-3d).

In either hidden field, gamma has the retained prime order R>L.
For e_j=3d-delta_j, the equation

    T(p)=x^e_j, p in K(x)

has a rational solution IF AND ONLY IF the complete original row
product P_L(gamma^(-N-delta_j);q) is ZERO in that field.

The proof supplies an exact obstruction, rather than a large-degree
heuristic. A rational gauge changes T into a cyclic difference S-1.
Such a difference has trace zero; conversely trace zero gives an
elementary rational solution. The trace of the source monomial is

    (explicit nonzero rational factor) * P_L(z_j;q).

Thus a unit row admits no rational endpoint-only certificate at all,
even allowing boundary poles. In independent formal weights,
T(p)=sum_j w_j x^e_j is solvable exactly when EVERY row product is
zero. Rational dependence of p on the weights is allowed.

The previous row-sparsity theorem leaves m-o(m) unit rows in both
fields on the same retained infinite family. The full weighted rational
certificate therefore does not exist there. No additional counterfamily
intersection or new prime-distribution input is used.

This is an exact rational-function identity theorem. It does not exclude
pointwise finite-grid interpolation with omitted poles, identities only
modulo x^R-1, parameter-deformation finite parts, another operator, or a
method retaining and evaluating a remainder. The rational cokernel is
ONE-dimensional over K(x^R); the earlier Laurent sector count must not
be transferred to it. The coefficients of the rational trace remainder
contain the unpaid row products.

The order R and its modular index occur only in the proof. Computing the
trace coefficient is not a free zero test or a new evaluator. See
[the exact trace theorem](reports/rational-trace-criterion.md).

## Selected coefficients of one stream have a nearlinear acquisition bound

For the ONE fixed coefficient stream

    P_L(Z;q)=sum_(k=0)^L c_k Z^k,
    (1-q^(k+1))c_(k+1)=(q^L-q^k)c_k,

any nu public indices k_j in [0,L] can be evaluated together in

    soft O(sqrt L+nu)

ring operations and comparable storage, under the actual-source unit
conditions 1-q^a invertible for 1<=a<=L. The indices may depend on the
full public N and may repeat. All preprocessing, index powers and one
certified batch denominator inverse are charged.

Shared degree-sqrt(L) block products acquire the coarse prefixes.
Binary tail refinement evaluates the SAME short block polynomial at
all requested starts at each level. Monic product/remainder trees work
over Z/N even with repeated points or nonunit point differences. The
construction does not import a field interpolation algorithm unchanged.

This specializes the several-index q-holonomic method to the composite
ring. For nu~m and L~m^2 it gives a paid soft O(m) subroutine. It does
NOT evaluate P_L at changing target points: those are weighted sums
of the stream, rather than selected terms. Unknown local discrete-log
indices, parameter jets, and pole regularization are also not supplied.
See [the algorithm and cost](reports/selected-qbinomial-primitive.md).

## The short weighted state can also be initialized cheaply

Let F_n=sum_j w_j P_n(z_j;q), Q_n=prod_(r=1)^n(1-q^r), and
s_k=sum_j w_j z_j^k. The q-binomial formula gives a single convolution

    F_n/Q_n=(A*B)_n,
    A_k=(-1)^k q^(k(k-1)/2)s_k/Q_k, B_k=1/Q_k.

The first J moments, all parameter constants and the convolution cost
soft O(J). Thus all F_0,...,F_(J-1), as formal-weight circuits, and the
inverse prefix transform are acquired in soft O(J). The natural dense
scalar-operator table is unnecessary for INITIALIZATION.

Initializing a distant state still requires the unknown weights
w_j P_n(z_j). A fast long-horizon jump is not implied. See
[the prefix construction](reports/q-newton-prefix-initialization.md).

## Literature and remaining target

Fresh rational-denominator and summation papers were checked, including
2017 q-recurrence bounds, 2022 q-rational reduction, 2025 discrete
residues and 2026 polynomial reduction. Their field, shift and singularity
premises remain explicit. The new trace proof is self-contained; it
does not transfer a characteristic-zero denominator theorem to the
finite hidden fields. The positive coefficient algorithm is likewise
proved directly with its composite-ring unit contract.

The next positive theorem must acquire the weighted/scalar long query
while retaining a nonzero remainder, or supply a different exact
collision-preserving construction. Nearlinear prefix initialization and
indexed coefficients now have paid interfaces; combining them into the
required long query remains open. The existing reverse-AD bridge would
turn a fast formal weighted program into all row products.

All new results are classical and independently reviewed. The existing
full seed coverage/recovery is unchanged. A restriction-stable soft O(m)
query, then the complete routing/kernel/controller bit and memory proof
in Lean, are still required for guaranteed one-sixth factorization.
The manifest preserves final report/review hashes, primary papers and
source pins; earlier evidence bundles remain frozen. No new Lean,
numerical corpus, broad build, commit or push was added.

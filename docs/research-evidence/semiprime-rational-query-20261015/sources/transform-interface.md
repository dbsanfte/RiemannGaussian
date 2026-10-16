# Offset-grid q-binomial transforms: a precise new interface

2026-10-15. Investigation of a positive implicit evaluator, not a repeat of the previous resultant catalog. No repository changes. No nearlinear algorithm is proved below.

Let d=m², q=gamma^d, J~m and L~m². Normalize the original residual product to

    P_L(z)=prod_(i<L)(1-z q^i),
    z_j=gamma^(-N-delta_j),

up to the explicitly known unit product of target powers. The supplied delta_j lie in [-3d,d]. The requested scalar is prod_j P_L(z_j), or a proper factor with the canonical recovery controller. Changing to inverse gamma or shifting all exponents by 3d does not change the following interfaces.

## 1. A genuine cheap sparse-exponential primitive

For arbitrary weights w_j, let E(T)=sum_j w_j T^(delta_j+3d). It has at most J monomials despite degree at most 4d. Its moments

    s_k=sum_j w_j gamma^(k(delta_j+3d)),  0<=k<K,

can be generated in soft O(J+K) ring operations once the J unit nodes are acquired. One direct division-free proof forms

    sum_(k>=0) s_k t^k = sum_j w_j/(1-a_j t),
    a_j=gamma^(delta_j+3d),

by a balanced rational-function product tree, then expands to K terms. Denominators have constant coefficient 1, so no target differences or q^k-1 need be inverted. This is the same transposed-Vandermonde primitive used for sparse evaluation on a geometric progression. It is valid over the composite ring.

The reverse transform computes evaluations of a polynomial C(T)=sum_(k<=L)c_k T^k at the J gamma-power nodes. Transposition gives soft O(J+L) for an EXPLICIT c vector. It does not make L implicitly supplied coefficients free. This distinction is central: the offset mask is sparse, while the q-binomial coefficient vector is generally dense.

For P_L, c_k=(-1)^k q^(k(k-1)/2) [L choose k]_q. When q^(k+1)-1 is a unit,

    c_(k+1) = -q^k (1-q^(L-k)) (1-q^(k+1))^(-1) c_k.

These formulas define polynomial coefficients by exact q-binomial identities even at exceptional q, but their rational sequential evaluation must not invert a nonunit. Ordinary sparse interpolation/evaluation does not supply the missing implicit-coefficient transform.

A concrete next positive target is an efficient arbitrary-weight INNER PRODUCT between this q-binomial coefficient stream and a short linear-recurrence moment stream, without producing all L terms. A numerical black-box value for one weight vector is only a linear combination of the P_L values and does not preserve ANY-collision semantics. However, a formal division-free straight-line program for the arbitrary-weight inner product over R[w_1,...,w_J] DOES suffice: reverse-mode formal differentiation at w=0 recovers every P_L value in O(T+J) operations from a T-operation program, after which J-1 multiplications give the product. This conditional positive bridge and its ring-safe proof are recorded in positive-adjoint-interface.md. No fast program for the weighted inner product has yet been obtained.

## 2. What the short exponent span actually buys

Writing delta_j=r_j+d h_j with 0<=r_j<d gives bounded integer h_j because delta_j lies in [-3d,d]. The exact q-step identity

    (1-z) P_L(qz)=(1-z q^L)P_L(z)

transports P_L(z q^h) to P_L(z) with O(|h|) endpoint factors, provided the necessary divisions are licensed by unit/gcd handling. Thus the short delta span can normalize each row to one of d residue sectors with only O(J) explicit endpoint factors. It does NOT identify the baseline values P_L(gamma^(-N-r_j)) for distinct r_j.

The original low-digit source formula admits at most two tags with the same delta modulo m; hence also at most two tags in any exact residue sector modulo d. Therefore this elementary normalization leaves Omega(J) distinct sectors. It offers at most constant-factor reuse, not a shared baseline q-factorial. No claim is made about hidden-field orbit disjointness: q and gamma may generate the same local subgroup, but their numerical conversion exponent depends on the unknown order.

Endpoint inversions must still be checked. A factor-or-query algorithm may stop on a proper gcd, and the canonical source recovery mechanism handles a suitably certified global leaf; the normalization itself is not a free assertion that every endpoint is a unit.

## 3. Exact correction degree for gamma-step transport

A tempting FFT-style strategy transports between consecutive gamma powers rather than consecutive q powers. The required rational correction is

    P_L(gamma z)/P_L(z)
      = prod_(i<L)(1-gamma z q^i)/prod_(i<L)(1-z q^i).

Over the rational-function field Q(gamma), with gamma transcendental and q=gamma^d, d>1, numerator and denominator are coprime: equality of one numerator and denominator root would imply 1+d(i-j)=0, impossible in integers. Both therefore have degree L in reduced form. Thus there is no bounded-degree rational correction for a gamma-step in this formal generic model; the q-step's degree-one endpoint correction is special to a full stride d.

For numerical gamma in a hidden field, cancellations can occur when its local order R divides 1+d(i-j). This possibility is NOT excluded by the global-order bound alone, since local exponent differences can wrap even when global numerical nodes are distinct. A valid actual-source algorithm might exploit such special cancellation if it cheaply acquires the relevant local-order information or proves an appropriate uniform relation. The generic correction-degree statement is not a lower bound for that algorithm, and it is not asserted as a fieldwise rank theorem for every actual input.

The output sequence f(r)=P_L(gamma^r) obeys a low-degree recurrence at STRIDE d,

    (1-gamma^r) f(r+d)=(1-gamma^(r+dL)) f(r).

This is not a constant-stride-one recurrence with a fixed number of sector initial values; it has d residue sectors in the elementary recurrence. The short exponent span makes the number of visited steps per chosen sector constant but does not acquire those sector values. A new batched-sector theorem is exactly what would be needed.

## 4. FFT and cyclic-dilog domain checks

The exact distribution identity

    prod_(r=0)^(d-1) P_L(z gamma^r) = P_(dL)(z;gamma)

holds because the exponent intervals d*i+r partition [0,dL). It needs the COMPLETE d-sector collection; the actual J~sqrt(d) sparse sectors do not form that complete mask. Completing them adds Theta(d) sectors, and the right side is a gamma-product of length dL~m^4 whose generic scalar square-root evaluation costs soft O(m²), not soft O(m).

Finite cyclic-dilog or q-binomial reductions based on q^L=1 cannot be inserted into the canonical family: the retained local prime orders exceed the searched L, and the global order is still larger. Approximate analytic Fourier or modular q-Gamma reciprocity would need an exact finite-ring reconstruction theorem with explicit precision and bit costs and preserved collision zeros. No such specialization was obtained here.

## 5. Narrow literature checks for this interface

The relevant sparse-evaluation discussion in van der Hoeven–Lecerf, *On the factorization of sparse polynomials*, section 2.4, explicitly treats evaluation of an s-sparse polynomial at consecutive geometric points using transposed multipoint evaluation. That is the sparse-moment primitive above; it does not claim evaluation of a densely supported implicit q-hypergeometric coefficient stream at a sparse subset for soft O(J+sqrt L). Primary: https://www.texmacs.org/joris/sparsefact/sparsefact.pdf .

The 2025 ESA paper *A Simple Algorithm for Trimmed Multipoint Evaluation* concerns bounded-total-degree multivariate polynomials and matching trimmed grids, with coefficient count matching grid cardinality. The input here is a dense one-variable polynomial of degree L represented by a q-product, evaluated on sparse selected gamma powers. No reduction preserving size O(J+sqrt L) to the trimmed-grid contract is supplied by that theorem. Primary: https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ESA.2025.89 .

No unsupported reduction to a generic sparse-Fourier lower bound is made. The coefficients here are highly structured, the output needed is nonlinear, and the finite composite ring differs from numerical complex Fourier models.

## Outcome

The useful new positive interface is a q-binomial transform with sparse gamma-power output nodes, supplied by a dense but succinct q-hypergeometric input stream. The ring-safe sparse-moment transform is cheap and genuine; transposition alone still pays L. Short source offsets give bounded q-stride corrections but leave Omega(J) distinct residue sectors. Generic gamma-step correction has degree L, while numerical local cancellations require a separately acquired order-dependent identity. These facts identify a concrete batched-sector/implicit-stream theorem to seek without claiming that all scalar or input-dependent algorithms are blocked.

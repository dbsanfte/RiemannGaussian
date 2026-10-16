# Direct q-resultant: scalar duality is exact; the audited resultants do not remove the growing degree

2026-10-16. This is a primary-source applicability audit and a self-contained costed reduction, not an operation lower bound. No whole-query nearlinear algorithm was obtained.

Let R=Z/NZ, q and z_j be supplied units, D(t)=prod_j(t-z_j) monic of degree J, and F(t)=prod_(0<=i<L)(1-t q^i). Multiplicities are allowed. The exact scalar target is Res_t(D,F)=prod_j F(z_j). Define G(X)=prod_j(1-z_j X)=X^J D(1/X). Then

    Res(D,F) = prod_(0<=i<L) G(q^i).                         (1)

This uses no root extraction, order oracle, interpolation, inverse node differences, or division. In particular it survives arbitrary composite moduli and zeros. Building G from the actual roots costs soft O(J). Scalar norm-first processing therefore has a particularly clean interface: a length-L first-order multiplicative q-recurrence whose polynomial coefficient has degree J. The polynomial coefficient degree must be charged; it is not a fixed-degree q-holonomic instance.

## Charged baby/giant scalar evaluation

For a positive block length b, write L=ab+r, 0<=r<b, and form

    A_b(X)=prod_(0<=s<b) G(q^s X),    deg A_b=Jb.

Then (1) is prod_(0<=h<a) A_b(q^(bh)), times prod_(0<=s<r)G(q^(ab+s)). Product trees, coefficient scalings, and monic remainder-tree multipoint evaluation give soft O(Jb+L/b+J) ring operations, including the incomplete block: its combined degree is at most Jb. Use b=max(1,ceil(sqrt(L/J))). This gives soft O(J+sqrt(JL)) for J<=L. For J~sqrt L, the clock is L^(3/4), not sqrt L.

This is a scalar-only route already: its failure to improve the baseline cannot be blamed on acquiring all J output values. Equally, the displayed implementation cost is not a lower bound on evaluating the scalar product. A different representation, cancellation, or determinant algorithm could improve it. Dense A_b acquisition is the specific unpaid interface in this implementation. No claim about unavoidable coefficient support on the actual family is made.

All operations above can be implemented over R without inverting a resultant or a row value. Product/remainder trees divide only by monic polynomials. Public powers contribute their usual logarithmic exponent cost. There is no requirement that 1-q^k be a unit. Hence a Gaussian-coefficient expansion with divisions is unnecessary for this upper bound.

## Primary theorem audit

1. Bernstein–De Feo–Leroux–Smith, *Faster computation of isogenies of large prime degree* (ANTS 2020), §§3.1–3.2 and Lemma 3.4/Algorithm 1:
   https://velusqrt.isogeny.org/velusqrt-20200616.pdf

   Section 3.2 explicitly treats a multiplicative modular factorial over Z/nZ with a supplied unit base. It builds two degree-b polynomials for ONE target alpha, b~sqrt(ell), and evaluates their resultant or uses a remainder tree. This is an actual composite-safe positive theorem for a single q-product. The group-index sumset identity behind the scalar resultant is exact. It does not assert simultaneous amortization over J arbitrary alpha targets. Replacing alpha by a degree-J norm produces (1); the naive combined factors have degree Jb, precisely the charge above. The later elliptic theorem is over a finite field and supplied elliptic-group/index-system data, not an algorithm that constructs a small sumset decomposition of this actual quadratic/carry catalog. The source's resultants have explicit small coefficient inputs; the word “resultant” alone does not provide a compressed-input evaluator.

2. Bostan–Flajolet–Salvy–Schost, *Fast Computation of Special Resultants*, JSC 41 (2006), Theorem 1:
   https://cs.uwaterloo.ca/~eschost/publications/BoFlSaSc05.pdf
   https://doi.org/10.1016/j.jsc.2005.07.001

   The composed product of degree-u and degree-v polynomials is a degree-uv polynomial, obtained in O(M(uv)) field operations in characteristic zero or >uv; the paper also treats specified small-characteristic multiplicity regimes. Taking the geometric-root polynomial of degree L and the node polynomial of degree J computes a degree-JL composed product, of which the desired scalar is its value at 1. This theorem computes that whole polynomial; its bound is not O(M(J+sqrt L)) for one selected value. Its power-sum reconstruction uses precision uv; retaining only the first J coefficients does not determine the value at 1. The theorem is stated over a field. Even if its permitted divisions are certified units or intercepted by gcds over R, neither the precision nor the explicit-input charge disappears.

3. Bostan–Yurkevich, *Fast Computation of the N-th Term of a q-Holonomic Sequence and Applications*, primary preprint and journal version:
   https://arxiv.org/abs/2012.08656
   https://doi.org/10.1016/j.jsc.2022.07.008

   This is background for q-factorial/recurrence acceleration, not a new improvement claimed here. Equation (1) is a recurrence with degree-J coefficient G, so a theorem with fixed recurrence degree cannot silently treat J as constant. The explicit ring-safe baby/giant derivation above supplies the degree-sensitive cost without relying on that interpretation.

A targeted primary web search including 2025/2026 q-factorial, geometric resultant, norm, and special-resultant terms did not identify a newer theorem supplying the missing compressed scalar interface. This is a search outcome, not an exhaustive nonexistence assertion. Only the two PDFs actually inspected for the applicability claims above are retained locally.

## Restriction and saturation requirements

For a subset S of tags and an interval [a,a+ell), replace G by G_S(X)=prod_(j in S)(1-z_jX), and q^i by q^(a+i). Equation (1) and the same bound soft O(|S|+sqrt(|S| ell)) remain valid. Variable row intervals can be split into interval/subset blocks, but the resulting number of blocks must be charged. One cannot cite a rectangle algorithm as a free algorithm for arbitrary row lists.

A hypothetical oracle with soft O(|S|+sqrt ell) rectangle cost would be useful even though the full norm can equal zero modulo BOTH prime factors: gcd=N is saturation, not a factor. Binary localization over tags and the interval uses O(log(JL)) restricted calls. A nonunit product has a nonunit descendant; at a leaf a proper gcd gives a factor, while a global-zero residual is handled by the already compiled native global phase/sum recovery for the canonical seed range. This coverage/recovery is inherited, not a new contribution of this note. Any scalar-only proposed algorithm must retain these restrictions or pay an alternative saturation-resolution mechanism. The actual known unit-difference nodes help ordinary interpolation, but supply no known direct scalar norm compression in the audited theorems.

# Multibase acquisition audit for the Fermat multiplier cover

Date: 2026-10-22. Scope: targeted primary-literature search and exact algebra/cost audit. No repository files changed. The frozen source of the cover and decoder is `docs/research-evidence/semiprime-fermat-multiplier-20261022/README.md`; this report does not claim those inherited results as new. The constructive-frontier index was checked, in particular original-row generic sharing, selected q-Newton coefficients/jets, fixed-weight norms, and the carry-preserving stationary transform.

**Result.** No cited theorem supplies the missing restriction-stable soft-O(r) query. A stronger exact algebraic scope result was subsequently proved in the companion `interval-reindexing.md`: restricting by T=H sigma-bc in an interval enumerates every T in that interval with r not dividing T, exactly once. For the sufficient positive interval [1,2r^3], even the total unit exponent cancels. Thus this cover alone relabels an ordinary length-Theta(r^3) geometric query rather than sparsifying it. The following literature ledger remains useful for auditing proposed accelerations of that query. The closest applicable results compute one geometric product in square-root time, or a resultant/norm in time charged to its dense degree or algebra dimension. The new exact check below identifies why the two-set structured-resultant representation cannot by itself make this particular exponent family soft-O(r). This is a statement about that representation, not a general computational lower bound.

## 1. Exact acquisition problem and paid inputs

Write H=r^2, R=Z/NZ, n=ceil(log_2 N)=Theta(log r). In the balanced branch N~r^6, the inherited setup gives a unit beta with

    D=ord_N(beta)>256 r^4,   D | phi(N).

It also certifies the needed local orders and short-q-factorial units; no new local-order assumption is required here. Let

    theta=beta^N,  q=beta^H,  x_b=beta^b.

There are k=O(log^3 r) selected Fermat-quotient layers. Each layer a has r-1 catalog residues s, a centered representative

    b_s = center(-N/s mod H),  |b_s|<=H/2,

and a set C_a subset {1,...,r-1}. These C_a are arbitrary selected subsets, not necessarily intervals or full geometric progressions. They arise from a partition of the r hidden quotient values, so

    sum_a |C_a|=r.

The target query is a modular product, or a sufficient gcd decision, over leaves

    q^sigma - theta*x_b^c,  b in B_a, c in C_a, sigma in I,
    I={-3r,...,3r}, L=6r+1.

A successful method must also support the restrictions required by product localization. Proper gcd leaves factor N; every global colliding leaf is decoded by the inherited bounded global-order argument, using P+Q=1+H sigma-bc. This report leaves that decoder unchanged.

All catalog rows and their bases are available in soft-O(r) bit operations: signed binary powering takes O(log r) multiplications per row, and there are J=(r-1)k=soft-O(r) rows. The polynomial

    F(Y)=product_(sigma in I) (q^sigma-theta Y),  deg F=L,

is also available in soft-O(r) bit operations by a product tree. It has unit leading coefficient. Arbitrary monic multipoint evaluation needs no inverse of target differences.

Throughout, soft-O suppresses powers of log r and log N. Ring operations are not bit operations: an explicit degree-d polynomial over R has O(d n) bits, and multiplication/remainder modulo a monic degree-d polynomial costs soft-O(d n) bits by Kronecker packing and integer multiplication.

## 2. Exact exponent count and its limited consequence

The cover's witness partition makes (s,c) -> s/c a bijection onto (Z/HZ)^*. Multiplication by -N then makes

    (b,c) -> bc mod H = -N/(s/c) mod H

another bijection. Consequently the selected exponent residues bc modulo H are all distinct and number exactly r(r-1). This does not require any statistical property of the greedy cover.

Now put

    E={bc-H sigma : selected (b,c), sigma in I}.

If two such integers agree, reducing modulo H gives the same selected pair, and then sigma agrees. Therefore

    |E|=r(r-1)(6r+1).

Also |bc-H sigma|<3.5 r^3. Since D>256 r^4, beta is injective on this entire integer interval: these exponents produce distinct elements globally modulo N. This does not assert pairwise unit differences modulo N; differences can vanish at one hidden factor, which is the intended signal.

The original leaves differ by known unit factors from

    beta^(-N) - beta^e,  e in E,

because q^sigma-theta beta^(bc) = theta q^sigma (beta^(-N)-beta^(bc-H sigma)). Thus a structured product over E would suffice.

Suppose one applies the two-set Pollard/resultant representation E=(U+V) disjoint-union K, with the pair map U times V -> U+V injective. Then necessarily

    |U| |V| + |K| = r(r-1)(6r+1).

In particular max(|U|,|V|,|K|) cannot be soft-O(r); a constant or polylogarithmic number of such representations of soft-O(r) size also has insufficient cardinality. This only excludes that particular small-two-set description of the full product. It does not exclude specialized multivariate algorithms, a sufficient subproduct, or algorithms sharing work without this description.

## 3. One progression: exactly what fast geometric-product results pay

Bernstein, De Feo, Leroux and Smith, *Faster computation of isogenies of large prime degree*, Section 3, Algorithm 1 and Proposition 3.5, give a multiplicative Pollard product via resultants. For exponent sets S=(U+V) disjoint-union K with no common differences between U and V, evaluation of product_(s in S)(alpha-zeta^s) costs soft-O(max(|U|,|V|,|K|)) base-field operations, plus constructing the required powers. Their Section 3.2 explicitly permits a unit zeta over Z/NZ and uses ordinary remainder trees as an alternative to resultant division. The elliptic extension is Theorem 4.11. [Primary preprint, pp.3-8](https://arxiv.org/pdf/2003.10118).

For fixed b and interval c, let z=x_b. The two-dimensional rectangle can be computed in soft-O(r) ring operations:

    product_(sigma in I) product_(1<=c<r) (q^sigma-theta z^c).

Indeed, form the degree-r polynomial A(T)=product_(1<=c<r)(T-z^c), evaluate A at the L points q^sigma/theta by a remainder tree, and restore theta powers. This is an exact resultant of degree-O(r) polynomials. For arbitrary C_a, form A only on those c, still at cost soft-O(r). Applying this independently to J=soft-O(r) bases costs soft-O(r^2), not soft-O(r).

Alternatively, fixed (b,c) gives a q-Pochhammer product of length L at cost soft-O(sqrt L). There are r(r-1) selected pairs, so this alone costs soft-O(r^(5/2)). The first construction is better, but neither is a new whole-family acquisition result.

The exponent-count argument in Section 2 shows that the cited two-set theorem, applied directly to all of E, cannot give soft-O(r). Enclosing E in its length-O(r^3) integer interval and using a square-root interval product gives soft-O(r^(3/2)), before appropriate gcd/localization handling. That is the familiar quarter-rate scale, not the desired sixth-rate scale. The frozen packet already contains an unconditional positive-integer product with this cost, so no claim of a new factoring algorithm is made here.

## 4. q-holonomic and q-multifactorial methods: the degree is not fixed

Bostan and Yurkevich, *Fast Computation of the N-th Term of a q-Holonomic Sequence and Applications*, Section 3.4 and Theorem 5, make the growing-parameter dependence explicit. A recurrence of order rho and coefficient degree d costs

    O(rho^omega sqrt(ell d) + rho^2 M(sqrt(ell d)))

field operations for an ell-step computation (ell>d). Their baby polynomial has degree sd and optimal block length s~sqrt(ell/d), not always sqrt ell. Algorithms 3-4 also explain the special monomial rescaling trick. [Primary preprint, pp.9-15](https://arxiv.org/pdf/2012.08656).

For our scalar product over c, the recurrence multiplier is F(z^c), degree d=L=Theta(r). A c-interval has length ell=Theta(r). At this boundary one can simply multiply r factors, or use the degree-r resultant above, at soft-O(r) cost per b. Reading the theorem with d treated as a constant would wrongly claim square-root improvement. Conversely, moving all b into a product coefficient algebra gives rank J~r; a scalar operation there is not a scalar operation over Z/NZ.

One may instead use sigma as the sequence variable and multiplier

    G_a(Y)=product_(b in B_a,c in C_a) (Y-theta x_b^c).

Its degree is (r-1)|C_a|. It is not already supplied for free. The total degrees sum to r(r-1), and explicitly building these polynomials already has soft-O(r^2) coefficient cost. A q-holonomic closure theorem does not bypass this acquisition: one must charge its resulting order, degree, and construction.

A full-orbit binomial identity is also unavailable at the present short length: ord_N(q)=D/gcd(D,H)>256 r^2, whereas L=6r+1. The target progression is not an entire q orbit.

## 5. Power composition and norm formulations: exact but still unpaid

For one layer define

    R_a(X)=product_(b in B_a)(X-x_b), J_a=r-1,
    H_a(X)=product_(c in C_a) F(X^c).

Then the exact layer product is

    Res_X(R_a,H_a)=Norm_(R[X]/(R_a))/R (H_a mod R_a).

The identity holds over a commutative ring even if some x_b-x_b' are nonunits. One can compute the final norm via the known linear factors of R_a and monic remainder trees, avoiding an unsupported field-only resultant step. Its cost is near-linear in J_a once H_a mod R_a is actually given.

The missing operation is constructing that residue. The unreduced degree is

    deg H_a = L * sum_(c in C_a) c.

Summing over layers gives at most L*r*(r-1)=O(r^3). This is an upper bound on the degree of this particular dense expansion, not an assertion that every selected cover attains it. Each selected c gives F(X^c) mod R_a, a modular-composition problem after computing X^c mod R_a. Even granting an ideal near-linear algorithm for each such composition, r selected labels times rank r still gives soft-O(r^2) by this route. Computing the norm does not itself construct H_a.

Likewise the power-map polynomial

    R_(a,c)(T)=product_(b in B_a)(T-x_b^c)

can move the c-th power from F into the root polynomial. Its degree is J_a, but there are sum_a |C_a|=r such polynomials. Expanding their product has degree r(r-1); the final evaluation at L geometric points then has a genuine r^2-scale dense object. Faster power projection for one c does not automatically share all these c's.

Poteaux and Schost, *Modular composition modulo triangular sets and applications*, explicitly use delta=product_i d_i, the dimension of the quotient algebra, as the complexity size. Norm means determinant of multiplication or iterated resultant; their finite-field algorithms are almost linear in that dimension, not in the number of variables. [Primary preprint, pp.1-4](https://cs.uwaterloo.ca/~eschost/publications/mulmodcomp.pdf).

As a current check, Neiger, Salvy, Schost and Villard's ISSAC 2026 *Faster modular composition using two relation matrices* gives soft-O(n^((omega+3)/4)) arithmetic cost under stated genericity assumptions (about n^1.343 with their cited matrix exponent). It distinguishes finite-field Kedlaya-Umans n^(1+epsilon) log(q)^(1+o(1)) bit bounds from quasi-linear formal-power-series composition. None of these statements is a deterministic soft-linear arbitrary-input modular-composition theorem over Z/NZ, nor an all-c product theorem. [Primary paper, p.1 and Theorems 1.1-1.3](https://perso.ens-lyon.fr/gilles.villard/BIBLIOGRAPHIE/PDF/comp2.pdf).

This report does not need to settle whether a particular finite-field composition algorithm can be adapted to the balanced composite modulus: even a perfect rank-linear one-composition primitive does not pay the r compositions in the above straightforward reduction.

## 6. Special resultants, sparse evaluation, truncation, and packing

Bostan, Flajolet, Salvy and Schost, *Fast Computation of Special Resultants*, Theorem 1, compute composed sums/products of degree-m and degree-n polynomials in O(M(mn)) field operations when the characteristic is zero or exceeds mn. Their output has degree mn. Their more general diamond product has a larger bound and represents a fixed polynomial function of two roots; it does not supply exponentiation by a variable integer c as a constant-degree polynomial map. [Primary preprint, pp.1-4](https://cs.uwaterloo.ca/~eschost/publications/BoFlSaSc05.pdf).

Our use-case conclusion is about the interface: a soft-linear-in-output composed-product algorithm with two degree-r inputs still handles an r^2-coefficient output. Reinterpreting c as a root coordinate requires an actual polynomial representing (X,c)->X^c, together with its degrees and construction cost. No such low-cost representation on the selected c set was supplied by the theorem. Computing only a scalar evaluation can sometimes be much cheaper; Section 3 records the applicable example, without extending its hypotheses.

Nogneng and Schost, *On the evaluation of some sparse polynomials*, Proposition 1, handle sums with quadratic exponent patterns and geometric coefficients in soft-O(sqrt ell) ring operations at one point. Proposition 2 handles arbitrary coefficients at ell points in soft-O(ell^((omega+5)/4)) operations. These are additive sums; no identity in that paper converts our multiplicative rectangle into a single qualifying sparse sum. [Primary paper, pp.3-4 and 9](https://cs.uwaterloo.ca/~eschost/publications/SparseEvaluation.pdf).

Thus a theta/chirp evaluation alone is not a norm evaluator. Linearizing the product through a formal logarithm requires enough coefficients or traces to recover the norm, and divisions must be checked over R. The inherited selected q-Newton/jets consumer is already in the constructive-frontier index; this search found no reduction of the present multibase product to its paid selected data.

Moroz and Schost, *A fast algorithm for computing the truncated resultant*, compute Res_y(P,Q) mod x^k in soft-O(kd) field operations for degree-d inputs, with characteristic zero or at least k. This removes dependence on the full output degree in x; it does not remove the degree in the elimination variable. [Primary ISSAC 2016 paper, pp.1-2](https://cs.uwaterloo.ca/~eschost/publications/resultant_series_final.pdf).

For Res(R_a,H_a), choosing k=1 does not make the unexpanded H_a a low-degree input: its degree in X is still L sum c unless a separate fast remainder construction is proved. Nor is this field theorem directly a ring-safe black box when zero divisors are the desired output.

Exact Kronecker packing makes the same charge visible in bits. To multiply two degree-d polynomials with representatives in [0,N), choose radix 2^w>(d+1)N^2. Packed inputs have O(d(n+log d)) bits, and multiplication costs soft-O(d(n+log d)); reduce output coefficients modulo N. A bivariate dense support of size (d_1+1)(d_2+1) costs the corresponding number of packed slots. Calling one packed multiplication a unit-cost operation would hide this support size. This observation audits ordinary dense packing, not every possible algorithm for the final scalar product.

## 7. Restriction safety and concrete remaining theorem

The cleanest sufficient new theorem would accept the paid inputs F, {x_b}, and the selected label sets C_a, and return

    gcd(N, product_a product_(b in B_a,c in C_a) F(x_b^c))

or a factor/global-collision certificate in soft-O(r) bit operations, together with the restrictions needed to localize a saturated product. No theorem above meets that specification.

A sufficient special-case advance could avoid computing every product leaf, but must prove coverage of that restriction for every admissible hidden prime. Merely taking few c values is not yet justified. At the elementary cover level, A-Q(C)=F_r requires |A||C|>=r, so a polylog-sized A cannot have only polylog-many distinct selected c values. This is only a counting constraint on that proposed restricted cover, not a lower bound on shared evaluation.

Restrictions to subsets of b or selected c preserve the monic-product and resultant identities; arbitrary subsets of sigma lose the direct q-Pochhammer interval speedup. If localization uses interval splits of sigma, the one-progression routines remain applicable. Any claimed new bound must specify these restrictions rather than just produce one unrestricted scalar value.

The precise unpaid object is the simultaneous product of power-composed evaluations, or an equally sufficient factor query, for r labels acting on r row bases. Existing norms/resultants make the endpoint cheap after that object is present. The targeted primary sources do not construct it at the sixth-rate budget.

## 8. Search provenance and limitations

Targeted queries covered multibase geometric products, special/resultant power composition, multiplicative Kronecker and quotient norms, q-multifactorials/q-holonomic matrix products, sparse quadratic-exponent evaluation, and the square-root Velu framework. The cited PDFs were inspected at their actual theorem statements and parameter analyses. The theorem-use exclusions above are algebraic/cost checks, not conjectures about factoring hardness and not an exhaustive impossibility result. No heuristic number-theory premise is used.

The fast Abelian-number-field norm literature was also located (Bernstein, *Fast norm computation in smooth-degree Abelian number fields*, DOI 10.1007/s40993-022-00402-0, [primary ePrint](https://eprint.iacr.org/2022/980.pdf)). Its specialized field/tower setup must be acquired and its dimension and element size charged. It does not directly identify the present selected products as a norm in such a supplied smooth-degree Abelian field. The constructive-frontier index already flags related fixed-weight norm consumers, so this source is not being proposed as a fresh acquisition result.

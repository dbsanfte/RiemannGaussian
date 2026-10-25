# Shared recurrence products: an initialized quadratic-state cut

24 October 2026. Scratch research; no repository changes. The concrete attempt below compresses a universal block product on the actual quadratic initial-state surface. It is executable and zero-safe, but its final contraction returns the already paid rectangular bound, not the requested soft-k endpoint. The primary theorems checked here do not supply that missing contraction.

## Input and preserved recovery contract

Use `frobenius-pairing.md`, SHA256 `215f1fd452452ce0719ff4b88b81f74b69c8a88dc12d80c8bb63a81d11e2e363`, and `shared-recurrence.md`, SHA256 `654218a0e5dde8e0261ea662cf40c8ceb82e5e152cebebb4542b831f0b322562`, in `/tmp/semiprime-recurrence-closure-20261024/`.

R=Z/N, B=R[tau]/(tau^2-D) has constant rank two and explicit conjugation. The actual targets V_j and unit seed z are acquired in soft k; J<=k, H=k^2 and L=2H+2. Put t=Norm(z), s=Tr(z). Every z^d-1 for 1<=d<=16H is a certified unit. Targets need not be separated and may repeat. The starts of ALL rows and the common monic recurrence are acquired in soft k:

    h_j(i)=Norm(V_j-z^i)
          =Norm(V_j)+t^i-bar(V_j)z^i-V_j bar(z)^i,
    C(T)=(T-1)(T-t)(T^2-sT+t).

The query is E=prod_(j,i<L) h_j(i), with row and interval restrictions. Its unrestricted zero is guaranteed and does not itself find a factor. For a nonunit restricted product, localize to ONE original leaf before invoking the predecessor's paired identity. That identity supplies a factor or the original bounded beta witness even at a saturated leaf; it does not require a large order for W. Nothing below replaces this consumer by an arbitrary recurrence zero oracle.

## 1. Concrete cut: universal products on the initial-state surface

Try to precompute a universal block polynomial once and evaluate it at many row states, rather than advance every row separately. Avoid diagonalizing C: over B introduce independent formal X,Y and define

    P_b(X)=prod_(0<=i<b)(X-z^i),
    K_b(X,Y)=prod_(0<=i<b)(XY+t^i-X bar(z)^i-Y z^i).

Here XY is the norm coordinate of the initial state, not a fourth unrelated free parameter. Direct factorization proves the exact identity

    K_b(X,Y)=P_b(X) bar(P_b)(Y).                         (1)

Thus the seemingly bivariate block has bidegree (b,b), but its coefficient matrix is an outer product. Both univariate factors, including every coefficient, are acquired in soft b by a monic product tree on the b acquired geometric nodes. No eigenvector or Vandermonde inverse, no division by h_j(i), and no assumption of distinct spectral bases is involved. Substituting X=V_j,Y=bar(V_j) gives the actual length-b row product. A single block for ALL J rows costs soft(b+J), by monic multipoint evaluation of P_b followed by norms. This is a useful initialized compression of the common-recurrence block; a generic four-start polynomial representation would miss (1).

Now actually contract all time blocks. Write L=rb+d, 0<=d<b. For block index a, its start is u=ab, and

    prod_(i=0)^(b-1) h_j(ab+i)
       =t^(ab^2) Norm(P_b(z^(-ab)V_j)).                 (2)

Consequently the full-block product is

    E_full=t^[J b^2 r(r-1)/2]
           Norm(prod_(a=0)^(r-1) prod_j P_b(z^(-ab)V_j)). (3)

The phase in (3) is known and unit. Initialize z^(-b), then all Jr actual nodes z^(-ab)V_j; evaluate ONE acquired P_b at those nodes with a monic remainder tree and multiply the answers. This costs soft(b+Jr). A length-d final block costs soft(J+b), with the same formula and acquired shifted targets. Include the soft-J product tree for any chosen row restriction. Total:

    soft(J+b+JL/b),

optimized at b approximately sqrt(JL), giving soft(J+sqrt(JL)). At b approximately sqrt(L), universal-block initialization fits the desired scale, but the executed contraction still contains Jr approximately J sqrt(L) nodes.

There is also an exact scalar resultant formulation, not a remedy hidden behind those nodes. Let

    R_r(X)=prod_(a=0)^(r-1) z^(-abJ) F(z^(ab)X),
    F(X)=prod_j(X-V_j).

R_r is monic of exact formal degree Jr and roots z^(-ab)V_j. Therefore the inner product in (3) is Res(R_r,P_b). Acquiring this explicit R_r or its full root tree costs soft(Jr). A coefficient-vector resultant routine cannot treat its implicit product description as already acquired. This is not a lower bound on another scalar-only routine. It identifies the precise remaining operation for this attempted compression: scalar contraction of a separably represented universal block against all scaled row states, with restrictions. After specialization, this cut coincides with the paid rectangular query; it is not a new endpoint algorithm or a novelty claim about rectangular blocking.

All formulas survive zero factors, repeated V_j and repeated eigenvalues of C. Monic remainder trees are valid over B even if target differences are nonunits. Their scalar norm products retain exact original row/block labels. Refinement to a single leaf uses the same algorithm on smaller row/interval restrictions, then the established saturated decoder. No endpoint is divided out.

## 2. Does an amortized evaluation theorem pay the contraction?

**van der Hoeven–Lecerf, author preprint, 14 March 2020, Theorem 8.** [Fast amortized multi-point evaluation](https://www.texmacs.org/joris/amp/amp.pdf) works over a field. For d hereditarily generic points, its evaluation-tree construction costs O(d^omega); given that tree, and with each rectangular support bound pi_i at least the source axial bound delta_(d,i), evaluation of a polynomial with support size pi=product_i pi_i costs O(M(d)log^3 d+M(pi)log^2 pi). It also requests a supplied element of multiplicative order at least (n+1)!pi for n variables. Remark 9 gives faster *expected* preprocessing in a bivariate case with extra hypotheses, still not linear initialization. These are explicit preprocessing bounds, not an oracle for implicit structured points.

Application ledger: use n=2 and the point pairs (z^(-ab)V_j,bar(z)^(-ab)bar(V_j)); the literal count is d=Jr and dense K_b support size (b+1)^2. These pairs need not be hereditarily generic. The native unit screen is not a proof that their multivariate evaluation matrices are invertible. B itself can split locally and is not a field. Moving the argument to unknown hidden fields is unauthorized; elimination over R would require certified unit pivots and still incur its actual preprocessing. Even if a valid tree were supplied, its theorem outputs d values; it gives no product-only contraction theorem. Identity (1) already provides a better executable implementation here than the dense bivariate call.

**Harvey–Sutherland, 2014, Theorem 4.1.** [Computing Hasse–Witt matrices of hyperelliptic curves in average polynomial time](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/5B804435BD9D57CBCFB1D0C4949D7B36/S1461157014000187a.pdf/computing-hassewitt-matrices-of-hyperelliptic-curves-in-average-polynomial-time.pdf) bounds an accumulating remainder tree for b explicit integer r0-by-r0 matrices. If B0 bounds the bit length of the product of the moduli, h bounds entry/modulus bit lengths, and B1 bounds the initial vector, assuming log r0=O(h), its time is O(r0^3 M(B0+bh)log b+r0 M(B1)). This extra hypothesis is automatic for r0=4 here. The matrix and modulus data enter the bound. This is amortization across many modular prefix products, not sublinear processing of an implicit long sequence.

Application ledger: the common 4-by-4 companion matrix transports each row linearly and can be powered cheaply, but the desired prefix product is not a coordinate of that four-dimensional state. Appending p(i+1)=p(i)h_j(i) gives a nonlinear update, outside this theorem's matrix input. Linearizing via the initialized polynomial K_b leads to (1), then the paid contraction (3); it does not produce a constant-size acquired transfer for the accumulator. Encoding the actual Jr evaluation tree as explicit data likewise pays Jr. This is a limitation of this application, not a general impossibility claim for recurrence products.

**Bostan–Schost, 2005, Section 5.** [Polynomial evaluation and interpolation on special sets of points](https://mathexp.eu/bostan/publications/BoSc05.pdf) gives fast geometric evaluation and basis conversions, with near-linear polynomial-multiplication cost in the explicit degree/number of points, over a field with the relevant distinctness assumptions. These are linear evaluation maps; the theorem does not evaluate an implicit product-only tensor norm in time independent of its point count. Its geometric operations can support our short polynomial construction; our actual composite-ring evaluation uses monic remainder trees instead of importing unchecked interpolation inverses.

For the whole-row product g(i)=Norm(F(z^i)), the known coefficient outer product f_a bar(f_b) has (J+1)^2 labeled bases z^a bar(z)^b. Treating a multivariate evaluator's dense coefficient vector as this compressed outer product is also a change to its input contract. The initialized common-family annihilator has formal degree (J+1)^2; its starts are not paid merely because each individual row has four starts.

## 3. Rectangular matrix multiplication: an intermediate-exponent check

A specific primary theorem is Nüsken–Ziegler, [Fast Multipoint-Evaluation of Bivariate Polynomials](https://arxiv.org/abs/cs/0403022), Result 4 (June 2004 version). Over a field, a coefficient-vector polynomial of partial degrees <n,<m can be evaluated at M points with distinct first coordinates in O((M+nm)m^(omega2/2-1+epsilon)) operations, for each fixed epsilon>0; omega2 is the exponent for multiplying an a-by-a matrix by an a-by-a^2 matrix. The hypothesis is not merely distinct points as pairs. Its ring-safe Theorem 3 has a different, cubic bound in the balanced degree parameter.

Two complete parameter substitutions do not improve the covered query. First, evaluate f(X)bar(f)(Y) at (z^i,bar(z)^i), i<L. Here n=m=J+1, M=L, and acquiring the dense coefficient vector costs soft J^2. The estimate is (L+J^2)J^alpha, alpha=omega2/2-1+epsilon. Even substituting the ideal rectangular exponent omega2=3 leaves order k^(5/2+epsilon), rather than k^(3/2). Distinct first-coordinate differences are certified by the short z screen, but this does not turn B into a field; the numerical comparison already fails before that extra applicability issue.

Second, evaluate the universal K_b at the Jr scaled row pairs from (3). The dense theorem has nm=(b+1)^2, M=Jr and cost approximately (b^2+JL/b)b^alpha. With alpha=1/2 (optimistically omitting epsilon), balancing the two terms uses b approximately (JL)^(1/3), and the estimate is (JL)^(5/6), or k^(5/2). It also lacks certified first-coordinate differences for these row pairs. Exploiting the rank-one coefficient matrix instead gives our better monic univariate evaluation, but that is exactly soft(b+JL/b), not a rectangular-matrix shortcut to its product only. These comparisons are assessments of displayed theorem guarantees, not complexity lower bounds.

Thus these specific multievaluation/matrix-product adaptations certify neither a soft-k query nor any intermediate exponent below 3/2. A k^(1+o(1)) multivariate bound would not by itself be a soft-k bound, and a dense-input theorem still has to acquire its coefficient vector and points. No claim that all possible rectangular-matrix adaptations fail is made.

## 4. What remains to test

The useful target exposed by (1)--(3) is an exact restricted scalar contraction algorithm for

    prod_(a<r) prod_j P_b(z^(-ab)V_j),

given only the two degree-b factors of K_b, the O(J) quadratic targets, and geometric block step. Such a routine must charge initial point/ideal data, work over the composite quadratic algebra without hidden-field inverses, and preserve restriction labels. Proving a soft(J+b+r) contraction for these actual native targets would advance acquisition. None of the primary results above proves it, and this report does not assume it. The universal-state cut saves the false b^2 block representation, but not the remaining Jr contraction. The complete covered query and factoring exponent remain unchanged.

## Cached primary-source pins

The following exact PDFs were fetched and converted to searchable text in `sources/` beside this report; SHA256 values:

- `amortized.pdf`: `f025997d312ef3037a74d4c3a88854ed3a7bfc10e3a8cb4e2fe780920ecb1f55` (the linked March 2020 preprint, not an assumed later theorem).
- `harvey-sutherland.pdf`: `5e8ce8d0207260506e057cb4a0d970bbdfe9c6bd897366089cf4648898c2b770`.
- `special-points.pdf`: `257beedc4a433fe5ebf5a8abc8db98e057e708c3e862140af6ea90d1874a9aa9`.

- `nusken-ziegler.pdf`: `e27343f0c1d81d05099a46ef61cb6cf1e6a7f3387dd162c04ee54d272445e94a` (arXiv PDF, June 2004 version).

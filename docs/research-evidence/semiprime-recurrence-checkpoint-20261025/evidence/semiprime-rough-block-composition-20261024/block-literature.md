# Rough torus input and a paid constant-width block/norm attempt

24 October 2026. Scratch only. This report executes the bounded-width ideal route over its actual coefficient algebra, and audits a current primary thin-matrix lead against explicit native matrices. Neither yields a saving below the covered soft-k^(3/2) query. No new endpoint theorem is asserted from a generic operation bound.

## 1. Acquired strong input and exact query

The actual rough supplier is `/tmp/semiprime-large-order-recurrence-20261024/rough-torus-working.md`, SHA256 `6333f318c8bc1c1e88a398aaeff94efb83b0d2e6ead3d64d455317b41036dcda`, with independent review SHA256 `c75d40a2873f4b9b24db438e36b79d19be158b48c3ab5f4d606f12f2e1ad7ebf`. It returns a factor or norm-one W with BOTH local orders k-rough and ord_p(W^H)>C=16k^2, H=k^2. These are actual deterministic soft-k preparations, not a hypothetical order oracle. They do not assert cross-prime coprimality or N+1-projection survival.

Use the actually rebuilt beta-coupled rows V_j and the actually rescreened seed z=(beta W)^H in B=(Z/N)[tau]/(tau^2-D). Their original own-row cover and same-original-leaf saturated beta decoder remain available. There is one unknown nonsplit field side; B has constant rank over R=Z/N. Every z^a-1 for 1<=a<=C is a certified unit. Targets have actual coordinates, native E_j=N+delta_j, delta_j in [-3H,H], J=O(k), and Norm(V_j)=beta^(2E_j).

The controlled public modulus and ideal preparation are pinned in `/tmp/semiprime-quadratic-ideal-20261024/ideal-literature.md`, SHA256 `90f760d067f9de61a2950289c4f8aceba013cba521a2e4078053c2c2916ef77b`, reviewed at `b922249b3fa55c5db826a8f86c2019f05ed49b0e41628198721e1c29b0924b1b`. Exact global target duplicates can be removed with labels; a derivative certificate gives a factor or unit-separated targets in soft J. Each exact norm/delta fiber has at most 16 native tags. Its actual norm node n_d=beta^(2E_d) is unit-separated from other norm nodes. All bounded-width coefficient vectors below are therefore paid in soft k. For the full unit-tag family the number of norm fibers is Theta(k), not a fixed constant.

The covered query is

    E=prod_(i<L) prod_j Norm(V_j-z^i), L=2H+2,

with original row/index restrictions. Only a supplied nonunit ORIGINAL leaf gets the existing saturated decoder. Arbitrary ideal residuals and intermediate matrix entries are not witnesses by themselves.

## 2. Concrete algorithm: constant-width q-product over the norm-fiber algebra

Partition the norm fibers by their retained cardinality r, 1<=r<=16. Let D_r be that group, m_r=|D_r|. Acquire

    G_r(T)=prod_(d in D_r)(T-n_d),
    Phi_r(T,U) in B[T,U],
    degree_T Phi_r<m_r, degree_U Phi_r=r,
    Phi_r(n_d,U)=prod_(j in fiber d)(U-V_j).

Each Phi_r is MONIC in U. Its r lower coefficient functions are explicitly interpolated in T, with certified derivative inverses. This partition avoids pretending that a variable-degree fiber polynomial has a unit leading coefficient after padding. Total coefficient storage and acquisition is O(sum_r r*m_r)=O(J); all starts are actual. Empty groups are skipped.

Set A_r=B[T]/G_r(T). It is an acquired free coefficient algebra of rank m_r over B, with monic reduction and known CRT norm nodes. Multiplication in A_r costs soft m_r base-ring operations. A scalar B multiplication/addition of a general represented A_r element also touches its m_r coordinates; it is not a unit-cost B operation.

The desired B-valued product factors exactly as

    Z_r(T)=prod_(0<=i<L) Phi_r(T,z^i) mod G_r(T),
    E=Norm_(B/R)( prod_r Norm_(A_r/B)(Z_r) ).          (1)

Indeed Norm_(A_r/B)(Z_r)=prod_d Z_r(n_d), hence it is precisely the product of (z^i-V_j) over the retained rows. The final B norm removes its harmless signs. This is an executable fixed-width formulation of the covered family, not a substitute family chosen for convenient geometry.

### Execute every block and every coefficient

For 1<=b<=L construct in A_r[X]

    B_(r,b)(T,X)=prod_(0<=v<b) Phi_r(T,z^v X).

It has exact X-degree rb because every factor is monic in U up to a known unit z^(vr). All rb+1 coefficient elements are acquired. Binary products, with monic T reduction, cost soft(m_r*r*b): bivariate polynomial multiplication can be done by Kronecker substitution followed by coefficientwise monic G_r reduction. The needed z powers and coefficient scalings are included.

Write L=ab+d, 0<=d<b. Evaluate that one block polynomial at X=z^(b h), 0<=h<a, by monic multipoint evaluation over A_r, and multiply the values in A_r. Acquire/evaluate the exact tail block of degree rd at X=z^(ab). This uses no endpoint inverse and no inversion of a target or geometric-node difference. The actual cost for group r is

    soft(m_r*(r*b+L/b+1)).                            (2)

The scalar norm at the end is also paid: evaluate the acquired degree<m_r representative Z_r at ALL known n_d by monic MPE, multiply, then take the rank-two B norm. This costs soft m_r. It assumes neither a hidden factorization of G_r nor a field structure for A_r.

Because r<=16 and sum m_r=Theta(k) for the full controlled family, balancing (2) at b approximately sqrt L gives soft(k sqrt L)=soft k^2. The whole attempt is correct and initialized, but worse than the preserved query. Fixed U degree has not made the growing norm-coordinate algebra constant rank.

### Change the order of norm and blocking

Taking the A_r norm FIRST is cheap here for a concrete reason: the original roots are already acquired. Build

    F_r(U)=prod_(d in D_r) prod_(j in fiber d)(U-V_j)
          =Norm_(A_r/B)(Phi_r(T,U))

by the actual root product tree, in soft(r*m_r); no generic polynomial resultant oracle is needed. Multiplying the F_r gives monic F(U) of degree J. Now a block prod_(v<b)F(z^v X) has degree Jb, and all its coefficients plus its L/b geometric values cost soft(Jb+L/b+J). Choosing b approximately sqrt(L/J) gives the existing soft(J+sqrt(JL)) bound, with the usual short direct branch if a parameter is small. This is the retained covered baseline, not a new use of the large rough orders.

Partitioning norm fibers into groups of h fibers does not improve this tested ledger: norm-first completion per such group costs soft(sqrt(h L)) up to the constant fiber width, and M/h groups cost soft(M sqrt(L/h)). This displayed upper-bound expression is smallest at the fully aggregated h=M, giving the baseline. Norm-last completion remains soft M sqrt L. These are comparisons among the executed choices, not a lower bound on another fused scalar-norm algorithm.

### Restrictions and zero-safe witness

For a row subset rebuild its fiber polynomials; the width is still <=16 and its actual degree is charged. For an interval [u,u+ell), replace Phi_r(T,U) by Phi_r(T,z^u U) in the block construction, retaining the global original indices u+i. Its leading coefficient is a known unit. Consequently (1)--(2) support all required restrictions. A nonunit scalar norm product is localized through the retained fiber/row/index product structure to one ORIGINAL V_j-z^i; then use the established same-leaf decoder. No cross-leaf pairing, division after a zero, or decoder for a norm-algebra coefficient is introduced.

The missing faster operation is now precise: a product-only or zero-support-only Norm_(A_r/B) of a constant-U-degree q-product, over an explicitly acquired rank-m_r norm algebra, WITHOUT paying m_r coordinates at each of sqrt L stages, and still supporting these original restrictions. That interface is not supplied merely by the paid width-16 ideal or by W's rough orders. The roughness is a genuine input property but this attempt does not exploit it to contract the coefficient algebra.

## 3. Primary batching theorem: many indices are not many parameters

[Bostan–Yurkevich, Fast Computation of the N-th Term of a q-Holonomic Sequence and Applications](https://yurkevi.ch/data/Alin%20Bostan%2C%20Sergey%20Yurkevich_2020_Fast%20Computation%20of%20the%20N-th%20Term%20of%20a%20q-Holonomic%20Sequence%20and%20Applications.pdf), April 2022 author version: Theorem 6 simultaneously computes up to sqrt N selected terms of ONE fixed q-holonomic sequence, in soft sqrt N field operations when order/degree are fixed. Its refinement reuses common block polynomials and evaluates them at known q^index shifts. The discussion after Corollary 7 retains growing recurrence degree/order parameters; Theorem 5 has the familiar sqrt(Nd) degree dependence. These are not a theorem for J independently parameterized Pochhammer symbols at a common horizon.

For (1), fixed r<=16 allows a short-degree q-product over A_r, but one A_r operation must be paid at rank m_r. Multiple endpoint terms over this coefficient algebra do not eliminate that cost, and the native V_j are not supplied as known bounded shifts of ONE scalar seed parameter. Equality to z^i at a hidden local hit is the query, not an acquired shift label. The explicit monic construction above establishes the ring-safe constant-degree algorithm without applying a field theorem blindly to A_r. Thus this stronger batch-index primary result still gives no new acquisition bound here; it is not presented as new literature superseding the already audited q-holonomic baseline.

[Johansson, Evaluating parametric holonomic sequences using rectangular splitting](https://fredrikj.net/math/rectangular_splitting.pdf), ISSAC 2014, Theorems 2--3, distinguishes coefficient operations, scalar operations in an extension algebra, and nonscalar extension multiplications. Its sqrt N nonscalar bound is accompanied by O(N) scalar operations and explicitly charged coefficient construction; matrix size and polynomial degrees are fixed in that claim. It is about polynomial-in-index holonomic recurrences, not directly our geometric index. The counted-cost distinction is relevant: even a hypothetical transfer of only its nonscalar count would not make a growing rank-m_r algebra free. We do not invoke it as a q-product theorem.

[Bostan–Schost, Polynomial evaluation and interpolation on special sets of points](https://mathexp.eu/bostan/publications/BoSc05.pdf), Section 5, explains fast explicit geometric evaluation. It is a linear evaluation map with the polynomial degree and point count charged, not a product-only implicit resultant contraction. The ring implementation of Section 2 uses monic remainders instead of importing field interpolation inverses. None of these primary results supplies the missing scalar norm operation just identified.

## 4. Current thin-matrix lead: actual theorem and native input sizes

The primary arXiv identifier in the new lead resolves to [Alman–Vassilevska Williams, Truly Subquadratic 3SUM and Truly Subcubic APSP via Triangles in Sparse Lopsided Graphs](https://arxiv.org/abs/2610.06783), v1, submitted 5 October 2026. Its title is not exactly “...via Thin Matrix Products.” Theorem 1 (and data-structure Theorem 3) concerns explicit S-by-D and D-by-S integer matrices, entries of polynomial size, D<=S^(1/18), and at most S^2/sqrt D requested output positions. It states time/preprocessing O(S^2/D^0.063); the query variant uses O(D^0.437) per entry. Only this matrix-input contract is used here; no 3SUM/APSP reduction is imported as a native query algorithm.

There is a legitimate native bilinear matrix, so test it rather than appealing to thinness abstractly. For one cardinality group the actual fiber coefficient matrix is

    C[d,a]=[U^a]Phi_r(n_d,U), 0<=a<=r,
    Y[a,i]=z^(a i), 0<=i<L.

Its product entry is the actual factor Phi_r(n_d,z^i). The inner dimension r+1<=17 is CONSTANT, so the theorem's denominator yields no polynomial exponent saving as k grows. The rectangular right input has (r+1)L entries, already order L, and explicitly writing all M L native factors is worse. Padding to a large square outer dimension does not improve this input ledger. This is an exact reduction to leaf values; it is not a reduction of their product to a small subset of bilinear entries.

Blocking makes the issue explicit at variable inner dimension. After a length-b block, the corresponding coefficient matrix has M rows and D=rb+1 columns, while the clock matrix has D rows and approximately L/b columns, with entries z^(a b h). Its explicit right input has Theta(L) slots for fixed positive r, independently of b; its acquired left input has Theta(Mb) slots before any extra sparsity theorem. These are precisely the coefficients/states charged in Section 2. At b approximately sqrt L and M approximately k, D is of order k, whereas an unpadded square with outer dimension of order k would require D<=k^(1/18). Splitting or padding does not furnish a cheaper bound than the already faster monic geometric evaluation, nor does it supply the unacquired block coefficients. A compressed-clock entry oracle is a different input contract, and the scalar product is not an output entry of these matrices.

The modular domain is NOT the decisive obstruction for this particular theorem. Lift R residues to polynomial-size nonnegative integers; exact integer XY can be reduced modulo N afterward. For the natural outer dimensions S>=k used above, with S polynomial in k and N<=k^6, these lifted entries have O(log S) bits. A B product can be implemented by a constant number of scalar coordinate matrix products with the known quadratic-discriminant multiplication in the final reconstruction. This route needs no inverse of a potentially nonunit ring value and is zero-safe. It nevertheless retains the actual input/preprocessing/output costs above. No hidden JL entry table, no reduction from a product of factors to a bilinear sum, and no useful sparse requested-position set for the terminal norm has been acquired.

Thus the genuinely current thin-product primary result does not, under these literal initialized reductions, improve the endpoint or any intermediate exponent below 3/2. This does not rule out another correct native reduction to its sparse-output interface. Such a reduction would have to specify the actual small matrices, requested positions, input generation and original restriction witness; it is the missing mathematical step, not a consequence of the theorem alone.

## 5. Exact outcome and source pins

The bounded-width ideal was fully used to form a fixed-degree q-product over an actual rank-M coefficient algebra. Its completed norm-last cost is soft k^2; norm-first gives the existing soft k^(3/2) completion. The stronger rough torus supplier has not itself reduced that rank or produced a finite query automaton. No source, shared journal or integrating packet was edited. No finite examples, performance campaign, lower bound on all algorithms, or factoring-rate claim is made.

Cached exact primary PDFs in `sources/`:

- `qholonomic.pdf` (April 14, 2022 author version): SHA256 `718904c094b78a76732fc7ca3959129c6996fd2689a251f580e20c2af91919fd`.
- `rectangular-splitting.pdf`: SHA256 `6adc15dab947c15832c2c53046ee9dfd62ae1d6fcbd44ae40dcfd8f019b7f7ee`.
- `special-points.pdf`: SHA256 `257beedc4a433fe5ebf5a8abc8db98e057e708c3e862140af6ea90d1874a9aa9`.
- `thin-products-2610.06783.pdf` (v1): SHA256 `d91a79c5dbf1fc662f0c5c1bb2b690ac3d83d9ef5bf872bde4cdaf7cc9e76005`.

The earlier Vienna-hosted q-holonomic PDF returned HTTP 503 on this pass; the author's current yurkevi.ch copy above was fetched and pinned. No theorem is based on an unacquired PDF.

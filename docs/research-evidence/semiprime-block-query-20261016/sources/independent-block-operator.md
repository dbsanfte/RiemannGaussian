# A paid nearlinear block-coefficient operator, with the diagonal contraction still separate

2026-10-15. Positive exact subroutine over Z/N. No whole-row query algorithm or lower bound is claimed.

Let c_k=[t^k]P_L(t;q), let B>=1, H=floor(L/B), and C_(n,s)=c_(Bn+s) for 0<=n<=H, 0<=s<B, setting c_k=0 for k>L. Assume every 1-q^k with 1<=k<=L+B is a unit. The actual retained source satisfies this when L<=4m² and B=Theta(m), since both local prime orders exceed 16m². Define X_n=q^(Bn), a=q^L and

 R_s(X)=product_(r=0)^(s-1)(a-Xq^r)/(1-Xq^(r+1)).

Then C_(n,s)=c_(Bn)R_s(X_n), including the terminal zero entries. The first zero numerator after k=L makes the continued rational recurrence zero, while the promised denominators remain units.

## Explicit common-setup algorithm

Given a scalar weight vector v of length B, compute f(X)=sum_s v_s R_s(X) as ONE rational function with degree-O(B) numerator and denominator, by a balanced product tree. For an interval [l,r), let

 U_[l,r)=product_(h=l)^(r-1)(a-Xq^h),
 V_[l,r)=product_(h=l)^(r-1)(1-Xq^(h+1)),
 f_[l,r)=sum_(s=l)^(r-1) v_s product_(h=l)^(s-1)(a-Xq^h)/(1-Xq^(h+1)).

Represent f_[l,r)=A_[l,r)/V_[l,r). The leaf numerator is A_[l,l+1)=v_l V_[l,l+1). Merge at midpoint p using

 A_[l,r)=A_[l,p) V_[p,r)+U_[l,p) A_[p,r).

This is an exact polynomial identity over any commutative ring. Products and merges cost soft O(B); an extra cancellable last denominator factor is harmless. The root numerator and denominator have degree at most B.

Evaluate both at X_0,...,X_H with monic remainder trees. Repeated points cause no problem. Every V(X_n) is a product of 1-q^k with k<=L+B, so batch inversion is legal under the unit promise. Multiply f(X_n) by the seed c_(Bn). The seeds at the H+1 supplied public indices are acquired by the existing shared selected-coefficient algorithm in soft O(sqrt L+H) ring work. Public q powers, product-tree construction and the evaluation cost soft O(B+H), with logarithmic powering overhead. Hence setup and one C*v cost

 soft O(sqrt L+B+H)

ring operations and comparable residue storage. At B~sqrt L, H~sqrt L this is soft O(sqrt L), genuinely the desired subroutine scale. No row value, node difference, factor or local order is inverted or supplied. Unqualified denominator gcds require the normal factor-aware contract; gcd N is not an inverse.

Once fixed product trees, points, unit denominator inverses and seeds are prepared, every operation on v is linear: multiplication by fixed polynomials, addition, monic remainder/evaluation, and diagonal scaling. Transposing this linear straight-line circuit gives C^T*w at the same soft complexity. Tellegen transposition here uses only the already paid fixed coefficients; no input-dependent division or field-pivot assumption is hidden. Restricting selected block rows or using a subset of coefficient columns preserves the paid setup bound. Bit cost is the ring-operation bound times soft log N, including the public index/exponent bit lengths (O(log L) on the intended branch).

## Why this does not yet perform the Cartier contraction

For the decimation mask E_B, let y_j=z_j^B and e_j=E_B(z_j)/B. Its polyphases satisfy

 E_(B,s)(y_j)=e_j z_j^(-s).

After actual-source deduplication, the y_j differences are units. Thus the matrix of polyphase polynomial coefficients factors as a Vandermonde-type matrix W_(s,j)=z_j^(-s), a diagonal e_j, and inverse evaluation at the y_j. This supplies fast scalar matrix-vector operations after the paid transport metadata. It does not make the product with C an ordinary single matrix-vector query.

The mixed evaluation kernel is

 sum_(s=0)^(B-1) R_s(X_n) y^s.

For free y this is a finite basic-hypergeometric partial sum. Evaluating it simultaneously for the J actual y=z_j^(-1), then taking the required coefficient antidiagonals/carry shifts, is an additional operation. The resulting output has O(J) coefficients, but neither two fast scalar operators nor their transposes alone supplies that diagonal contraction at the same cost.

The exact column relation for C is

 C_(n,s+1)-q^L C_(n,s)
   =X_n q^s (q C_(n,s+1)-C_(n,s)).

This is a useful rational-Newton pencil structure. W instead converts the column shift into multiplication by its node y. A compatible low-rank displacement for their MIXED product, and a paid diagonal-extraction theorem, must still be exhibited. No assertion is made that such structure cannot exist. In particular, arbitrary matrices with fast products need not be used as black boxes here; their explicit structure may yet yield a positive algorithm.

## Primary scope

Bostan--Lecerf--Schost, Tellegen's Principle into Practice (ISSAC 2003), section 3, gives the transposition framework and systematic fast polynomial applications: https://mathexp.eu/bostan/publications/BoLeSc03.pdf . The self-contained straight-line construction above specializes it to this ring-safe scalar operator.

Bostan--Jeannerod--Mouilleron--Schost, On Matrices With Displacement Structure: Generalized Operators and Faster Algorithms (SIAM J. Matrix Anal. Appl. 38 (2017), 733--775), https://mathexp.eu/bostan/publications/BoJeMoSc17.pdf , studies fast operations from supplied displacement generators over a field, including products with multiple right-hand sides. It does not state that arbitrary compositions of fast operators automatically admit a constant-rank compatible generator or that every coefficient antidiagonal is obtainable by one matrix-vector multiplication. A composite-ring application also needs the actual invertibility contracts; no field structured solver is imported here.

Both primary PDFs/texts were downloaded and inspected. Their hashes and the previously paid selected-coefficient prerequisite are pinned in block-operator-manifest.json. The new positive result is the nearlinear C and C^T primitive with paid setup; the mixed Cartier contraction remains the acquisition problem.

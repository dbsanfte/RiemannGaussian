# Finite geometric Christoffel determinant: initialized boundary test

2026-10-24. Scratch only; no repository edits, examples or Lean work. This tests one concrete determinant route. The moment and displacement data can be initialized, but the completed determinant computation here retains the existing soft(J+sqrt(JL)) clock. No soft(J+sqrt L) algorithm or generic lower bound is obtained.

## Prior boundary read first

This is NOT a new Christoffel reformulation. Read:

- direct-frontier.md, SHA256 eba769360060996c82fc354bb2e4f3c819d0e90a2b5b9d6779f9c8e9a1fcfcb5: the full-support monic orthogonal polynomial is already identified with the grid polynomial; the small alternant retains its unpaid evaluations.
- /tmp/semiprime-cayley-acquisition-20261022/structured_matrix/report.md, SHA256 cc92c584fb06a7a88f844e58cec0438c13d061f9ab7b66a1be1cd6ba69873039: cheap low weighted moments, full-L Gram identity, failure of a small Gram determinant to retain every hit, and already stronger selected-q-coefficient access.
- /tmp/semiprime-scalar-native-20261023/scalar-factorial-constructor.md, SHA256 d0167c9f1fda092365f22077618e9747363ff5ce6aed303ef44331a12f1bf3fb: exact J-by-J Toeplitz/Schur scalar determinant whose far boundary is unpaid; direct scalar determinant contraction remains open.
- parameter-charlier.md, SHA256 5f59aa34e578123ce8acaadbcfbfbe0a3d4ea78baf188aeb9a0cc124541e25b7: the parameter-N Charlier list construction is a different paid polynomial-family query; it does not supply the finite geometric grid boundary here.

The following derives the exact ring-safe identities and explicitly tests acquiring their compatible data. It does not count those inherited identities as new rate progress.

## Actual source and full-support determinant

Use the ORIGINAL scalar native query over R=Z/N, with acquired monic F(X)=product_(j=1)^J(X-Y_j). The Y_j are units with unit pairwise differences. Let x_i=q^i, 0<=i<L, with all 1-q^k for 1<=k<=2L+J certified units by the inherited order guard (this range fits <16m^2 on the native scale). Empty dimensions return the appropriate empty product directly. The desired scalar is

    E_L=product_(i=0)^(L-1) F(x_i).

A shifted native interval replaces x_i by q^a q^i and leaves all arguments and costs below valid.

Define unweighted and weighted moments

    mu_n=sum_i x_i^n,
    nu_n=sum_i F(x_i)x_i^n=sum_(k=0)^J f_k mu_(n+k),

and full L-by-L Hankel matrices H_1=(mu_(r+s)), H_F=(nu_(r+s)). With V_(r,i)=x_i^r,

    H_1=V V^t,
    H_F=V diag(F(x_i)) V^t,
    det(H_F)=det(H_1) E_L.                         (1)

The seed Vandermonde V is invertible because its pairwise differences are units. Thus det(H_1) is a certified unit even at target hits, while H_F is SINGULAR at those hits. Inverting H_F, its target determinant, or a collision value is never licensed by (1).

The normalizer is explicitly

    det(H_1)=Delta^2,
    Delta=q^binom(L,3) product_(k=1)^(L-1)(q^k-1)^(L-k).

This is a known unit PRODUCT FORMULA, not a free numeric scalar. Direct acquisition costs soft L (generate powers and all factors, then signed integer powers); at L~m^2 this exceeds the target clock. For a factor/nonunit query its numeric value can be avoided: (1) preserves support using the certified unit property alone. This avoids an unnecessary normalization cost, but does not acquire det(H_F).

## A cheap moment formula and its full initialization

For n>=1,

    mu_n=(1-q^(nL))/(1-q^n),  mu_0=L.

Generate q^n and (q^L)^n to n=2L+J-2, batch-invert only the certified denominators 1-q^n, and cross-correlate the mu list with the acquired f_k. This actually acquires every required nu_n in soft(L+J) residue work and O(L+J) storage. Numerator nonunits are retained; no numerator is inverted. For only O(J) moments this costs soft J, as already frozen in the prior packet.

The full target matrix has rank L-c_p over each hidden field, where c_p is the number of hit seeds: V is invertible and its diagonal weight matrix has exactly c_p zero entries. Since c_p<=J, the ordinary moment rank is almost L, NOT the small hit count. This repeats the existing full-Hankel-rank distinction, not an operation lower bound.

For a d-by-d weighted Gram determinant with d<L, Cauchy-Binet instead gives

    det(nu_(r+s))_(r,s<d)
      =sum_(S subset seeds, |S|=d) Delta(x_S)^2 product_(i in S)F(x_i).

A hit deletes only terms containing that seed. Hence the cheap d=O(J) moments do not supply a determinant in which every original hit is a factor. Replacing full L by J silently changes the detector.

## Exact compact displacement, and what its compatible generators cost

There is a genuine short rational descriptor, which can be initialized without the full moment list. Set

    A(X)=product_(k=0)^J(1-q^k X),
    P(X)=sum_k f_k A(X)/(1-q^k X),
    Q(X)=sum_k f_k q^(Lk) A(X)/(1-q^k X).

Here the displayed divisions are EXACT polynomial quotients by explicitly included factors; they are acquired by rational-addition/product trees, with no inversion of 1-q^k X at a target argument. A,P,Q cost soft J, including the short power lists; deg A=J+1 and deg P,Q<=J. For every n>=0,

    A(q^n)nu_n=P(q^n)-q^(Ln)Q(q^n).                (2)

At n=0 the k=0 quotient is removable: both sides of (2) are zero, so the equation does NOT determine nu_0. That known value must remain supplied separately; no inversion of A(1)=0 is legal.

Let D_q=diag(1,q,...,q^(L-1)), A(X)=sum a_k X^k. Equation (2) gives the exact generalized displacement

    sum_k a_k D_q^k H_F D_q^k
      =sum_(t=0)^J p_t v_t v_t^t
        -sum_(t=0)^J q_t v_(L+t) v_(L+t)^t,
    v_t=(1,q^t,...,q^((L-1)t))^t.

Its right side has rank at most 2(J+1). There is no hidden low-rank moment assertion here. It is a legitimate compressed equation, but explicitly supplying its length-L generators requires O(JL) emitted entries. Their geometric recurrence does not make those entries free to a theorem whose input is the actual generators. An algorithm accepting these compact geometric generators could conceivably do better, but no scalar determinant algorithm with that input and the desired clock is initialized here.

Alternatively ordinary Hankel shift-displacement generators together with their necessary boundary contain length-L moment vectors. Those are genuinely acquired at soft(L+J) above, which is already soft m^2. Merely labeling the moment matrix Hankel, Cauchy-like or low displacement rank does not replace that compatible-data acquisition by soft sqrt L. This statement concerns these two explicit initialization routes only.

## The J-dimensional Christoffel boundary, with exact signs

Set the geometric grid polynomial

    P_L(X)=product_(i=0)^(L-1)(X-x_i).

It vanishes on the whole measure, so it is the monic degree-L orthogonal null polynomial. Beyond that degree ordinary nonzero-norm orthogonal recurrences are singular: the measure has only L support points. One may choose the monic null tail p_(L+r)(X)=X^r P_L(X); no singular moment inverse is needed for this choice.

For V_Y=product_(j<k)(Y_k-Y_j), the exact alternant M is

    M_(r,j)=Y_j^r P_L(Y_j),  0<=r<J,
    det M=V_Y product_j P_L(Y_j),
    E_L=(-1)^(LJ) det M/V_Y.                      (3)

The last sign follows by exchanging each x_i-Y_j with Y_j-x_i. V_Y is a certified unit by target separation. Equation (3) is proved directly over R, including zero divisors and hits; it does not rely on an infinite quasi-definite orthogonality sequence.

The determinant is structurally Vandermonde times an unknown diagonal. Its entries contain EXACTLY the long grid values P_L(Y_j). The cheap moment descriptor does not acquire them. Arbitrary selected coefficient access for P_L also does not acquire its evaluation at general unit Y_j: evaluation mixes its whole coefficient range. Computing only det M without acquiring that diagonal remains a possible distinct scalar algorithm, but (3) does not initialize one.

The primary formula was checked against C. Krattenthaler, [Hankel determinants of linear combinations of moments of orthogonal polynomials, II](https://arxiv.org/abs/2101.04225), Theorem 1 and its surrounding hypotheses. That source gives a small orthogonal-polynomial alternant under quasi-definiteness; it is an identity, not a fast determinant algorithm. Here finite support reaches a null polynomial, so the direct proof above is required rather than importing all its nonzero-normalization assumptions. No asymptotic theorem or characteristic-zero division is transferred to the composite ring.

## An actual scalar-only completion, at the inherited clock

The following pays for (3) without acquiring a dense J-by-J alternant and without evaluating or inverting H_F:

1. Choose b>=1. Build B_b(X)=product_(r=0)^(b-1)(X-q^r), degree b, by a product tree.
2. For each target Y_j and complete seed block k, acquire the start q^(-kb)Y_j. Evaluate the ONE common B_b at the actual J*floor(L/b) starts by monic MPE. Include the corresponding known q-power scale, and the final common short-tail polynomial at its J starts.
3. Multiply block values for each target to acquire g_j=P_L(Y_j), then output (-1)^(LJ)product_j g_j=E_L. Scalar-only output is permitted; per-target g_j can be discarded after their products are accumulated.

The initialized cost is

    soft(b+JL/b+J),

optimized at soft(J+sqrt(JL)). The common polynomial degree and actual target-list size are both included. At J~m,L~m^2, this is soft m^1.5, not soft m. The structure of (3) lets the scalar determinant be obtained from the g_j product without constructing J^2 matrix entries or acquiring the numeric V_Y; no collision-sensitive division is performed.

This is equivalent to the inherited geometric product algorithm and is recorded as a COMPLETION LEDGER, not algorithmic progress from Christoffel notation. The earlier Toeplitz/Schur determinant already has a different short scalar boundary formulation; replacing it by (3) has not supplied a new scalar evaluator.

## Nonunits, restrictions and stopping point

All moment and MPE divisions above are either certified small q-differences or monic polynomial divisions. No target matrix inverse, hit value, target determinant or nonunit Christoffel pivot is used. A generic orthogonal recurrence would additionally require actual leading Hankel-pivot unit certificates; the large-order guard for q by itself does not state those certificates. Such an algorithm would need proper-gcd handling and a lawful saturated-pivot continuation, neither of which can be assumed from its formal recurrence.

The completed scalar product algorithm supports native row subsets and shifted seed subintervals with the same bound. Proper gcds factor. Saturated products are localized by those paid restrictions; the ORIGINAL scalar native global-leaf decoder is then retained. Thus all nonunit branches of the available completion are accounted for. The hypothetical faster determinant is NOT granted this restriction/witness guarantee automatically.

This attempt initializes full weighted moments and compatible generators, derives the exact small alternant without a singular inverse, and completes its scalar evaluation at the old clock. It does not find a determinant algorithm accepting only the compact geometric descriptor at soft(J+sqrt L), or a smaller guaranteed covered Gram determinant. The finite-measure Christoffel boundary and nearly full Hankel rank were already known; no generic lower bound or new factoring exponent is claimed.

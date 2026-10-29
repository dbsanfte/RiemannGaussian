# Negative-prefix transfer through Bezout and Loewner boundaries

2026-10-26. Constructive test of a different compressed-boundary route. The raw/weighted short-Padé and parity attempts are not reused here. The result is an exactly initialized symmetric structured transfer, plus a decisive test against constant-channel divided-difference compression. No soft O(J+sqrt m) advancement or factoring exponent improvement is proved.

## 1. Exact native target and fixed-size transfer

Use the already paid lambda=0 unit screen and actual opposite closure. Let

    F(t)=t^L*G(t+q/t),  deg G=L, J=2L,
    a_s=q^-s+q^(s+1),
    C_m(W)=prod_(s=1..m)(W-a_s).

The acquired G is monic and G(1+q) is a unit. By the reviewed half-center identity, the original zero-prefix predicate is equivalent to

    det(C_m(C))=0,

where C is the L-by-L column companion matrix of G (multiplication by W on the basis 1,W,...,W^(L-1)). Explicitly,

    prod_(i=1..m) F(q^-i)
      =q^(-L*m*(m+1)/2) * prod_(s=1..m)G(a_s),

and det C_m(C)=prod_s G(a_s), up to the resultant sign (-1)^(Lm). The sign and q-power are units, sufficient for both zero and nonunit predicates. This statement does not confuse the deduplicated scalar with the original full Alexander scalar: its zero equivalence still uses squarefree N and the previous multiplicity-removal theorem.

Define the polynomial divided-difference matrix H by

    (G(U)-G(V))/(U-V)
       = sum_(i,j=0..L-1) H_ij U^i V^j.

For G(W)=sum_(r=0..L)g_r W^r, g_L=1,

    H_ij=g_(i+j+1), with g_r=0 for r>L.

Thus H is symmetric anti-triangular, det H=(-1)^(L*(L-1)/2), and C H=H C^T. All entries are explicitly acquired from G in O(L) encoded data; writing the dense H would cost Theta(L²) and is unnecessary.

The initialized symmetric boundary transfer is

    B_0=H,
    B_(n+1)=(C-a_(n+1) I) B_n,
    a_0=1+q,  a_1=q^-1+q²,
    a_(n+2)=(q+q^-1)*a_(n+1)-a_n.                       (1)

Then B_n=C_n(C)H is symmetric and det B_n=det H*det C_n(C). Its determinant zero is exactly the requested folded-prefix zero. No coefficient of G, collision value, or pivot is inverted. This is an executable recurrence over R with all starts acquired inside soft O(J), not an unspecified recurrence-existence statement.

A compact exact representation is R_n(W)=C_n(W) mod G, since B_n=R_n(C)H. One step updates R_(n+1)=(W-a_(n+1))R_n mod G in O(L) ring operations, so direct advancement costs O(Lm). The established block geometric evaluator improves this to soft O(J+sqrt(Jm)). Merely declaring B_n's displacement structure does not change those paid costs.

## 2. The proposed constant-channel boundary algorithm

A natural sparse-Seifert/continued-fraction proposal is to glue dyadic clock blocks using a bounded number of separated channels for the polynomial boundary kernel

    K_G(U,V)=(G(U)-G(V))/(U-V),
    K_G(U,V)=sum_(r=1..h) A_r(U) B_r(V),   h=O(1).       (2)

A rank-one/rank-two boundary factorization would permit a bounded-size determinant correction at each join, avoiding dense L-by-L boundary matrices. This is a concrete algebraic condition to test before charging such a join as constant-size. It is not assumed that every possible gluing algorithm must use (2).

**Exact negative result for (2):** its minimal separated rank is L, for every monic G of degree L, including the actual native G. Its coefficient matrix H has determinant +/-1, so any separated expansion with h terms yields a matrix factorization of H through h columns and forces h>=L over each residue field. Reciprocity of the unfurled F has already been fully used in passing from degree 2L to G; it supplies no further ordinary rank collapse of this kernel.

The same statement is visible on actual cheap clock nodes, rather than formal generic points. Choose

    u_i=q^-i+q^(i+1),   1<=i<=L.

For i!=j,

    u_i-u_j=(q^-i-q^-j)*(1-q^(i+j+1)).                  (3)

Both factors are units whenever the positive exponents |i-j| and i+j+1 are below both local q-orders. This holds for sufficiently large native inputs since 2L+1=soft O(k), whereas the local orders exceed 16k². Let V be the Vandermonde evaluation matrix at the u_i. Then the confluent Loewner matrix

    K_ij=(G(u_i)-G(u_j))/(u_i-u_j), i!=j,
    K_ii=G'(u_i)

satisfies K=V H V^T. Therefore det K=det(V)² det(H) is a unit modulo N, **independently of G's lower coefficients and of whether any G(u_i) vanishes**.

This also rules out the especially naive determinant selector: det K cannot be used to detect a root in this clock interval, since it is always a unit. A collision makes a value zero, not this polynomial's divided-difference boundary singular. This assertion is uniform for the actual monic family and does not depend on a nonnative diagnostic polynomial.

## 3. What remains possible: displacement compression is different from low rank

The rank test does not exclude representing H, B_n, or their joins with O(L) generators and doing quasi-linear structured linear algebra. H itself already has that encoding despite full ordinary rank. In particular no conclusion is drawn against a new displacement-aware dyadic algorithm.

There is, however, an exact acquisition check for a lossless B_n representation. Since H e_(L-1)=e_0 and C^i e_0=e_i for 0<=i<L,

    B_n e_(L-1)=R_n(C)e_0
               = coefficient vector of R_n.            (4)

Thus the last column of the exact symmetric boundary is precisely the original degree-L remainder. A claimed cheap lossless generator acquisition, together with cheap boundary-vector multiplication, would already give the full C_n mod G query. That would be a valid substantial advance, but cannot be counted as free boundary preprocessing. Conversely a determinant-only or zero-only state need not reveal (4), so this is not an obstruction to the weaker target.

A precise positive next task in this representation is: acquire enough determinant-relevant information for B_m in soft O(L+sqrt m), without materializing its last column and without the false constant-rank factorization (2). Proving closure of a displacement generator under dyadic joins would be useful only if its updated generators, including the boundary data, are acquired in that same budget.

## 4. Primary matrix reference and theorem scope

Vlastimil Ptak and Zdenek Vavrin, *Bezout, Hankel, and Loewner matrices*, Linear Algebra and its Applications 184 (1993), 13–36, DOI [10.1016/0024-3795(93)90367-W](https://doi.org/10.1016/0024-3795(93)90367-W), studies these classes as matrix realizations of one operator in different polynomial bases. Zdenek Vavrin, *A unified approach to Loewner and Hankel matrices*, LAA 143 (1991), 171–222, DOI [10.1016/0024-3795(91)90011-K](https://doi.org/10.1016/0024-3795(91)90011-K), studies generalized Loewner matrices and rational interpolation.

Only the primary metadata/abstract scopes were consulted here; no uninspected fast-algorithm theorem is claimed from them. All identities and rank/unit assertions used above are directly proved in this report. They remain valid over the composite ring under the stated native unit checks and do not import a field-only pivot algorithm.

## 5. Recovery and cost boundary

The negative-only original point polynomial F still supports the existing prefix-zero binary search. Once the first zero index m is obtained, scan only the original remaining x_j-q^-m. A saturated leaf yields the known nonzero exponent E_j+Hm; mixed CRT witnesses are handled by separate original rows. No transfer determinant eigenvector or root label is needed.

The new recurrence (1) is initialized, zero-preserving and division-free, but its current advancement cost is not better than the established soft O(J+sqrt(Jm)). The failed candidate is specifically constant-channel Loewner/Schur boundary compression, and the naive Loewner determinant selector. Small displacement encodings, other continued fractions, and determinant-only projections remain open. No general algorithmic lower bound or achieved 1/6 exponent is asserted.

## Scratch convention check

`check_boundary.py` passed 700 exact companion/Bezout transfer steps over N=101*103, for L=1,...,7 and ten coefficient lists at each size, plus 70 exact unimodular-Hankel determinant and adjoint checks. It checks the orientation C H=H C^T, symmetry, and the remainder-column identity (4), including nonunit intermediate entries. The proof above establishes the transfer identities; endpoint coverage is inherited from the previously proved native family. No cost scaling or native-hit promise is inferred from these checks.

After direct remainder advancement, the scalar determinant predicate can be obtained by monic multipoint evaluation of R_m at the already acquired native W_pair nodes and multiplying the values, in soft O(L); thus no uncharged field-pivot determinant routine is needed over R.

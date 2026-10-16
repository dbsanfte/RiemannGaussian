# The mixed matrix now has paid fast actions; its diagonal still needs a compatible generator

2026-10-16. New exact link from the paid block transform to the actual row query, followed by a standard displacement-based conditional extraction. No low-rank displacement generator or nearlinear diagonal/query theorem is proved here.

## A matrix-free operator whose diagonal is the entire row list

Supply J unit targets z_i, a unit q and length L>=1 with every 1-q^r, 1<=r<=L, a unit modulo N. Write F(t)=P_L(t;q)=sum c_k t^k. Choose a dyadic B=Theta(sqrt L), put T=floor((L+1)/B) and h=L+1-BT, and set y_i=z_i^B. Define the complete-block matrix

    C_(n,s)=c_(Bn+s), 0<=n<T, 0<=s<B.

Let A_(i,n)=y_i^n, W_(s,j)=z_j^s. If h>0, acquire the h remaining coefficients and form

    u_i=y_i^T,
    v_j=sum_(s=0)^(h-1)c_(BT+s)z_j^s.

Define S=A C W+u v^T when h>0, and S=A C W otherwise. Then exactly

    S_(i,j)=sum_(n<T,s<B)c_(Bn+s)y_i^n z_j^s
                + y_i^T sum_(s<h)c_(BT+s)z_j^s,
    S_(i,i)=F(z_i).                               (1)

The ragged term is a rank-one correction, not uncomputed padding beyond L. All coefficient indices used by C and by the correction lie within [0,L]. This handles the unit-denominator promise without strengthening it to L+B.

Both S*x and S^T*x have paid bit complexity soft O((J+B+L/B+sqrt L)log N), including their parameter construction. W*x is a transposed Vandermonde operation (weighted power sums); C and C^T are the new paid formal block operator; A is monic multipoint evaluation; and the ragged correction is a dot product and vector scaling. The transpose uses the reverse operations. Repeated targets are allowed for these actions. Product/remainder-tree transposition needs no inverse of node differences. All selected seeds, q powers and the ragged coefficients are acquired at the stated clock. Storage is soft O(J+B+L/B+sqrt L) residues.

At J=Theta(m), L=Theta(m^2), B=Theta(m), these are actual soft O(m) matrix-vector actions, with no full S, C or mask table. In particular b=S*1 is already paid. This does NOT supply diag S: fast actions alone are not an asserted general diagonal algorithm. It does explicitly identify the mixed diagonal with the original row list, rather than leave that identification as an additional condition.

## A compatible ordinary commutator would suffice

Now impose the actual odd-subgroup, distinct-node promise, so the y_i have unit pairwise differences modulo N. Let Y=diag(y_i). Suppose one could acquire arrays U,V with r columns satisfying

    YS-SY=U V^T,                                  (2)

at soft O(rJ) bit cost up to log N, with r=polylog(m). Neither the existence of such a small r nor a cheap construction of its generators follows from the new block transform. Merely computing the commutator as a black-box operator is not such a construction.

Given (2), for i!=j,

    S_(i,j)=sum_(a=1)^r U_(i,a)V_(j,a)/(y_i-y_j).

Thus diag S is b minus these off-diagonal row sums. They are computable softly linearly per generator by rational multipoint arithmetic. For completeness, with one weight vector w_j define

    Q(X)=prod_j(X-y_j),
    P(X)=sum_j w_j Q(X)/(X-y_j).

The latter sum is assembled by a product tree, without separately expanding J quotients. Its regular-part identity is

    sum_(j!=i) w_j/(y_i-y_j)
       = [P'(y_i)-w_i Q''(y_i)/2]/Q'(y_i).         (3)

This follows by expanding P/Q at X=y_i and removing its residue w_i. In the actual odd squarefree semiprime ring, 2 and every Q'(y_i) are units; one batch inversion is valid. A proper nonunit gcd outside that promise is a factor, while a saturated value is not an inverse. Construction, differentiation and multipoint evaluation of P,Q and the batch inversions cost soft O(J log N) bits per column, with soft O(rJ) residues if all supplied generators are retained.

Equations (1)--(3) would therefore acquire all actual row values and their gcd/product query at soft O(m) if the compatible polylog-rank generators were themselves acquired at that clock. This is a sufficient interface, not a claim that low rank must hold. Row-subset and common-seed-interval restrictions require the same generator theorem for their corresponding operators as well.

The rational-Newton q-displacement currently available yields a relation changing z to qz. It is not the fixed-node commutator (2). The reviewed mixed-contraction note derives that relation and shows why a small fixed target set is not closed under it. The two displacement contracts cannot be substituted for one another. Norm-only and other diagonal algorithms remain possible even if (2) has large rank.

## Provenance and outcome

The formal block transform and its paid seeds are report SHA256 825aaaa7d10637eddcf38a7b8e8f2241a70984c4b94c506372e922b845b2fe70. The mixed q-kernel and alignment classification are SHA256 ad33d26baea13d0d6f0ea968c1f8373042f7911049255c48d45e8c2118cde73f. The ragged operator factorization (1) and its action clock are proved here. The standard Trummer diagonal extraction is independently derived in (3); the primary-search note cites Bini--Meini--Poloni, ETNA 33 (2009), section3.3 equation3.9, for the displacement-generator-plus-one-action interface. No field-only solver or inaccessible matrix entries are granted for free.

This advances the concrete acquisition interface by paying BOTH matrix actions and identifying the exact required diagonal. It does not provide its displacement generators, acquire the collision-locator polynomial gcd, or establish a better overall query exponent. Those remain the substantive missing steps, followed by the full Lean bit/memory/controller proof.

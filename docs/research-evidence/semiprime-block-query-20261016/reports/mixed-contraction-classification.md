# The mixed block displacement changes targets; coarse binomials align with one row

2026-10-16. Exact follow-up to the paid scalar block-transform primitive. No general query lower bound or new fast factorization algorithm is claimed.

## 1. Exact mixed-kernel identity

Let F(z)=P_L(z;q)=sum_(k=0)^L c_k z^k, B>=1, and

    R_s(X)=prod_(a=0)^(s-1)(q^L-Xq^a)/(1-Xq^(a+1)),
    M_B(X,z)=sum_(s=0)^(B-1)R_s(X)z^s.

As an exact rational identity,

 (1-q^L z) M_B(X,z)-X(1-z) M_B(X,qz)
    =1-X-(1-Xq^B)R_B(X)z^B.                       (1)

Proof: multiply the recurrence

    (1-Xq^(s+1))R_(s+1)=(q^L-Xq^s)R_s

by z^(s+1) and sum s=0,...,B-2. The interior coefficients cancel; the remaining last coefficient equals -(1-Xq^B)R_B by the same recurrence. For B=1 the displayed identity also follows directly from M_1=1. The identity may be cleared of all displayed denominators before specialization.

Put H=floor(L/B)+1, X_n=q^(Bn), and a_n=c_(Bn). When the denominator factors through exponent HB are units, c_(Bn+s)=a_n R_s(X_n), with coefficients beyond degree L interpreted as zero. The last R_B vanishes because its numerator crosses the factor q^L-q^L. Thus

    F(z)=sum_(n=0)^(H-1)a_n z^(Bn)M_B(X_n,z).

Multiply (1) by a_n z^(Bn) and sum n. Since a_n R_B(X_n)=a_(n+1), X_(n+1)=q^B X_n, and a_H=0, the boundary terms telescope. The result is exactly

    (1-q^L z)F(z)=(1-z)F(qz).                     (2)

No division by F(z), 1-z, or a row collision value is needed. The actual retained source has the required denominator units for the chosen B~sqrt L: L+B lies below both local orders.

This specifies what the rational-Newton column displacement becomes after the mixed contraction: it changes the external target z to qz. It does not automatically supply the fixed-target diagonal. In either actual hidden field, a nonempty set of J<R nonzero target nodes cannot be invariant under q multiplication, because every such orbit has R members. This last fixed-carrier observation is inherited, not a new implicit-algorithm lower bound. Moving target sets or compressed propagation remain open.

## 2. The diagonal at the actual powered nodes

Use the reviewed decimation mask E_B(t)=D_B(t^B)/D(t), and let

    F_s(Y)=sum_n c_(Bn+s)Y^n,
    E_B(t)=sum_(s=0)^(B-1)t^s E_s(t^B),
    Y_j=z_j^B,  e_j=E_B(z_j)/B.

At every original node, E_s(Y_j)=e_j z_j^(-s). For the zero Cartier channel K,

    K(Y)=F_0(Y)E_0(Y)+Y sum_(s=1)^(B-1)F_s(Y)E_(B-s)(Y).

Therefore

    K(Y_j)=e_j sum_s z_j^s F_s(Y_j)=e_j F(z_j).    (3)

All multipliers are units on the actual odd-subgroup branch. The mixed matrix diagonal is precisely the wanted row payload, with the known unit scaling. The paid C/C^T and mask operators do give all F_s(X), E_s(X), and all Cartier outputs at ONE arbitrary scalar X nearlinearly. Equation (3) does not batch that scalar primitive across the J distinct Y_j. It isolates the additional structured diagonal-contraction theorem that would be needed; no assertion is made that it cannot exist.

## 3. A coarse point either aligns with one row, factors already, or is unaligned

This classification uses only the actual distinct-node/odd-subgroup promise, not new asymptotic deletions. Work in R=Z/N with N an odd squarefree semiprime. Distinct z_j have unit differences, and dyadic B preserves this property, so the Y_j are distinct in each hidden field.

For any supplied scalar X compute g=gcd(N,D_B(X)). A proper g already factors N, without acquiring F or a Cartier channel. If g=N, evaluate gcd(N,X-Y_j) for the J public nodes. A proper value again factors N. If none is proper, each difference is either a unit or zero modulo N. Since D_B(X)=0 in each field, at least one difference cannot be a unit; hence X=Y_j modulo N for exactly one j. These evaluations and gcds cost soft O(J log N) bits. Thus an everywhere-aligned coarse point, unless it already reveals a factor, is an ordinary known single row. At this point all B outputs in (3) and its r-channel version are unit multiples of that ONE row value; they do not scan B different rows.

If g=1, set G_X(t)=t^B-X. In R[t]/G_X,

    D(t)E_B(t)=D_B(X),

which is a unit. Hence multiplication by E_B is invertible there, with inverse D(t)/D_B(X). The entire Cartier output vector evaluated at X is exactly the coefficient vector of F E_B modulo G_X. It is therefore an invertible linear change of the already paid remainder F mod(t^B-X), not a root-aligned collision projector.

This last case does NOT imply that its individual coordinates are units: additive cancellations can reveal proper factors, and that remains a possible algorithmic escape. It only establishes the exact representation contract. In a field, a root constraint F(z_j)=0 at a node with z_j^B!=X places no universal constraint on an arbitrary prescribed remainder H modulo G_X: F=H+G_X A can satisfy that root by a suitable constant A. This arbitrary-polynomial observation is not a counterfamily theorem for the special q-Pochhammer F; it prevents deriving a guaranteed zero test from the mask identity alone.

## 4. Exact binomial-cover scope

There is a narrow actual-source obstruction to recovering the whole target remainder by a SMALL COVER of such binomial moduli. In either hidden field, each polynomial t^(B_a)-X_a, for any dyadic B_a, has at most one root among the distinct actual target nodes: dyadic powering is injective on their common odd-order subgroup. Consequently

    product_j(t-z_j) divides product_(a=1)^h(t^(B_a)-X_a)

requires h>=J. This holds even for fully input-dependent or privately advised X_a and different dyadic B_a. Repeated roots or repeated choices cannot improve the count. It rules out an exact CRT/remainder-cover proposal using only O(1) or polylogarithmically many such coarse moduli to cover all J nodes.

It does not force h independent invocations of a scalar algorithm, forbid a fast simultaneous-point method, or rule out scalar norm/factor acquisition without covering the roots. In particular replaying the O(m) scalar primitive at J points would be a quadratic algorithm, while the existing generic acquisition is already better. The missing positive task is a paid simultaneous diagonal contraction, an additive factor-selective observable at unaligned points, or another computation that avoids this cover contract.

## Pinned prerequisites

The adjacent mixed-contraction-source-pins.json records exact bytes for the scalar block operator, arbitrary-point block transform, one-channel interface and decimation identities. Their stated conditional clocks and promises are retained. No new repository edit, Lean theorem, primary-literature complexity claim or all-input sixth-rate clock is introduced here.

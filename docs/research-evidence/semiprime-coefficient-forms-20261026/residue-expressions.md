# Projective factor-tag coefficients as norms, residues and local-duality pairings

26 October 2026. Paper derivations; no tests, examples, repository edits or factoring implementation. Input is [hybrid-handoff §§1–4](../semiprime-axis-supplier-20261026/hybrid-handoff.md), including its actual torus preparation and the two monic families. Its new uniform coverage theorem is used as supplied, not replaced by the old smaller-nonsplit-only promise.

**Outcome.** There is a valid simplification: replace the original leaf first jet by a row-level cofactor jet, or by two directional norm coefficients on a degree-J algebra. Both have the same good-field tag ratio and avoid acquiring the clock derivative. The coefficient polynomials for the latter are actually acquired in soft J without root-separation inversions. The long clock values, or the two scalar norm derivatives directly, remain unpaid; the completed algorithm still costs soft(J+sqrt(JH)). This does not establish a query speedup. It identifies exactly what a residue/duality implementation would have to acquire.

## 1. Actual inputs and permissible replacement output

Work in B=(Z/N)[tau]/(tau²-D), with N=PQ and the preparation, norm guards and q=pi^H of the handoff. For each of its two families acquire unit roots y_j, integer weights w_j=[j]_n, J<=K, h=2H+1, and clock x_i=q^i, 0<=i<h. Define

    F(X)=product_j(X-y_j),       G(X)=product_(i=0)^(h-1)(X-x_i).

Only F, its split roots/metadata, q and the binary clock length are supplied. In the good family, at the nonsplit prime R the complete grid has exactly one hit (j*,i*), so theta=y_(j*)=x_(i*) and w_(j*)=R mod n. This implies theta is a simple root of F and G at that field. Other nonhit roots of F may repeat; no global Vandermonde inversion is assumed.

The handoff asks for exact coefficients of

    Z(delta,Y)=product_(j,i)[1-y_j/x_i+delta(1-Y*w_j)],
    V=[delta]Z(delta,0),       U=-[delta Y]Z.

Its recovery proof actually accepts **any** pair (U*,V*) in B with V* nonzero at the good nonsplit field and U*/V*=R mod n there. The other local components may be arbitrary. The same norm/coordinate guards and bounded residue scan then give a proper factor or a correct either-factor residue candidate for HH. No claim that an arbitrary global scalar phase has this provenance is made.

## 2. Exact leaf-jet formula and the derivative it can discard

Put a_j=G(y_j), b_j=y_j G'(y_j), C_j=product_(l!=j)a_l, R0=product_j a_j, and c=(-1)^(Jh)*(product_i x_i)^(-J), a known unit. Direct multiplication gives the exact composite-ring identities

    V=c*[h*J*R0 - sum_j b_j C_j],
    U=c*[h*(sum_j w_j)*R0 - sum_j w_j b_j C_j].       (1)

This follows by writing each leaf as (1+delta*c_j) times a leaf with y_j replaced by y_j/(1+delta*c_j), c_j=1-Yw_j. It is a polynomial first-jet identity, not division by a collision.

At the good field exactly a_(j*) is zero, C_(j*) is nonzero, and b_(j*) is nonzero by the clock order guard. Thus (1) has the promised ratio. But **the factor b_(j*) is unnecessary for projective tag recovery**. Instead ask for

    V_row=sum_j C_j,          U_row=sum_j w_j C_j.     (2)

Then V_row=C_(j*)!=0 and U_row/V_row=w_(j*) at the good field. This discards G' entirely. It is not a claim that (2) equals the original U,V globally.

Equivalently (2) is the first jet of product_j(a_j+epsilon*(1-Yw_j)). Given the actual a_j, a three-state product computes product a_j, V_row and U_row with O(J) ring operations and no inversions. This is the old three-state/cofactor mechanism applied to the newly uniform arithmetic tag promise, not new acquisition credit. Exact a_j acquisition is still the long query.

## 3. A division-free degree-J directional-norm target

Acquire the two degree-less-than-J polynomials

    H0(X)=sum_j y_j F(X)/(X-y_j)=X*F'(X)-J*F(X),
    Hw(X)=sum_j w_j*y_j F(X)/(X-y_j).                (3)

The displayed quotients are exact polynomial cofactors. They need no inverses or separated roots. Explicit balanced acquisition: at a leaf return (X-y_j,c_j), c_j=y_j or w_j*y_j; at a merge return

    F=F_left*F_right,
    H=H_left*F_right+F_left*H_right.

Polynomial products at each level give soft J work in the constant-rank coefficient ring B, with O(log N)-bit scalar weights and exponents. Therefore **both full H polynomials are paid inputs**.

Let g=G mod F, currently unacquired. Define

    D_F(g;H)=[epsilon] Res_X(F,g+epsilon*H),
    V_norm=D_F(g;H0),       U_norm=D_F(g;Hw).         (4)

These are polynomial functions of the supplied coefficients once g is supplied, valid over B through collisions. Since F is split, without using any interpolation inverses,

    D_F(g;H)=sum_j H(y_j)*product_(l!=j)g(y_l).       (5)

At the good field only j* survives. There H0(theta)=theta F'(theta)!=0, Hw(theta)=w_(j*)H0(theta). Hence V_norm!=0 and U_norm/V_norm=w_(j*). Repeated *nonhit* roots cause no problem: the multiplication by g is invertible on those components, and (5) is still an exact polynomial identity.

This is a legitimate smaller projective acquisition request than an exact original leaf jet in the sense of output specifications. No complexity separation is proved. It replaces the clock derivative by two fixed, cheaply initialized directions. It does **not** replace g by a short known scalar. A direct two-scalar algorithm for (4), without first producing g, would suffice and is not supplied by writing (4).

## 4. Local algebra / residue expressions: what is actually singular

Let A=B[X]/F, a free rank-J algebra. For supplied g, let M_g be multiplication by g. Then

    D_F(g;H)=Trace(adj(M_g)*M_H).                    (6)

This determinant first-variation identity is polynomial; it never inverts M_g. At the good field M_g has one-dimensional zero eigenspace supported at theta and is invertible on the complementary algebra, including any nonreduced nonhit components. Consequently adj(M_g) is a nonzero rank-one multiple of the projector onto theta. Formula (6) evaluates H at theta times a common nonzero amplitude, explaining the tag ratio.

A resolvent version is

    R_H(t)=Trace(M_H*(M_g+tI)^(-1)).

At the good field its coefficient of t^(-1) is H(theta): the complementary inverse has an ordinary power series in t, while the theta component is H(theta)/t. Thus

    Res_(t=0) R_Hw(t) dt / Res_(t=0) R_H0(t) dt
       = Hw(theta)/H0(theta)=R mod n.              (7)

This is a **local-field interpretation**, not a lawful composite-ring instruction to invert M_g at t=0. Globally other components can have larger zero multiplicities. The polynomial pair (4) is the safe uniform acquisition target. A method that first computes a local primary component, a common-root projector, or a local residue functional has already supplied the missing hit selection unless its construction and cost are proved.

There is also a canonical coefficient-residue functional on the monic algebra,

    lambda_F(A)=[X^(J-1)](A mod F).

Its pairing lambda_F(AB) is perfect over any coefficient ring: the monomial-basis matrix is anti-triangular with anti-diagonal entries one, so its determinant is a sign. This gives a genuinely division-free duality domain, with no field or separability assumption. It does not select the theta component. Turning this universal duality into the theta-supported functional requires g (or an equivalent collision-dependent adjugate/local projector). The cheaply acquired dual basis of the full algebra is not that projector.

These univariate identities are proved here directly. Primary context: D'Andrea–Dickenstein, *Explicit formulas for the multivariate resultant*, J. Pure Appl. Algebra 164 (2001), §§5–6, discusses Bezoutian residue duality on its stated nonvanishing-resultant/regular-sequence locus: https://doi.org/10.1016/S0022-4049(00)00145-6 . The primary indexed text was consulted; full publisher fetch returned 403. Its nonvanishing hypotheses are not imported at the very singularity we need to detect, and no algorithmic bound from that paper is asserted here.

## 5. Relation to old packets and exact initialized cost

The [24 October unique-gcd report §§1–2](/home/dbsanfte/riemann/formal/docs/research-evidence/semiprime-recurrence-checkpoint-20261025/evidence/semiprime-unique-acquisition-20261024/unique-gcd.md) already requests one linear subresultant or two Bezout cofactors. Its matrix uses the unacquired remainder g. Equation (3) there even reconstructs g from one acquired Bezout column. Therefore (6) is not credited as a newly acquired small matrix, and (7) is not credited as a new selected-residue oracle. The new useful arithmetic fact is that two monic families uniformly guarantee one good nonsplit field and that the recovered projective value may be the coarse integer tag, not the original root.

The [23 October reciprocal-Bezout audit §3](/home/dbsanfte/riemann/formal/docs/research-evidence/semiprime-arithmetic-selection-20261023/reports/reciprocal-bezout-kernel.md) similarly preserves collisions by an exact resultant after acquiring a long remainder. Moving to a Bezoutian or a different dual basis does not initialize that remainder. Neither source provides the two directional scalars (4) cheaply on the present input.

A fully initialized completion is explicit:

1. Acquire F,H0,Hw, labels and q powers: soft J.
2. Acquire all a_j=G(y_j) using the existing common geometric-block query: soft(J+sqrt(Jh)). Normalized leaves differ by the already paid unit c and rowwise unit factors; no endpoint is omitted.
3. For (2), form prefix/suffix products and two sums: O(J). For (4), monic multipoint evaluation of H0,Hw at all y_j plus the same prefix/suffix products evaluates (5) in soft J. Repeated evaluation nodes are permitted; no pair difference is inverted.
4. Apply the handoff's norm/coordinate guards, scan at most n residues, complement either-factor tags and run its restricted HH consumer: soft K with its stated preparation.

All arithmetic is over a constant-rank ring with soft O(log N) bit multiplication; the total is soft(K+sqrt(KH))=soft K^(3/2) for the two monic families. The old shorter weighted-family query soft K^(5/4) remains better and is not replaced. Constructing a dense J-by-J matrix, its inverse, or a general residue system would add work, not remove step 2.

## Precise next primitive

The best expression-level handoff found is: given the acquired split F, the two explicitly acquired polynomials (3), q and h=2H+1, compute just the pair of directional norms (4), or the row cofactor pair (2), in soft(K) without expanding the clock norm values. Only projective correctness at the guaranteed good nonsplit field is required; exact original U,V and G' are unnecessary. The first unpaid operation is this two-scalar collision-dependent contraction, not basis construction, a denominator certificate, or the HH decoder. No new whole-query bound or general obstruction follows from these alternative expressions.

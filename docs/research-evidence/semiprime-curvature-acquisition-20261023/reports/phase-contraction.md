# Quadratic phase contraction: an exact power-trace primitive

Date: 2026-10-23. This note is an algebraic construction and resource audit, not a completed factoring query. It uses the already prepared unit base and the already paid nonzero-global-annihilator decoder. No repository files were changed.

## Outcome

There is an exact shared evaluator for **one specified power trace** of the complete quadratic collision family. Its cost is soft O(r), including arbitrary row restrictions, common multiplier restrictions, and every endpoint of one common short sigma interval. It does not expand the r^2 row/multiplier pairs. A length-h formal product prefix costs soft O(rh), not soft O(r). This prefix does not by itself detect a local collision.

The elementary catalog s=1+rt makes the native-row restriction a common multiplier restriction, so this primitive applies to restricted native families as well. The catalog also has a cubic modular generator for its quadratic coefficients, with all centering carries explicit. The dyadic catalog has four analogous cubic branches. These coefficient descriptions do not yet provide a norm or resultant evaluating the full collision product in soft O(r).

Public integer-zero exponents can be removed with an O(r) scan, and in the elementary catalog at most one pair needs examination. This screen also applies when C_s is centered rather than positive.

## 1. The exact collision product

Let r be an odd prime, H=r^2, M=H^2=r^4, and N=PQ with the balanced window P,Q of order r^3. For each unit residue s modulo H, choose integers B_s,C_s satisfying

    G_s(Z)=Z^2+B_s Z+C_s N,
    2s+B_s = 0 (mod H),
    G_s(s) = 0 (mod M).

These are precisely the a_s=1 quadratic rows considered here. Take 1<=C_s<H and a centered lift |B_s|<=M/2. At an actual short multiple cP=s+Hh, the usual relation is

    M sigma = c^2 P+B_s c+C_s Q.

Consequently sigma=O(r), uniformly in the balanced window and 1<=c<r. For any supplied row set R, common multiplier set C contained in {1,...,r-1}, and integer interval I=[a,b] of length O(r), put

    E_s,c = C_s N+c^2+B_s c,
    K_s,c,sigma = E_s,c-M sigma,
    Z_s,c,sigma = beta^(K_s,c,sigma),
    F(z) = product_(s in R,c in C,sigma in I) (1-z Z_s,c,sigma).

The row convention in this note is positive C_s and centered B_s. It differs from the sibling AP report's centered C_s and centered b_s, with B_s=H b_s-2s. The trace identities and public-zero screen apply to either convention. The finite bound |sigma|<4r established for that sibling convention is not asserted here for the positive-C convention; this note uses only the O(r) bound with its own fixed window-dependent constant.

Negative exponents use the inverse of the prepared unit beta. Each original collision leaf is exactly

    beta^(E_s,c)-beta^(M sigma)
      = -beta^(M sigma)(1-Z_s,c,sigma).

Thus the full product F(1) has exactly the original local zero support, up to an explicit unit. This statement is about the full product; no corresponding zero-test assertion is made for one trace or a bounded prefix.

## 2. One trace for the whole family in soft O(r)

For a specified positive integer k of O(log N) bits, define

    A_k(I) = sum_(sigma=a)^b beta^(-k M sigma),
    P_k(T) = sum_(c in C) beta^(k c^2) T^c.

Then the kth power sum of all nodes is exactly

    S_k = A_k(I) * sum_(s in R) beta^(k C_s N) P_k(beta^(k B_s)).       (1)

Equation (1) is a direct rearrangement of a finite sum, over Z/NZ. It preserves the actual interval endpoints and requires no order hypothesis beyond beta being a unit.

To evaluate (1), construct the one polynomial P_k of degree <r and evaluate it at all |R|<=O(r) points beta^(k B_s) by a monic product/remainder tree. Ordinary fast polynomial multiplication and monic remainder division work over Z/NZ. They require neither inverses of differences of evaluation points nor distinct points. The weights beta^(k C_s N), the points, and the chirp coefficients have polylogarithmic-bit exponents and can be generated in soft O(r) bit work, with the usual suppressed factors in log N. Summing the weighted evaluations costs O(r) ring operations.

Compute A_k division-free by geometric doubling. In particular, do not divide by 1-beta^(-kM): that element can be a nonunit precisely in cases relevant to a collision search. The full cost for one k is soft O(r), and the product/remainder tree uses soft O(r) residues of storage. Arbitrary common multiplier masks merely zero coefficients of P_k. Arbitrary row masks merely omit evaluation points.

For a prefix of length h, compute S_1,...,S_h and use

    F(z) = exp(-sum_(k>=1) S_k z^k/k).

When h<min(P,Q), these denominators are units. In particular h<=r is safe under the prepared factor lower bound. This gives F modulo z^(h+1) in soft O(rh) bit work and soft O(r+h) residues by reusing the trace workspace. No claim of a shared soft-O(r) evaluation across all k is established here. For h of order r the stated bound is already soft O(r^2).

## 3. Public integer-zero leaves: linear cleanup, or none

Write

    B_s=H b_s-2s,
    G_s(Z)=(Z-s)^2+H b_s(Z-s)+M d_s.

If M divides G_s(c), then H divides c-s. Indeed, if v_r(c-s)=v<2, the first term has valuation 2v, strictly less than the valuations >=2+v and >=4 of the other terms, so their sum cannot be divisible by r^4. This proof also works for H=p^a with v_p(c-s)<a, including p=2.

Canonical 0<=s<H and 1<=c<r therefore imply c=s<r for every public leaf K=0. Scan the supplied rows once; only rows s<r need their single candidate c=s checked. Also test membership of c in the supplied multiplier set and whether the integer

    sigma_0=G_s(s)/M

belongs to I. This computes the number h0 of public zero-exponent leaves in O(r) arithmetic operations. It never counts r^2 pairs. For s=1+rt there is only the possible pair s=c=1. The dyadic catalog below likewise has only s=c=1 for c<m.

Deleting these leaves changes every trace by the same known integer:

    S_k(clean)=S_k-h0,
    F_clean(z)=F(z)/(1-z)^h0.

These are exact identities. Remaining global collisions beta^K=1 have nonzero integer K and are eligible for the already paid unconditional short-annihilator decoder. For the true own leaf,

    K=(P-1)(C_s Q-c^2),

which is nonzero under Q>16r^2 and nonzero C_s. No new global factor-sum theorem is needed.

## 4. Elementary catalog and exact cubic coefficient generator

Take S={1+rt:0<=t<r}. If the native residue is j=P mod r, then for every s in S the unique multiplier compatible modulo r is

    c_j = j^(-1) mod r,  1<=c_j<r.

This c_j is independent of s. The actual c_j P modulo H is one of these rows. A native-row restriction is consequently a common restriction of the c coefficients in (1), rather than a different restriction at each evaluation point.

Let n0 be N^(-1) modulo r in {1,...,r-1}. The coefficients

    C_s = s^2 N^(-1) mod H,  1<=C_s<H,

run exactly through C=n0+ru, 0<=u<r. This follows from s^2=1+2rt modulo r^2 and the invertibility of 2N modulo r.

For X=CN-1, which is divisible by r, define B(C) modulo M by

    B(C) = -2-X+X^2/4-X^3/8 (mod M).                          (2)

The fractions in (2) mean multiplication by the inverses of 4 and 8 modulo M. The truncated binomial square root gives

    B(C)^2 = 4CN (mod M),  B(C) = -2 (mod r).

Set s=-B(C)/2 modulo H, choosing 0<=s<H. Then s=1 modulo r and G_s(s)=0 modulo M; all the required rows are obtained. Taking the centered lift of B(C) gives the stated O(r) sigma bound.

Since C=n0+ru, (2) is cubic in u modulo M. Reduce each cubic coefficient to a centered integer modulo M and let P3(u) be that integer cubic. Then

    B(u)=P3(u)-M h(u),  |P3(u)|=O(r^7),  h(u)=O(r^3).

This is an exact coefficient description with one centering carry per row. It is not a low-degree polynomial description of beta^(B(u)). In particular,

    beta^(CN+c^2+B(u)c)-q^sigma
      = q^(-h(u)c) [ beta^(CN+c^2+P3(u)c)-q^(sigma+h(u)c) ],
    q=beta^M.

Replacing the centered B by its cubic lift therefore shifts the seed interval by h(u)c. Dropping this shift changes the local zero support. Its full family of endpoints is not acquired by the paid degree-two carrier norm.

## 5. Dyadic catalog: four cubic branches, with carries

Let m=2^k with k>=2, H=m^2, M=H^2=m^4, and N odd. Take the m residues

    S={s modulo H: s=+1 or -1 modulo 2m}.

The coefficients C=s^2 N^(-1) modulo H run through

    C=C0+4m u,  0<=u<m/4,

where C0=N^(-1) modulo 4m is chosen in {1,...,4m-1}. Each C has four s rows. For X=CN-1, divisible by 4m, the integer

    R(C)=1+X/2-X^2/8+X^3/16

satisfies R(C)^2=CN modulo M and R(C)=1 modulo 2m. All displayed divisions are exact integers. For example

    R^2-(1+X)=5X^4/64-X^5/64+X^6/256

has 2-adic valuation at least 4k.

The four valid B branches, with their centered lifts modulo M, are

    B_(epsilon,e)(C)=epsilon(2R(C)+e M/4) mod M,
    epsilon in {+1,-1}, e in {0,1}.                           (3)

For e=0 the corresponding s is -epsilon R modulo H. For e=1 it is -epsilon R+H/2 modulo H. To check G_s(s)=0 modulo M, put D=(B^2-4CN)/M and b=(B+2s)/H. For e=0, D=0 modulo 4 and b is even; for e=1, D=1 modulo 4 and b is odd. Therefore G_s(s)=M(b^2-D)/4 is a multiple of M. Centering B modulo M does not alter this conclusion. These four rows are distinct and all lie in the stated catalog.

Writing X=4m Y gives

    R=1+2mY-2m^2Y^2+4m^3Y^3,

with Y affine in u. Thus (3) consists of four integral cubic generators modulo M. Reducing their coefficients and then centering the row value again introduces one integer carry per row, exactly as in the odd-prime case. The same seed-shift identity must be retained. Formula (1) applies unchanged to any supplied dyadic row list and common subset of odd multipliers c<m.

## 6. Bit and storage ledger

Put b=ceil(log_2 N) and assume r=Theta(N^(1/6)), |C_s|=O(r^2), |B_s|=O(r^4), and the sigma endpoints have size O(r). Every E and K has O(b) bits. For one supplied trace index k, put L=b+log(1+k). The exponent arguments used in (1) have O(L) bits. For a prefix h<=r, L=O(b).

* Input generation: each of the O(r) modular row coefficients and evaluation-point exponents has O(b) bits. Modular coefficient arithmetic costs soft O(rb). Restrictions can be supplied as O(r)-bit masks or row lists. For the elementary catalog, j-to-c restriction conversion uses inverses modulo r in soft O(rb) bit work.
* Unit inversion: invert beta once by the extended Euclidean algorithm in soft O(b) bit work. If it is a nonunit, its gcd already factors N. No evaluation-node differences are inverted.
* Point and weight powers: O(r) binary modular exponentiations, each with O(L) modular multiplications. Writing M_int(b) for integer multiplication cost, this is O(r L M_int(b)), up to the cost of modular reduction. Coefficients beta^(k c^2) can alternatively be generated along c=0,...,r-1 using a second-order geometric recurrence with O(r) modular multiplications, then masked.
* Multipoint evaluation: degree <r, O(r) supplied points, monic product/remainder tree, in soft O(rb) bit work using fast polynomial arithmetic over Z/NZ. Repeated points are permitted. This step uses soft O(rb) bits of workspace, including the tree.
* Seed factor: division-free geometric doubling costs O(log(1+|I|)) ring multiplications after the endpoint power. All actual integer endpoints are retained. The weighted sum costs O(r) ring additions/multiplications.
* Public K=0 screen: O(r) integer operations on O(b)-bit quantities and at most one candidate multiplier per row. It is done once per restricted family, independently of k. The subtraction h0 from each trace costs soft O(b).

Thus a uniform conservative bound for one trace is soft O(r b^2) bit operations and soft O(rb) workspace bits. The bit cost for h<=r traces and the resulting prefix is soft O(rh b^2); storage can be reused between indices, giving soft O((r+h)b) bits, including the h output residues. Fast formal exponentiation adds soft O(hb) bit work, with all denominators units as stated above. These bounds count setup for the evaluator itself. They assume the base and the previously established factoring/annihilator consumers supplied by the parent construction, and do not charge their already paid setup a second time.

## 7. Validation and precise remaining condition

Direct exact modular checks were performed for odd r=3,5,7,11 with N=101*103, checking the C progression, cubic B, derivative condition, double-root congruence, and equality of direct versus contracted traces for k=1,...,4 and sigma=-2,...,3. For m=4,8,16, enumeration of the actual dyadic rows agreed with all four branches in (3). These checks corroborate the displayed identities; their proofs are given above.

The new bounded-state object is the full-family fixed-k trace (1), plus the linear public-leaf cleanup. The full formal product retains the original zero support and all endpoints. Its degree is normally of order r^3; evaluating it at z=1 is still unpaid. A bounded trace or formal prefix can cancel or miss a local zero, so it cannot be substituted for that evaluation. A full soft-O(r) query would need an additional theorem that contracts the k direction or evaluates this particular multiplicative product directly, while retaining the centering carry and seed endpoints. Neither the cubic modular coefficient generator nor the existing degree-two dyadic carrier norm supplies that theorem here.

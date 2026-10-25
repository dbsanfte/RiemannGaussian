# Scalar binary elimination with an acquired native 2-adic image mask

24 October 2026. Scratch only; no source/repository edits, examples, or backend claim. A positive initialized operation is obtained: the exact native index-residue image modulo 2^r is acquired as O(r) dyadic classes per row, without listing 2^r factor residues. Its completed scalar query still costs soft(J+sqrt(JL)). The operation is a native coverage filter, not an exact evaluation of the original arbitrary-F resultant. No general impossibility or new factoring exponent is asserted.

## Prior material inspected and duplicate boundary

Read the latest AGENTS tail, the recurrence journal appendix in /tmp/semiprime-one-shot-construction-20261023/journal-append.md, the preserved semiprime-high-digit-query-20261016/sources/journal-entry.md, and these exact reports:

| Report | SHA-256 |
|---|---|
| /tmp/semiprime-one-shot-construction-20261023/recurrence-decimation-design.md | 61bc72cda7a8c4d97e68883b1519d916d064fcae7cb198b371dd5f4503edf065 |
| /tmp/semiprime-one-shot-construction-20261023/bostan-mori-attempt.md | 5275f72c33e6c7b2f2a4ac4aef6b663e89e2b25c69fbdca7280267376d516353 |
| /tmp/semiprime-forcing-acceleration-20261023/paired-norm-execution.md | d2d09b95ac3ac721f49a5f7e7bab4d93e2bbc78d3561e38424fc510209a76b11 |

They already pay BM proper-state transport but not its source initialization, identify the shifted-quotient boundary, and execute split-pair norms whose child rank doubles. Native parity/fourfold reductions are also already recorded. None is counted again as a new rate advance here. The new attempted initialization below is entirely integer arithmetic on the actual native coefficients, so no far coefficient, quotient remainder, fixed-matrix power, or algebra endomorphism is assumed.

## 1. Exact generic length elimination: paid baseline, not the innovation

For arbitrary acquired F of degree J and unit q,

    E_(2n)(F,q)=E_n(F(X)F(qX),q²).

After B=2^r length sections, the acquired parent polynomial is product_(t<B)F(q^t X), degree JB, and the remaining length is roughly L/B. Geometric doubling constructs that polynomial in soft(JB); odd tails are explicit. Blocking at that point retains the interaction (JB)*(L/B)=JL. Reversing the resultant or retaining its scalar norm does not construct a smaller polynomial by itself. This is the already-known degree/rank ledger, included only to delimit the different native arithmetic attempt.

## 2. Native factor-residue elimination and its exact startup

Retain original beta, H=m² odd, L=2H+2, and actual row metadata a_j, ell_j, delta_j=a_j+ell_j, Y_j=beta^(N+delta_j). At the original own tag j=P modulo m,

    H I=a_j P+Q+ell_j, 0<=I<L, N=P Q.

Fix B=2^r<=L with r>=1; B=1 is the trivial mask {0} and needs no recursion. Since P is odd, its residue v modulo B is a unit and Q=N/v modulo B. Therefore I belongs to the exactly specified public residue set

    S_j(B)={H^-1*(a_j v+N/v+ell_j) modulo B : v odd modulo B}.   (1)

All inverses here are modulo a PUBLIC power of two, never modulo an unknown prime. These are actual native integers, including ell_j's carry. Replacing P by every odd residue is an overcover, so (1) retains the own index without knowing the successful j. It does not assert that every retained residue contains a factor.

For one parent residue v modulo 2^t, let alpha be the FULL value of H^-1*(a_j v+N/v+ell_j) modulo 2^(t+1), acquired using the inverse of the chosen odd representative at that precision. Then its two lifts satisfy exactly

    I(v+2^t e)=alpha+2^t e*H^-1*(a_j-N/v²) modulo 2^(t+1).

A parent I residue alone does not supply alpha: different factor preimages can have different next carries. Retaining only the image set without a preimage/ball representation would leave this update uninitialized. Literal factor-residue enumeration costs JB, even if many images coincide. The following ball algorithm avoids that enumeration.

## 3. Positive initialized operation: O(log B) exact image classes per row

First ignore the invertible affine output H^-1*(x+ell_j) and study

    f(v)=a v+N/v modulo 2^r, v odd.

Use balls v=v0+2^t z, beginning with the single odd ball v0=1,t=1. For a ball compute the truncated valuation

    k=v_2(a v0²-N).

The odd denominator v0² makes this also the valuation of f'(v0)=a-N/v0².

**Regular ball, k<t.** Put delta=2^t z. The exact identity is

    f(v0+delta)-f(v0)
       =delta*(a-N/v0²)+N*delta²/(v0²*(v0+delta)).     (2)

More explicitly, put c=(a v0²-N)/2^k, which is odd. Then the normalized map is

    F(z)=[f(v0+2^t z)-f(v0)]/2^(t+k)
        =z*[c+a v0*2^(t-k)z]/[v0*(v0+2^t z)].

Its denominator is odd and its reduction modulo 2 is z. Moreover F'(z) is odd for every integer z: its linear coefficient reduces to c/v0², while every nonlinear correction has an even coefficient and odd denominator. For s>=1, rational Taylor expansion with odd denominators gives F(z+2^s)=F(z)+2^s F'(z) modulo 2^(s+1); the quadratic remainder is divisible by 2^(2s). Thus the two possible lifts of a solution modulo 2^s have opposite next output bits, and exactly one solves any prescribed lift. Starting from the bijection modulo 2 proves by induction that F is a permutation modulo every needed power of two. The parameter z ranges over at least that whole modulus because it initially ranges modulo 2^(r-t), whereas the output needs only 2^(r-t-k). Thus this WHOLE factor ball maps ONTO exactly one output class

    f(v)=f(v0) modulo 2^min(r,t+k).                  (3)

The image class is acquired by one modular inverse/evaluation, with all carries present. If t+k>=r it is one residue modulo B.

**Critical ball, k>=t.** If 2t>=r, (2) is zero modulo 2^r for every z, so the whole image is the one residue f(v0) modulo B. Otherwise split into the two actual factor balls v0 modulo 2^(t+1) and v0+2^t modulo 2^(t+1), recompute the valuations and continue.

Only critical balls are refined. At precision 2^t they satisfy a v0²=N modulo 2^t. If a is even there are none. If a is odd, there are at most four for t>=3: for two odd square roots x,y of a fixed odd unit, (x-y)(x+y)=0 modulo 2^t; exactly one of x-y,x+y has valuation one, forcing x=+y or -y modulo 2^(t-1), with at most two lifts per sign. The first two levels contain only constantly many balls as well. Consequently the tree has O(r) nodes and emits O(r) exact dyadic image classes, stopping by t=ceil(r/2). No 2^r residue table is materialized.

Apply the output affine map H^-1*(x+ell_j) to each acquired class; an odd unit preserves its dyadic modulus. Remove duplicate/contained classes using their acquired residues/moduli (two dyadic classes are either disjoint or one contains the other). This costs soft r and gives EXACTLY S_j(B) as a disjoint union of O(r) classes.

The entire native mask constructor costs soft(J log B) small-integer work and O(J log B) output metadata, customarily soft J including O(log N)-bit costs. All startup, branching tests, valuations, inverses, full output offsets and terminal balls are acquired. This is the positive algorithm of the attempt, rather than a recurrence with a missing boundary.

## 4. Image size: test the hoped-for square-root pruning

The map is not silently assumed to have sqrt B images.

If a is EVEN, f(v)-f(w)=(v-w)*(a-N/(vw)). The second factor is odd and hence invertible modulo B. Thus f is injective on the B/2 odd residues and is a bijection onto the odd output class. After H^-1 and ell shift, S_j(B) is one parity class, of size exactly B/2. This recovers only the existing parity saving.

If a is ODD, a known regular subball with bounded modulus always exists. If v_2(a-N)<=3, choose v0=1 and k=v_2(a-N). Otherwise choose v0=3: then 9a-N=8a+(a-N) has valuation exactly 3. In both cases 1<=k<=3. Take the factor ball v=v0 modulo 2^(k+1); it is regular, so (3) shows that its image is a FULL class modulo

    2^(2k+1)<=128.

For B>=128 this gives |S_j(B)|>=B/128; for smaller B, nonemptiness gives the same numerical lower bound. No distribution assertion about the parity of the native a_j palette is needed: every supplied a, even or odd, satisfies a constant-density conclusion. This is an elementary per-row property of this particular arithmetic filter, not an operation lower bound or a claimed semiprime counterfamily. The exact image may of course have more classes, and exceptional narrower local pieces can still be used adaptively.

In particular there is always an output class of modulus <=128 within the mask (or a larger containing class after deduplication). This explains why the initialized image recurrence does not repeatedly halve the whole query horizon while keeping the same target count. The first parity/fourfold successes do not extend to vanishing-density masks by this mechanism.

## 5. Actual scalar terminal acquisition from the compressed masks

For each disjoint image class i=c modulo D, 0<=c<D, retain its ORIGINAL row label. Within [0,L), write i=c+Dk, 0<=k<h_c. Acquire

    z_(j,c)=q^-c Y_j, q_D=q^D.

The retained collision comparison is z_(j,c)=q_D^k, which is the original comparison Y_j=q^i times a known unit. Every c,D,h_c and endpoint is paid metadata. All virtual roots are acquired by signed unit powering; no pairwise unit-difference promise is made for them.

Group classes by D (a power of two). There are only O(log B) groups, and h_c has at most two values for each D. Build the explicit target polynomial in each group and length class, degree K_D, using a product tree. Its remaining horizon is h_D=O(L/D). Ordinary geometric blocking constructs degree-K_D*b coefficient blocks and evaluates them at O(h_D/b) explicit giant starts. It costs

    soft(K_D+sqrt(K_D*h_D))

per group, including all polynomials, starts and tails. Summed across the O(log B) groups this is bounded by soft(J+sqrt(JL)), since there are only soft J acquired image classes and sum_D 1/D is bounded. Thus a scalar covered query, with its terminal product actually acquired, follows from the compressed metadata. There is no quotient-algebra rank doubling or unacquired remainder in this completion.

However the masks contain bounded-modulus classes for EACH row. Among the finitely many D<=128 some class group contains a constant fraction of the row labels; its horizon remains a constant fraction of L. The displayed implementation therefore still calls a growing-degree, long-horizon scalar routine when retaining these labeled targets with multiplicity, at the old square-root-of-degree-times-length scale. This is a finite pigeonhole over the seven possible small MODULI, not an assumption that those rows share the same residue offset; different offsets are acquired as shifted targets of the common q_D query. Coincident shifted targets could be deduplicated and help particular instances; no lower bound on their distinct count or on a different implicit algorithm is asserted. This statement prices this concrete completion only.

The query is an overcover of the actual own witnesses within an UNDERSET of the full original row/index rectangle; its masks are the exact arithmetic residue images (1), and preserve the own factor witness, but its product need not have exactly the same residue as E_L(F,q). For arbitrary supplied F without the native arithmetic, only section 1's exact norm elimination is justified.

## 6. Zero-safe localization and original recovery

No desired leaf or product value is inverted. Take gcd of the acquired group products with N. If nonunit support saturates, restrict groups/rows/image classes and then the public k interval; monic product/MPE recomputation has the same bound up to logarithms. Every retained leaf maps back to the original integer index i=c+Dk in [0,L).

A proper leaf gcd factors. A saturated leaf is the ORIGINAL beta equality beta^(N+delta_j)=q^i. Invoke the pinned uniform setup/interface, SHA-256 4c4efaba5c3a09dd4ca1a87801e44212d5fcd2570ff26ec5f193f71589ec0d46, section 8: the retained beta global-order and factor-sum bounds force P+Q=1+H i-delta_j, so exact square-root arithmetic factors. Equivalently the positive O(log N)-bit exponent N+delta_j-H i admits the inherited original-beta short-annihilator route. Original row metadata is retained throughout, including false tags. No new order for a transformed representation or decoder is assumed.

## 7. Rank, degree and acquisition ledger

| Stage | Explicit acquired state | Paid work / degree |
|---|---|---|
| Generic exact B-section | polynomial product_(t<B)F(q^t X) | degree JB, horizon L/B; old JL interaction |
| Literal native residue table (avoided) | odd v and image per row | JB metadata |
| Critical-ball mask constructor | O(log B) balls/classes per row | soft J total; every carry initialized |
| Native image sizes | exact union of dyadic classes | B/2 for even a; at least B/128 for odd a |
| All transformed scalar targets | O(J log B) labeled roots | soft J acquisition; no hidden full vector |
| Group D terminal polynomial | degree K_D | horizon O(L/D), paid blocking |
| Whole acquired covered query | scalar products and restrictions | soft(J+sqrt(JL)) |
| Saturated leaf | original j and i=c+Dk | original beta decoder, paid |

At J~m,L~m² the initialized mask acquisition is soft m, but the completed query remains soft m^(3/2). The concrete positive deliverable is the exact compressed 2-adic image constructor and its zero-safe integration. It does not achieve soft(J+sqrt L), and does not assert that other moduli, nonseparable terminal contractions, or native arithmetic selectors cannot do so. The next useful change must improve the actual grouped terminal acquisition or find a different genuinely sparse covered image, not count the acquired mask descriptor as the scalar product.

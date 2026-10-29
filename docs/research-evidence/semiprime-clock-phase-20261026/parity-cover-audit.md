# Audit and explicit completion of the parity-lattice cover

26 October 2026. Independent paper audit of native-phase.md and the proposed amended ellipse. **PASS with the explicit construction and bounds below.** This closes the unique-support handoff for this enlarged family; it gives an acquired parity selector and a constant clock improvement, not a sixth-rate exponent gain.

## 1. Covered coefficient family and its size

For each correct dyadic bin B<=R<2B, use the lattice

    a*r*(r+K)=cN mod 2K,

and the completed nonaxis ellipse

    a²B⁴+c²N² <= (4/sqrt(3))*K*B²N,
    4 divides a+cN.                                      (1)

N and r are units modulo 2K; the lattice has determinant 2K. Its weighted Gauss shortest vector satisfies (1), so every factor colour retains a covered witness. The phase lift exists because reduction modulo K is the original stationary congruence. The lattice condition is independent of the representative r modulo K: its change is a multiple of 2K. Its mod-4 component is precisely 4|(a+cN).

Keep only the shortest axis coefficients (±2K,0),(0,±2K), and only when they lie in (1). The old ±K axes fail the new parity condition and must not be imported. Every shortest axis lattice vector has exactly these coefficients; no nonshortest axis vector is needed for coverage.

Write g=gcd(a,K)=gcd(c,K) for an eligible nonaxis pair. The ellipse gives |ac|<=2K/sqrt(3), hence g²<=2K/sqrt(3). Nevertheless g²<K for pure K=2*3^e: for odd g=3^v the possible ratios g²/K are 3^(2v-e)/2; for even g=2*3^v they are 2*3^(2v-e). Neither sequence has a value in [1,2/sqrt(3)]. In particular g<K, and the old divided stationary equation has unit coefficients modulo K/g. This is the precise replacement for the old strict |ac|<K assumption wherever that assumption was only used to obtain g²<K.

If A,C are the semiaxes in (1), AC=4K/sqrt(3). At most 4AC/g² nonaxis pairs of content g and at most 2g unit colours per pair give

    J_nonaxis <=8AC sum_(g|K)1/g <24sqrt(3)K <42K.

Here sum_(g|K)1/g<9/4 for this pure conductor. The four axes add at most 4phi(K)=4K/3 rows. This is soft-K acquisition, including colours, canonical phases and actual numeric roots; it does not charge a thin ellipse by a large enclosing integer box. Use the existing sparse ellipse enumeration / coefficient-direction enumeration contract.

## 2. Unique-support selection survives

For nonaxis rows the original phase-class incidence proof requires the stationary equation, the exact content g, and g²<K. Those remain available. Thus the hypothetical factor-colour support is exactly an eligible equal-canonical-phase class, with all original odd-unit and modulo-4 conditions retained.

The axis a=2K has phase ell=-2Kj mod H. Its support condition is K|2(r-j), or K/2|(r-j). Since r and j are odd and K/2 is odd, this implies K|(r-j). The other three axes give the same singleton conclusion. They do not create a two-colour ambiguity.

For high-content direction disjointness, the weighted determinant bound is now

    |a*c'-a'*c| <=4K/sqrt(3) <3K.

Two rows with a shared eligible colour and positive 3-content have determinant divisible by 3K. Therefore intersecting high domains still force parallel vectors. The old bound <2K is unnecessary for this step. Primitive directions have 3-unit core coordinates, since otherwise the unit-colour stationary equation would force content at least 3^e, contrary to g²<K.

Within one primitive direction, choose an actually admitted pair of maximal v3(content). Its eligible domain contains all lower-level domains: after dividing the multiplier, the 3-power congruence weakens with that valuation. The extra condition 4|d(a0+c0N) restricts admitted multipliers but is independent of the unit colour, so does not invalidate domain nesting. For that chosen pair, retain one actual row per equal-phase class. Distinct high directions have disjoint domains. Outside their union, an original parity-lattice shortest witness must have 3-unit content or be an axis, hence singleton support; choose one such actual singleton per remaining colour.

This is exactly the existing finite support-partition algorithm with its determinant constant changed. It yields J_selected<=phi(K)=K/3 and EXACTLY ONE good-field row-clock hit in the correct bin. It does not assert that every completed row has singleton support. Building and verifying the sparse incidence partition costs soft K using the acquired O(K) incidence bank.

## 3. Explicit window and exact-integer provenance

Set

    Dceil=ceil(sqrt(2KN)),
    M0=ceil(4Dceil/H)+2,
    h=2M0+1.

For a row in (1), put U=aB,V=cN/B. Then U²+V²<4KN. When R/B belongs to [1,2],

    |aR+cN/R| <=2|U|+|V|
                  <=sqrt(5)*sqrt(U²+V²)
                  <sqrt(20/ sqrt(3))*sqrt(KN)
                  <4Dceil.                              (2)

The looser U²+V²<4KN alone would give sqrt(20)*sqrt(KN); the displayed sharper constant uses (1) itself. With centered |ell|<=H/2, every actual stationary index

    i=(aR+cS+ell)/H

has |i|<4Dceil/H+1/2<M0. Thus the signed window [-M0,M0] covers every selected witness, and even every stationary hit of an added row in its correct bin.

Conversely a numerical local hit in that window gives the exponent congruence

    ord_R(pi) divides L=aR+cS+ell-Hi.

This uses the prepared Frobenius relation barpi=pi^R and pi^(R²-1)=1 at the nonsplit prime. From (2),

    |L|<8Dceil+(7/2)H <=12K^(7/2)+4H+8 <16H²

for K>=54 and N<=K^6. The prepared order >256H² therefore forces L=0 as an INTEGER. The constants are deliberately loose; no modular alias is admitted. The same bound holds for the four axes when they pass (1). Wrong factor-size bins do not inherit (2) for the actual R and remain bounded attempts rather than receiving this promise.

Since ceil(x)<x+1 and Dceil<sqrt(2KN)+1,

    h<8sqrt(2)*K^(3/2)+8/H+7
      <=8sqrt(2)*K^(3/2)+9 <16H  (K>=54).          (3)

All retained q² node gaps are original q gaps <h. Any implementation asking for one extra boundary factor must check its actual exponent; h+2<16H still follows from the same margin. The prepared clock-unit screen supplies these inverses.

Every added actual mixed-relation leaf has labels (ell-Hi,a+cN). The second is nonzero: nonaxis |a|<=2K/sqrt(3)<N when c!=0, while horizontal axes have a=±2K. Thus the existing complete mixed-label decoder applies after proper localization; no additive-zero or aggregate-product decoder is being assumed.

## 4. Acquired row parity and the final common-base query

Condition (1) gives ell=0 mod4. At an actual integer hit, R,S odd imply R^-1=R mod8 and S=NR mod8. Therefore

    aR+cS=(a+cN)R=a+cN mod8,
    i=(ell+a+cN)/4 mod2,

because H=4 mod8. This holds for EVERY colour in this row's support; it does not depend on which support representative was retained. With T=q^M0*pi^ell*barpi^(a+cN), set

    r_row=M0+(ell+a+cN)/4 mod2.

Retain normalized clock indices r_row+2s in [0,h-1]. The actual inspected leaves are exactly

    1-(T*q^(-r_row))*(q²)^(-s).

There are only the two lengths M0+1 and M0, one common base q², and no quotient by discarded leaves. Metadata and shifted starts cost soft K. The unpadded variable-window first-jet consumer is directly valid; a SINGLE-W first-subresultant or q-Newton consumer requires the following additional paid padding gate.

For every r_row=1 row, acquire its next q² leaf, at original normalized index h=2M0+1, hence signed physical index i=M0+1. There are O(K) such actual endpoints, each obtained by a short modular power. Norm/coordinate classification gives a proper factor or localizes a saturated endpoint to its actual mixed relation with labels

    (ell-H*(M0+1), a+cN).

The second label is nonzero by §3, so the existing mixed-relation decoder handles a global saturated relation; it is not an assumed unit. On continuation every appended endpoint is a GLOBAL unit. In the correct bin, §3's alias bound grows by at most H and remains <16H², while the strict true-index margin |i|<M0 rules out this endpoint as an actual good-field hit. Thus that bin cannot silently lose its covered promise at this gate. Wrong-bin nonunits are handled by the same actual-label factor decoder, not by importing the correct-bin magnitude bound.

Now append that certified unit to each shorter row. With

    Q=q², T'_j=T_j*q^(-r_row), L=M0+1,

all rows have the SAME clock s=0,...,L-1 and the acquired short polynomial D*(X)=product_j(X-T'_j). The unit padding preserves the componentwise hit set, uniqueness and projective first-jet ratios; it does not assert that arbitrary amplitudes or the numerical unpadded product are unchanged. The original single-W pole-pair, q-Newton and first-subresultant formulas now apply literally to D* and W_L, with their own norm gates and bounded wrong-bin validation. Node exponents through 2L=h+1 remain below 16H. The extra endpoint work and rebuilding D* cost soft K. Alternatively grouping the two unpadded lengths invokes the inherited variable-window/common-baby engine without this padding. No product division by an unclassified endpoint is used.

The index span grows by sqrt(2) while this acquired phase halves it: an asymptotic constant improvement in the row-clock horizon, approximately 1/sqrt(2), before rounding and before changes in the selected row count. It is not automatically an exact 1/sqrt(2) total runtime ratio and does not change the K^(5/4) exponent. Repeating the construction for many dyadic bits incurs the scalar-content growth already proved in native-phase §4.

## 5. Independent audit of the full-fibre iff and forced scaling

**PASS, with its stated full-fibre scope.** For r odd and R=r+Ks, R is a unit modulo every dyadic b. Subtracting the proposed constant phase k gives the integer quadratic

    P(s)=a*s²+(C-kK)*s+(A-kr).

It vanishes modulo b for every integer s iff P(0), P(1), and its constant second difference vanish modulo b. These are exactly b|(A-kr), b|(a+C-kK), b|2a. Conversely write P(s)=P(0)+s*(P(1)-P(0))+a*s*(s-1); the three conditions make each term divisible by b. No oddness or invertibility of the auxiliary integer s is assumed.

The quotient (a*r²-cN)/K is an actual integer by stationarity. The identity

    r*C-K*A=(a*r²-cN)/K

and k=A/r modulo b convert the middle condition exactly to cN=a*r*(r+K) modulo Kb. Thus native-phase equations (1) and (2) are equivalent, not merely necessary tests; their only modular division is by odd r.

For b=2^t>=2, b|2a forces d=b/2 to divide a. The congruence modulo Kb and odd N then force d|c as well. Cancelling this INTEGER factor d from both sides and from modulus Kb gives precisely

    c'*N=a'*r*(r+K) mod 2K,

so every such coefficient pair is d times a parity-lattice pair. This remains true for arbitrarily large dyadic b, not only b dividing H. Canonical phases scale modulo H, with an explicit integer H-carry on choosing centered representatives; physical index spans therefore scale by d, up to that integer translation. Thinning by b compensates that forced scaling only to a constant factor within this constructor. This is not a lower bound on selectors valid only for actual divisors of N, a different coefficient family, or a collective acquisition algorithm. In particular the iff is not claimed for the sparse set of actual factor lifts alone.

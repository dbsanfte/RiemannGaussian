# Paid strong-order setup and an exact remaining query interface for every semiprime

2026-10-16. Classical composition, removing balance from the paid setup and making the original canonical collision source explicit for its new base. No nearlinear long-query evaluator or new Lean/controller theorem is obtained. Native coverage/projection arithmetic is inherited and credited; the new setup proof closes its same-input branches with paid routines.

## 1. Inputs and paid prerequisites

Let N=P Q with distinct odd primes, ordered P<=Q. Let supplied integer m>=2 satisfy

 N<=m⁶,       m=Theta(N^(1/6)),       B=16m².

There is NO balance or P+Q<=3m³ premise. The setup below returns a proper factor or a unit beta modulo N satisfying

 ord_P(beta),ord_Q(beta) odd and>B,
 gcd(ord_P(beta),ord_Q(beta))=1,
 ord_N(beta)>B²=256m⁴,
 ord_P(beta^(m²)),ord_Q(beta^(m²))>B.                                (1)

The numerical orders are neither known nor output. Their indices in P−1,Q−1 need not be below m. All input acquisition and a fixed number of invoked procedures cost soft O(m) bits.

The paid prerequisites are:

1. Harvey--Hittmeir's deterministic large-GLOBAL-order theorem: given a target B<N−1, return a factor or alpha with ord_N(alpha)>B in soft O(sqrt(B)) bit cost at this scale.
2. The universal first-nonunit detector: for any unit u and cap H², in soft O(H) bits return a proper factor, an EXACT common local order c<=H², or NoHit certifying BOTH local orders>H². The exact-common-order conclusion follows by finding the first nonunit positive exponent, not by substituting an lcm. Its ordinary monic product/remainder trees and gcd localization handle repeated nodes and zero divisors without inversions of point differences.
3. The companion ALL-SEMIPRIME dyadic short-annihilator extractor: if a supplied unit gamma has both exact local orders odd and>B, a supplied nonzero polylog-bit global annihilator K permits factoring in soft O(N^(31/192)) bits. No balance, small-index, order primality/coprimality, multiplier bound or factorization of K is supplied. This is the new unbalanced extractor, not an unlicensed invocation of the old balanced small-index theorem. Since31/192<1/6, its cost is soft O(m).

These are classical bit algorithms, not axioms delivered to a Lean backend. The detector and HH mechanisms are inherited. The new dyadic extractor has its separate proof; the setup uses it only after explicitly computing a valid K.

If B>=N−1, ordinary trial division through floor(sqrt(N)) is affordable: sqrt(N)<=sqrt(B+1)<=4m+1. Return a factor on this explicit branch. Thus HH is called only on its stated input range. Even semiprimes and prime squares can first be factored by parity and integer-square-root checks. These observations extend the stated distinct-odd input route to all semiprimes; they do not assert this theorem handles arbitrary composite shapes without further routing.

## 2. Large global order to large odd local orders, without balance

Run HH at target B. Return its factor if found, otherwise retain alpha with ord_N(alpha)>B. Put L_2=ceil(log₂N) and gamma=alpha^(2^(L_2)), using L_2 squarings. This removes the entire local two-primary parts, so both gamma orders are odd. It costs polylogarithmic bit work.

Apply the universal detector to gamma with H=4m, exact cap B.

- Proper factor: return it.
- NoHit: retain gamma. Its odd local orders are both>B. NO small-index conclusion is drawn here on unbalanced inputs.
- Exact common odd order c<=B: write the local orders of alpha as c*2^(a_P), c*2^(a_Q). Compute alpha^c and square repeatedly, checking gcd(value−1,N), including before the first squaring. If a_P!=a_Q a proper factor appears. Otherwise the first saturated stage gives a COMPUTED common full order

 r=c*2^a=ord_P(alpha)=ord_Q(alpha)=ord_N(alpha)>B.

It has O(logN) bits. Since r divides both P−1 and Q−1,

 r²|phi(N)=N+1−(P+Q),      P>=r+1.

The new unbalanced estimate makes this known order sufficient. The function x+N/x decreases on positive x<=sqrt(N), so, as r+1<=P<=sqrt(N),

 P+Q<=r+1+N/(r+1).

Also

 r³>B³=4096m⁶>=4096N.

Thus N/(r+1)<r²/4096. Since r>B>=64, we have

 P+Q<r+1+r²/4096<r².

Therefore T=(N+1) mod r² is EXACTLY P+Q. Compute the integer square root of T²−4N and recover the two factors. No factorization of r or an unknown local order is needed. This replaces the former balance-dependent bound on the factor sum; it does not change HH's output contract.

All branches are now paid. The surviving gamma has both local odd orders>B, while the common-order branch factors directly. No source-density or majority qualification is involved.

## 3. Direct coprime refinement using an acquired annihilator only when valid

Set beta=gamma^(N−1). The existing native arithmetic gives coprime projected local orders: with g=gcd(P−1,Q−1), those orders divide (P−1)/g and (Q−1)/g. This is SemiprimeOrderSeparation.projected_orders_coprime; no primitive-root assumption, balance, or prime-order hypothesis is needed.

Run the universal detector on beta through B.

- Proper factor: return it.
- Exact common order c: since the local beta orders are coprime, c=1. Hence beta=1 modulo N. The explicit positive K=N−1 is a verified global annihilator of the ORIGINAL gamma, whose local orders are odd and>B. Invoke the new unbalanced dyadic extractor, returning a factor. The original gamma need not have small indices. No annihilator-acquisition oracle or circular promise is used.
- NoHit: both beta orders exceed B. They are odd and coprime; their exact global order D is their product>B². Keep beta. Its indices are not presumed small.

The N−1 projection, shared-order-one identity, and earlier algebraic kernel closure are already compiled. The new statement is this paid same-input all-semiprime composition, using the newly generalized extractor. It is not the first algebraic resolution of kernel branches and does not retroactively certify the old controller's full bit backend.

## 4. Certify the entire short q-unit interface

Compute q=beta^(m²). Its local orders divide their respective beta orders, so they remain coprime. Run the universal detector on q through B.

A proper factor stops. An exact common q-order must be1 by coprimality; then both beta orders divide m², contradicting their being>B. Therefore that branch is impossible. The only surviving outcome is NoHit, certifying both q-orders>B.

Consequently1−q^k is a unit modulo N for every1<=k<=B. The beta orders themselves are>B and their global product is>B². A fixed number of detector calls, HH, modular powers, roots/gcds, and at most one unbalanced extractor invocation has soft O(m) total bit cost. These certifiable scalar units do not license arbitrary quotient-algebra inversions or an unacquired long scalar product.

## 5. Factor-sum margin on the surviving unbalanced branch

Both primes now exceed B+1, since a field unit's order divides its prime minus one. Monotonicity of x+N/x again gives

 P+Q<=B+1+N/(B+1)<16m²+1+m⁴/16.                                    (2)

Here N<=m⁶ is the only size input. This is much smaller than the retained global order D>256m⁴, even for highly unbalanced P,Q. It will replace the balanced factor-sum bound in bounded global-leaf recovery below.

## 6. Canonical first-current collision coverage for the NEW beta

For the query stage take m to be an odd prime, m>=5. This can be selected from N alone at the required cost: search integers starting at ceil(N^(1/6)) (and at least5), using deterministic polynomial-bit primality tests. Bertrand's bound gives a prime within twice this starting size, so O(m) tests and soft O(m) total bits suffice. If m divides N, return that factor. Thus no prime-selection or inverse oracle is free.

On the surviving setup branch P>B>m², so in particular P is coprime to m and its own tag j=P mod m lies in1,...,m−1. Define the literal native first-current row:

 a_j=N j^(−2) mod m in1,...,m−1,
 D_j=(N−a_jj²)/m,
 b_j=centered(m,−j^(−1)D_j),
 ell_j=mb_j−2a_jj,
 delta_j=a_j+ell_j.

The exact source gives −3m²<=delta_j<=m². At the own tag there is an INTEGER index

 I=(a_jP+Q+ell_j)/m².

Native SemiprimeWideWrapCoverage.seed_index_bounds proves

 0<=I<=2m²+1                                                        (3)

from m>1, P<=Q, P>=m², N<=m⁶. It does NOT require balance or prime local orders: it uses P<=m³,Q<=m⁴ after the small-factor prefix. Here the setup already supplies the prefix P> B. Thus the interval length

 L=2m²+2

suffices. The exact integer identity is

 N+delta_j−m²I=(P−1)(Q−a_j).                                        (4)

Fermat's theorem for ANY unit beta modulo P gives beta^(N+delta_j)=q^I in that field. This is a genuine local collision in the canonical searched interval for the new beta. The native quotient_row_power_hit and the arithmetic part of SemiprimeSeedSumAcquisition.long_seed_reader_witness already implement this mechanism. Their final packaged theorem carries the old LongData/projectedUnit wrapper; no automatically compiled beta-controller theorem is claimed here.

## 7. Paid targets, deduplication and legal unit promises

The m−1 literal offsets and target powers Y_j=beta^(N+delta_j) are acquired in soft O(m) bits: public inverses/lifts are polylogarithmic per tag, beta^N is shared, and signed beta^delta_j uses known-unit powering. Sort and deduplicate the INTEGER offsets, retaining a representative offset for each target. This preserves the own-hit value from (4).

Indeed two offsets differ in absolute value by at most4m². Because each local beta order exceeds16m², distinct integer offsets give unequal targets in BOTH hidden fields. Their target difference is therefore a unit modulo N. Equal offsets are globally identical values and are publicly identifiable without factoring. Thus the deduplicated targets have unit pairwise differences, with J<=m−1.

The q-seed interval also has unit pairwise differences because its local orders>B>L. The certified short q-factorials are units. CROSS differences Y_j−q^i are allowed to be nonunits: they are the desired collision data and must not be silently inverted by a proposed evaluator. All statements survive row restriction and shortening to a common subinterval. Deduplication need not preserve a private tag name for recovery, because the bounded global-leaf method below uses the retained integer offset itself.

No long polynomial of degree L is acquired by this setup. A target polynomial of degree J can be built softly linearly if needed; acquiring its long interaction with the seed interval is the missing query work.

## 8. A bounded global leaf recovers the factor sum directly

Suppose a leaf in this canonical rectangle has global equality Y_j=q^i, for0<=i<L, or more generally i<4m². Let S=P+Q−1 and let D be the exact global beta order. Since D divides both phi(N)=N−S and N+delta_j−m²i,

 D divides S+delta_j−m²i.

Using (2), the offset interval and i<4m² gives the safe bound

 |S+delta_j−m²i|<(4+1/16)m⁴+19m²+1<256m⁴<D.

Hence this integer is zero, so

 P+Q=1+m²i−delta_j.                                                  (5)

A single exact square root recovers the factors. This works for ANY globally colliding public row, not only the private own tag. It has no prime-local-order or literal-base2 requirement. It is the existing phase-sum mechanism under the new certified order and unbalanced factor-sum bounds, not a new recovery identity. There is no need to invoke the wide-annihilator extractor at these bounded leaves, nor to assume that an arbitrary reorigining preserves interval coverage.

## 9. Exact unpaid acquisition interface

Let Delta be the publicly deduplicated offset set. One sufficient interface is a restriction-stable deterministic evaluator that, for any supplied subset A of Delta and any COMMON seed subinterval [a,a+ell) contained in[0,L), returns either a proper factor or the exact scalar

 V(A,a,ell)=product_(delta in A) product_(i=a)^(a+ell−1)
                     (beta^(N+delta)−q^i) modulo N.                  (6)

All source acquisition, constants, endpoint powers and nonunit branches must be charged. A bound soft O(|A|+sqrt(ell)) ring operations with the corresponding residue-bit cost would suffice; even a uniform soft O(m)-bit bound for each such restricted call is enough here. Empty products equal1. The evaluator must allow actual cross collisions, saturated products and the legal source promises of section7.

By (4), V(Delta,0,L) is nonunit. A proper gcd with N finishes. A saturated gcd can be localized by binary restriction of rows and then of the common interval: inspect child products, return a proper child gcd if found, discard a unit child, and otherwise keep a saturated child. There are O(logm) levels. At a leaf, a proper gcd is a factor and a saturated gcd gives the global equality handled by (5). Repeated values were already deduplicated and do not change the product/gcd argument.

Thus a paid evaluator of (6), or an equivalent factor/nonunit-witness oracle with the same complete guarantees, would close the all-semiprime pipeline in soft O(m) bit cost. A full norm returning zero modulo N WITHOUT restriction or witness guarantees does not by itself supply this localization contract. This is a precise sufficient interface, not a claim that no other scalar recovery route is possible.

The general existing product bound remains soft O(J+sqrt(JL)), namely soft O(m^(3/2)) here. The new setup, legal unit promises, and exact arithmetic coverage do not improve that acquisition bound. No full-query evaluator, new Lean declaration, automatic compilation of the original controller for beta, all-input sixth-rate bit theorem, or operation lower bound is asserted. Source and prerequisite pins accompany this report; no native edits or broad builds are used.

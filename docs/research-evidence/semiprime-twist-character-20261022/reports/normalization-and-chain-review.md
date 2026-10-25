# Review: outside-product normalization and public q-chain acquisition

2026-10-22. This reviews the constructive interface, maps it to the current covered canonical query, and identifies the unpaid varying-stride consumer. No universal acquisition improvement, implementation, or repository changes.

## 1. Application to the actual covered query

The current canonical long query consists of P_L(z_j;q), where

 z_j=gamma^(-E_j), E_j=N+delta_j, q=gamma^(m²).

The existing inverse-reflection involution pairs m−3 tags; the fixed tag and the tag without a partner leave at most two unpaired tags. Retain those separately. For each actual pair, c_j=E_j+E'_j is positive in the asymptotic balanced regime, or its sign is directly checked from the public integers. With A=product_j c_j and r_j=A/c_j, apply exponent r_j to BOTH pair anchors AND its stride. Then

 z_j^(r_j) z'_j^(r_j)=gamma^(-A), q_j=q^(r_j), q_j^(c_j)=q^A.

The resulting query is P_L(z_j^(r_j);q_j)P_L(z'_j^(r_j);q_j). Each original local zero survives, so together with the unpaired tags this is an actual covering query, not merely optional arbitrary paired input. Degenerate zero centers must be retained without normalization; mixed center signs may be split into two classes. The current large positive E_j make this unnecessary after the explicit public check.

Outside-product exponent propagation acquires all modular bases in soft O(B), B=sum_j bitlen(c_j), without materializing all long r_j. A product tree retains A; the one selected r_j is recovered in soft O(B). For B=soft O(m), the metadata is paid.

### Newly integer-trivial collisions do NOT appear

The selected original exponent is K=−E_j+m²i (or the equivalent sign convention). Its transformed exponent is r_j K. Since r_j is a nonzero integer,

 r_j K=0 as an INTEGER iff K=0 as an INTEGER.

Powering can create many modular equalities by collapsing some local order. Those are genuine nonzero annihilators of the original prepared gamma when K!=0, with bit length O(B+bitlen K). They may help acquisition but are not integer-trivial errors. Monic localization tolerates repeated residues and roots; a saturated leaf gives the nonzero original-gamma annihilator r_j K. The decoder's hypotheses refer to original gamma, so it is unnecessary that gamma^(r_j) retain large orders.

On the canonical range one can check N−3m²>m²(L−1) publicly, which excludes all K=0 leaves at once. Otherwise apply the inherited exact integer-root/trivial-leaf handling. In a generic Gauss row there is at most one integer-zero sigma per row, unchanged by nonzero powering.

### Consumer cost remains unpaid

The native shared routine uses ONE baby base q. It cannot be passed q_j varying with j. A safe per-pair monic baby/giant evaluation/localization costs soft O(sqrt L) per pair, independently of order collapse, hence soft O(J sqrt L+B+decoder). At J~m,L~m² this is soft m², worse than the native shared m^(3/2) query. No faster consumer for these particular q_j is proved. Common centers alone therefore have not helped the current acquisition rate.

## 2. Binomial-curve resultants: useful exact formula, no hidden degree saving

The formal curve X^c=Q has degree c, not bitlen(c). A quotient-ring algorithm using a dense basis has dimension c. A binary exponent circuit uses only O(log c) gates, but replacing it by quadratic auxiliary equations does not grant cheap elimination: its elimination degree is still c. No supplied primary result removes that charge here.

Nevertheless this particular binomial norm has an exact fast formula, so degree alone must NOT be used as a general computation lower bound. For c>=1,i>=0,g=gcd(c,i),

 Res_X(X^c−Q,1−zX^i)=(1−z^(c/g)Q^(i/g))^g.

This follows over characteristic zero by grouping the c roots under X->X^i, and then holds as an integer polynomial identity in Q,z over arbitrary rings, including characteristics dividing c. At i=0 it gives (1−z)^c. Each individual norm is computable with logarithmic powering in c and i.

For the normalized query z=gamma^(r e), Q=q^A=gamma^(Ad), c=c_j and r=A/c, the binomial factor is

 1−gamma^((A/g)(e+di)).

Thus a zero of this norm gives a decodable multiple of the original exponent, even if its common-root interpretation uses a sheet other than the supplied q_j. But multiplicativity of resultants leaves a PRODUCT OVER ALL L indices, with g=gcd(c,i) varying. No O(B)-degree polynomial or free evaluation of that product follows.

Where g=1, the norm returns the original common-stride query powered by A: common base gamma^A, with the old row-dependent pair centers restored. For other g it creates queries at gamma^(A/g), partitioned by gcd(c,i). Enumerating those partitions or all factors still has its charge. Factoring the potentially large c is not a supplied free input. The formula therefore exposes the exact favorable structure but does not close the long-query computation.

## 3. A paid public factor-or-chain acquisition lemma

There is a stronger constructive alternative to assuming a hidden-field gcd oracle. Suppose supplied integer exponents e_1,...,e_J and d define z_i=gamma^(e_i), q=gamma^d, with original prepared gamma. All e_i,d have charged short bit length. Then in soft O(J+decoder) work one can either factor N or publicly certify that EVERY local q-overlap among these supplied nodes is an exact integer exponent edge e_i+d=e_j. The decoder term includes one selected nonzero exponent's bit length and the inherited N^(1/12) cost.

First deduplicate equal INTEGER exponents. Equal exponents with different query intervals retain their interval labels; this prepass concerns the node set only. Build H(X)=product_i(X−z_i) by monic trees. Compute H'(z_i) at all nodes in soft O(J). A nonunit derivative means a nonunit pair difference. Localize one such pair using the product tree excluding its own leaf. A proper gcd factors N; a saturated pair gives gamma^(e_i−e_j)=1, where e_i−e_j!=0 because of integer deduplication, and the reviewed decoder factors. This step either factors or certifies all distinct node differences are units in BOTH fields.

Now sort the integer exponents and find every exact formal neighbor e_j=e_i+d. Such an edge is the SAME numerical edge in both fields. Unit pair differences certify that its source cannot have any other local successor, so it may be skipped safely.

Evaluate H(qz_i) for all remaining sources using one monic multipoint evaluation. If every gcd is 1, no other local q-overlap exists. A proper gcd factors. If a value is saturated, descend H's product tree at qz_i. Different local successor leaves separate into a proper gcd during descent. If one leaf is saturated, qz_i=z_j modN gives gamma^(e_i+d−e_j)=1. The exponent is nonzero because formal neighbors were skipped, so one decoder call factors.

This handles gcd=N by localization; it never interprets a saturated coefficient as an inverse. All polynomial arithmetic used is monic and remains valid with repeated evaluation points. Only one nonunit pair/edge needs full descent, so localization costs soft O(J), not J².

If the routine returns the formal graph instead of a factor, it also constructs a monic gcd without arbitrary ring pivots:

 gcd_monic(H(X),H(qX))=product_(i: e_i+d is a listed exponent)(X−z_i).

Its local reductions are the field gcds, because both fields now have exactly the same known graph and simple nodes. Constructing it takes soft O(J).

In particular differing local overlap DEGREE forces a factor, but so does any nonformal local overlap, even if the two degrees agree. Ordinary Euclidean/subresultant algorithms should also encounter a proper nonunit pivot when the local gcd degrees differ, but the explicit monic-evaluation approach supplies the paid algorithm and a stronger certificate directly.

## 4. What this lemma does and does not acquire

For the literal canonical family, the already established order bound >16m² and small delta span force all q-overlaps to be those exact integer edges. Thus the prepass is valid and public but does not guarantee a factor there; it recovers the previously known short-chain graph. Each low-digit fiber has at most two tags, so this graph does not give long chains whose positive orbit union would collapse JL supports to L+J.

For a different actual Gauss family, the prepass can reveal useful modular wrap/cross-field disagreement without factors as inputs. If it certifies only a sparse formal graph, a new arithmetic coverage theorem is still needed to force enough positive overlap or another cheap query. This is a public chain-acquisition INTERFACE, not a universal collision-acquisition theorem.

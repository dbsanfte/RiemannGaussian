# Direct route from the paid strong-order setup

2026-10-22. Verified optional public order normalization against the newer unconditional setup; no claim of novelty over the earlier projection work. No frozen files changed. This does not give a complete sixth-rate factoring algorithm or an acquired annihilator on every branch. See order-cleaning-independent-review.md for the inherited smooth-projection/root provenance.

## Starting contract

Use the proved classical setup in `docs/research-evidence/semiprime-unbalanced-annihilator-20261016/reports/uniform-setup-and-query-interface.md:7–80`. For N=PQ distinct odd primes, public N<=m^6, m=Theta(N^(1/6)), it returns a factor or beta whose odd local orders r_P,r_Q exceed B=16m², are coprime, and whose global order is their product>B². q=beta^(m²) also has both local orders>B. beta is an explicitly computed (N−1)-power of a preceding unit, not a hidden primitive root.

The exact-first-nonunit detector has soft O(m) bit cost through B and returns a proper factor, exact COMMON local order<=B, or both orders>B. With coprime local orders, its common-order output can only be1. The existing unbalanced Burgess extractor accepts a nonzero polylog-bit global annihilator of the ORIGINAL beta and factors in soft O(N^(31/192)), without QRH.

## A paid order-cleaning lemma

Supply any public nonzero integer A of polylogarithmic binary length. Let T=ceil(log2 N) and compute

 K=|A|^T,             b=beta^K mod N.

K has polylogarithmic binary length and is actually constructed; computing b costs polylogarithmic bit work. The case |A|=1 simply leaves beta unchanged. At each hidden prime,

 ord(b)=r/gcd(r,|A|^T).

Every prime-power exponent dividing r is below log2 N, since r<N. Therefore all prime divisors shared with A have been COMPLETELY removed: gcd(ord(b),A)=1. Oddness and pairwise coprimality of the two local orders persist.

Run the exact detector through B ONCE, after this computation.

* Proper factor: return it.
* Common local order: coprimality forces both orders=1, hence b=1 modulo N. The explicitly computed nonzero K is now a verified global annihilator of ORIGINAL beta. Its original large odd local orders satisfy the Burgess extractor's promises, so factor within soft O(m).
* NoHit: retain b. Both local orders>B are odd, coprime, and additionally prime to A. Their global order remains>B².

A final detector on b^(m²) restores the original q-order interface: a common order would have to be1, making both b orders divide m², contrary to their being>B. Thus this call either factors or certifies both q orders>B. Total cost is soft O(m), with no unknown order, factorization of A, or hidden factor supplied.

In particular A=N−1 gives a rigorous factor-or-base contract with gcd(ord_N(b),N−1)=1. The previously known beta=gamma^(N−1) does NOT already imply that coprimality: a single powering may only partially reduce a shared prime-adic valuation. The high enough power above removes it completely.

This is a constructive reduction of the surviving family, not an assertion that all remaining inputs factor. It can also use, for example, A=N²−1, or a polylog-length product of prescribed N^k−1. Coverage of all possible surviving order primes is not proved.

## Exact surviving arithmetic

After A=N−1 cleaning, r'_P divides P−1 but gcd(r'_P,Q−1)=1, since N−1=Q(P−1)+(Q−1); analogously r'_Q is prime to P−1. This separates the retained orders from the OTHER FULL FIELD order, stronger than coprimality with just the other retained beta order.

However neither r'_P nor r'_Q is numerically acquired. The relation beta=gamma^(N−1), and its cleaned analogue, describes an image of a public powering map; it does not output the inverse of that map or its order. In the stable branch that public powering is an automorphism of the retained cyclic subgroup, but its inverse exponent still depends on the unknown subgroup order.

One useful index inequality is genuinely available: P<=sqrt N<=m³ gives (P−1)/r'_P < m/16. The other index can be much larger, because Q can approach m^4/16. Thus one small local coindex exists as a hidden integer; it is not a supplied residue modulus or a computed annihilator. Existing known-modulus residue algorithms cannot simply take it as input.

Public Frobenius still says b^N=b^(P+Q−1). This reduces the unknown exponent to a factor sum but does not acquire it. The retained bound P+Q<16m²+1+m⁴/16 gives an interval of order m⁴, whose ordinary baby/giant clock is order m² rather than m. No new shorter interval is implied by the cleaned gcd condition.

## Sparse norms and relevant primary interface

The newly paid sheared cyclic norms and one fixed tangent have genuine soft(h+L) construction cost. They work with a PUBLIC cyclic relation X^m=Y and known narrow support. None of their evaluated unit norm identities supplies a numerical annihilator of b on the cleaned branch. Replacing that defining relation by X^(P−1)=1 or a hidden local-order relation would introduce exactly the unknown factor/order. This is a boundary of the currently proved primitive, not a lower bound on other norm constructions.

Primary literature inspected: Harvey–Hittmeir, *Deterministic methods for finding elements of large multiplicative order*, arXiv:2601.11131v2 (5 June 2026), Theorem1.1, printed p3, https://arxiv.org/pdf/2601.11131v2. It provides a deterministic factor-or-element-above-D algorithm with essentially square-root-D cost; it does not convert a supplied already-large order element into a short annihilator. Its introduction pp2–3 distinguishes acquired exact orders from mere lower bounds. This supports the paid setup, not an additional inverse-order oracle.

## Outcome and immediate actionable use

The order-cleaning lemma is a verified optional soft-m preprocessing step, with every exceptional branch closed by an ACTUALLY COMPUTED short annihilator. It removes any need to reason separately about partial (N−1)-valuation removal in future direct-order attempts. It also preserves the canonical scalar coverage, since that coverage holds for any retained unit with the prepared large/coprime-order and q-order promises. This normalization is not counted as a whole-query acquisition advance.

No theorem found here forces a final annihilator or proper factor when the cleaned base survives. Thus the full row query has not been bypassed. A future direct route may assume, after a paid factor-or-cleaning reduction, that each local order is coprime to the other full field order. It must still acquire some numerical relation rather than infer it from these divisibility facts.

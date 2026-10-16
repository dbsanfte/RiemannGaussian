# Uniform preprocessing to two large odd local orders, or a factor

2026-10-16. Deterministic classical preprocessing. This removes the prime-local-order and original-family restrictions from this particular setup interface. It does not acquire an annihilator, prove collision coverage, or evaluate a long query.

## Theorem and input

Let N=P Q with distinct odd primes P,Q, and let m>=2 be an integer satisfying

    N<=m^6,       P+Q<=3m^3.

Only N,m are input; the factors are proof witnesses. There is a deterministic algorithm using soft-O(m log N) bit operations (equivalently soft-O(m) in this scale) which returns either a proper factor of N, or a unit gamma modulo N for which the exact local orders r_P,r_Q satisfy

    r_P,r_Q odd,       r_P,r_Q>16m^2,
    (P−1)/r_P<m,       (Q−1)/r_Q<m.

No primality or coprimality assertion about r_P,r_Q is made. They need not be distinct and are not computed. Even inputs and perfect squares can first be factored by gcd/integer-square-root checks. More general fixed balance constants can be handled by adjusting the fixed target constant; the theorem here keeps the displayed numerical assumptions.

## 1. Exact external input: deterministic large GLOBAL order

Use Harvey--Hittmeir, Deterministic methods for finding elements of large multiplicative order, arXiv2601.11131v2, Theorem1.1, printedp3. Primary PDF: https://arxiv.org/pdf/2601.11131 . The authors define time throughout as steps of a deterministic multitape Turing machine (printedp2).

For integers N>=3 and 1<=B<N−1, the theorem deterministically returns either a nontrivial divisor of N or a unit alpha modulo N with ord_N(alpha)>B. Its bit-time bound is

    O(sqrt(B) log(B) log(N)/sqrt(log log B)),

with the standard bounded modification for small B. It need not return the order or any factorization of it. This is a global-order guarantee; it does not directly imply that both hidden local orders exceed B.

Set B=16m². If B>=N−1, perform ordinary deterministic trial division through floor(sqrt N). In this branch sqrt N<=sqrt(B+1)<=4m+1, so even this explicit fallback costs soft-O(m log N) bits. In the intended m=Theta(N^(1/6)) scale it is only a small-input branch, but no unknown finite threshold is needed.

Otherwise invoke Theorem1.1. Return its factor if one is produced. Retain its unit alpha and global-order guarantee. Since sqrt B=4m, this invocation has the claimed soft-O(m log N) bit cost.

## 2. Universal first-nonunit detector contract

The following elementary detector is needed in its UNPROMISED form, not just a small-order-promise version. Given a unit b modulo N and a search cap H², it deterministically returns one of:

1. a proper factor of N;
2. an integer c<=H² certifying the EXACT equality ord_P(b)=ord_Q(b)=c;
3. NoHit, certifying BOTH ord_P(b)>H² and ord_Q(b)>H².

Its bit cost is soft-O(H log N). In particular a saturated output is not merely a shared annihilating exponent or the global lcm of two unequal orders.

For completeness, construct babies b^i for0<=i<H, giants b^(Hj) for1<=j<=H, and f(X)=product_(i=0)^(H−1)(X−b^i). Evaluate f at all giants using balanced monic product/remainder trees. Scan the rows j increasingly and compute gcd(f(b^(Hj)),N). A proper gcd is a factor. If every gcd is1, every exponent1,...,H² has b^t−1 a unit, so neither local order can lie in that range: return NoHit.

At the first gcd-N row, localize through the retained baby tree, always inspecting larger i first. A proper child gcd is a factor; a unit child contains only unit leaves and may be discarded; a gcd-N child may be descended into. At a gcd-N leaf output c=Hj−i. The leaf identity

    b^(Hj)−b^i=b^i(b^(Hj−i)−1)

shows that exponents are inspected in increasing positive order, since rowj covers (j−1)H+1,...,jH and larger i gives smaller exponent. All earlier exponents are certified units. Both hidden local orders divide c, but neither is smaller than c; hence both are exactly c. This remains true without a prior order bound.

All evaluation divisions are by monic polynomials; reciprocal-series constant1 needs no nonunit inversion. Repeated babies/giants do not affect evaluation or the factor/unit logic. Balanced trees cost soft-O(H) ring operations. Localization by Horner evaluation has geometrically decreasing total sibling degrees O(H), plus O(logH) gcds. The row scan uses H gcds. Fast integer polynomial arithmetic and residue reduction give soft-O(H logN) bit cost and storage up to ordinary logarithmic factors. This is the universal extension of the separately written small-order separator; no unprovided order oracle is assumed.

## 3. Remove the local two-parts

Let L=ceil(log2 N) and form

    gamma=alpha^(2^L) modulo N

by L successive squarings. This costs polylog N bits. Each exact local order of alpha divides the corresponding prime minus1 and is less than N. Its2-part therefore divides2^L. Raising alpha to2^L removes that entire2-part and leaves its exact odd part unchanged. Thus gamma has odd local orders, whether large or small.

Run the universal detector on gamma with H=4m. Its tested cap H² is EXACTLY B=16m².

- ProperFactor: return it.
- NoHit: both exact odd local orders r_P,r_Q exceed B. Their integer indices satisfy

      (P−1)/r_P < 3m³/(16m²)=3m/16<m,

  and similarly for Q. Return gamma. This is the required surviving-base branch.
- CommonOrder: the detector supplies the exact common odd local order c<=B. Continue below; merely knowing a shared multiple would not suffice.

## 4. A common odd local order also yields a factor

Write the local orders of alpha, using their now-known equal odd parts, as

    ord_P(alpha)=c*2^a_P,       ord_Q(alpha)=c*2^a_Q.

These exponents are proof witnesses. Since c is odd, z=alpha^c has local orders exactly2^a_P and2^a_Q. Compute z, then repeatedly square it, checking gcd(z−1,N) at each stage, including before the first squaring. A proper gcd is a factor. At most L squarings are needed before both components are1.

If a_P!=a_Q, at the smaller of these exponents one component is1 while the other is not; its gcd is proper. Therefore, if the first gcd-N stage is reached without a prior proper gcd, its index a certifies a_P=a_Q=a exactly. The common FULL local order of alpha is then

    r=c*2^a.

This is a computed integer of O(logN) bits. It is also the global order of alpha. The Harvey--Hittmeir guarantee consequently gives r>B. Exact local-order divisibility gives r|(P−1) and r|(Q−1), hence

    r² | (P−1)(Q−1)=N+1−(P+Q).

Since r²>B²=256m⁴>3m³>=P+Q>0, the least nonnegative residue

    T=(N+1) mod r²

is EXACTLY P+Q. Compute Delta=T²−4N and its integer square root; the roots (T±sqrt Delta)/2 recover P,Q. Under the promised semiprime input Delta=(P−Q)², so all exactness/parity assertions follow. The final factors can be verified by multiplication.

The power alpha^c, squaring/gcd chain, integer remainder, square root and factor verification require only polylog N bit work. No factorization of c,r, or either prime minus1 is used. If c=1 the proof still applies. A common-order return followed by a=0 would contradict r=c<=B<ord_N(alpha), so that impossible subcase need not be separately assumed away.

## 5. Complete paid interface and limits

All branches either return a proper factor or the specified gamma. Harvey--Hittmeir and the universal detector each cost soft-O(m logN); every remaining step is polylogarithmic in N,m. The trial-division fallback is explicitly affordable when required by B>=N−1. No random choices, hidden orders, factor-dependent centers, analytic nonresidue bounds, or supplied annihilator occur in this preprocessing algorithm.

The output orders can be arbitrary odd integers. This is sufficient for the later conditional wide-annihilator extraction algebra: if a nonzero K annihilates gamma globally, its odd part is divisible by both r_P,r_Q, so for every unit a the local orders of a^(Kodd) divide their respective indices. Indeed if d|r_i v_i and r_i|Kodd, then d/gcd(d,Kodd)|v_i prime by prime, without assuming gcd(r_i,v_i)=1. Odd powering also preserves each2-primary order. This observation does not acquire K or include its later extraction cost in the present setup theorem.

The original strong-order collision-coverage and phase-recovery theorems are NOT automatically inherited by this redesigned gamma; this report proves only the stated order/index interface or factor. In particular no global-order lower bound proportional to m⁴, no prime local orders, no full-query algorithm, no all-input collision controller, and no Lean sixth-rate composition is claimed. The positive result is uniform balanced preprocessing usable by an independently proved conditional extractor.

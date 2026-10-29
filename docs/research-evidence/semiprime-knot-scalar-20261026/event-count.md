# Literal continuous-tag HH event covers: descriptor lower bound

26 October 2026. Independent proof audit of the root's proposed measure argument. Verdict: it works for the stated *full continuous-tag covering problem*. In fact the small-coefficient contribution is O(delta²), without a logarithmic loss. This does not prove a lower bound for actual-semiprime-specific coverage, the knot prefix primitive, or another implicit acquisition algorithm.

## The precise covering problem

Let k=2*3^e, e>=1, N coprime to k, and delta>0. A descriptor is a nonzero integer pair (a,b). It covers the set

    C(a,b)={(sigma,t): sigma in (Z/kZ)^*, 1<=t<=4,
               aN=b sigma² mod k, |at-b|<=delta}.

Measure this set by counting measure in sigma times ordinary Lebesgue measure in t. The whole domain has measure

    3 phi(k)=k.

For delta<k and k larger than an absolute constant, a cover by R descriptors satisfies

    k <= C1 delta² + C2 delta sqrt(R tau(k)),             (1)

for absolute constants C1,C2. In particular if delta=C sqrt(k/r), with C fixed and r larger than a sufficiently large constant depending on C, then

    R = Omega(kr/tau(k)) = Omega(kr/log k).              (2)

If r grows as a fixed positive power of k, this is superlinear even allowing arbitrary polylogarithmic factors in an O(k) descriptor budget.

This covering problem is a relaxation of the literal HH transverse constraints on balanced bins: with t=N/B² in [1,4], dividing |aN/B-bB|<=2sqrt(Nk/r) by B yields |at-b|<=2sqrt(kt/r)<=4sqrt(k/r). A descriptor satisfying the original constraint therefore lies inside the relaxed cover with C=4. A lower bound for the relaxed cover applies to the original full-domain cover.

## 1. Content normalization is legitimate for this cover

Write a=h a0,b=h b0, where h=gcd(|a|,|b|)>0 and gcd(|a0|,|b0|)=1. Let d=gcd(h,k). Since h/d is invertible modulo k/d,

    aN=b sigma² mod k
       iff a0N=b0 sigma² mod (k/d).

Replace (a,b) by (d a0,d b0). The tag congruence is unchanged and

    |d a0 t-d b0|=(d/h)|at-b|<=|at-b|.

Thus the replacement covers a superset and does not increase descriptor count. It suffices to prove the lower bound when every descriptor has content d|k. This normalization is purely about this covering problem; it is not asserted to preserve some arbitrary original integer leaf label or a factoring consumer.

Simultaneous negation leaves the covered set unchanged, so when a!=0 take a>0. Descriptors that become equal after normalization may be deduplicated.

## 2. Number of compatible unit tags

For a=d a0,b=d b0 with d|k, put n=k/d. If n>1, the congruence is a0N=b0 sigma² mod n. At any prime dividing n, if either a0 or b0 were divisible by that prime, both would be, contradicting primitiveness. Hence both are units modulo n.

The congruence is therefore a square-root equation modulo n, where n divides 2*3^e. It has at most two solutions modulo n: at most two at the odd prime power and at most one unit solution at the possible factor 2. Each such residue has at most d lifts modulo k. Thus the number of compatible unit sigma is at most 2d. For n=1 it is phi(k)<=k=d, also satisfying the bound.

Axis descriptors require separate treatment, because the preceding unit argument used both coordinates. If a=0 or b=0, primitiveness makes the other primitive coordinate ±1, and compatibility forces n=1, hence d=k. The nonzero coordinate then has magnitude k. Such a descriptor cannot satisfy |at-b|<=delta anywhere in [1,4] when delta<k. Axes therefore cover no part of the domain under the theorem's hypothesis.

## 3. Small coefficients cover O(delta²) total measure

Consider all normalized descriptors with 0<a<=2delta that cover a nonempty t interval. They necessarily have |b|<=4a+delta<=9delta. For a fixed d|k, the primitive coordinates obey

    1<=a0<=2delta/d,  |b0|<=9delta/d.

A nonempty set requires d<=2delta. The number of such integer pairs is O((delta/d)²), uniformly also when delta/d is between 1/2 and 1. Dropping the primitive and congruence restrictions only increases this count. Each pair has at most 2d compatible tags and interval length at most 3, hence contributes at most O(d) measure. Summing gives

    total small-coefficient measure
      <=O(delta²) sum_(d|k)1/d
      <=O(delta²)(1+1/2) sum_(j>=0)3^-j
      =O(delta²).                                      (3)

This includes the possible b=0 descriptors in the count, although the compatible ones were already shown not to hit. Negative b and the a<=delta range are included. There are no omitted large-a opposite-sign descriptors: t>=1 and a>2delta force b>=a-delta>a/2>0.

## 4. Large coefficients: weighted descriptor capacity

For a>2delta and a valid t, one has

    a/2 < b < (9/2)a.

Writing a=d a0,b=d b0 therefore gives a0/2<b0<(9/2)a0. For each fixed positive integer a0, there are O(a0) possible integer b0 and tau(k) possible d|k. Thus at most

    O(a0 tau(k))                                       (4)

distinct normalized descriptors occur at that level. No finite upper bound on a or b is needed.

The t interval for a descriptor has length at most 2delta/a=2delta/(d a0). Multiplying by at most 2d compatible tags bounds its measure by

    4delta/a0.                                         (5)

For any selected R large-coefficient descriptors, their sum of 1/a0 is O(sqrt(R tau(k))). To see this, split at an integer T>=1. Levels a0<=T contribute O(T tau(k)) by (4); the remaining R descriptors contribute at most R/T. Taking T of order sqrt(R/tau(k)) gives the claim when R>=tau(k). If R<tau(k), the direct bound R<=sqrt(R tau(k)) handles it. Hence their combined union measure is at most

    O(delta sqrt(R tau(k))).                            (6)

Overlaps only reduce union measure; no independence hypothesis is being used.

Combining (3),(6) with domain measure k proves (1). If delta²=C² k/r, then for r sufficiently large the first term is at most k/2. The second term must then be at least k/2; squaring gives (2). Since tau(2*3^e)=2(e+1)=Theta(log k), the proposed logarithmic denominator follows.

## What this settles and what it does not

The proof rules out a literal positive-pair/event-enumeration strategy that acquires only soft(k) descriptors and requires them to meet the HH-type transverse condition for *every* unit residue sigma and *every* balanced real scale t in [1,4], while choosing r=k^epsilon. It already allows arbitrary coefficient sizes, content normalization, overlapping validity intervals and deduplication. It therefore removes the hope that simple parametric continued-fraction event reuse alone achieves that full-domain descriptor budget.

The actual factorization input has only its two factor points, with their residues and scales linked by P*Q=N; they do not range independently over this whole product domain. A covering family specifically proved sufficient only on those actual semiprime points need not obey the full-domain premise. The bound likewise does not exclude a different collision mechanism, an implicit norm algorithm that does not acquire descriptors individually, or a new coverage theorem using fewer required points. It is not a factoring lower bound.

No numerical experiments are used. The argument is an exact measure/counting proof for this scoped constructor and complements, rather than replaces, the previous center-drift calculation.

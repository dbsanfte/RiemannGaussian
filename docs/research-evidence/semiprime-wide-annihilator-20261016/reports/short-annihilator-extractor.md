# Factoring from an arbitrary short annihilator of a small-index odd-order base

2026-10-16. A conditional deterministic bit algorithm. The supplied annihilator may have an arbitrarily large multiplier relative to the base's exact order. Its bit length, rather than that multiplier, is charged. This proof does not acquire the annihilator and makes no Lean or literature-priority claim.

## 1. Input contract and result

Let N=P Q, where P,Q are distinct odd primes and P,Q<=C sqrt(N) for a fixed balance constant C. Let m=Theta(N^(1/6)) be a supplied positive integer. Suppose a supplied unit gamma modulo N has exact local orders r_P,r_Q satisfying

 r_P,r_Q odd,   (P-1)/r_P<m,   (Q-1)/r_Q<m.                         (1)

Neither local order, factor, nor index is an algorithm input. The local orders need not be prime, distinct, or coprime to their indices. Suppose also that a supplied nonzero integer K satisfies

 gamma^K=1 modulo N,   bitlen(K)<=O((log N)^A)                       (2)

for a fixed constant A. We may check the displayed modular equality in polylogarithmic bit time. A negative K can be replaced by its absolute value. A zero K is rejected.

There is a deterministic factoring algorithm, under (1)-(2), with bit cost

 soft O(N^(5/32)+N^(5/64)*sqrt(m)+sqrt(m))
     =soft O(N^(31/192))=soft O(N^(1/6)).                           (3)

The soft notation suppresses fixed powers of logarithms of N, m, and the encoding of K. The bound includes reading K and modular powering by K; K need not have O(log N) bits. The theorem holds asymptotically for every input satisfying the promises, rather than merely for a density-one family. An explicit fallback described below makes the algorithm total without knowing any analytic threshold.

There is no hypothesis |K|/ord_N(gamma)<=m², and no need to factor K. The separate uniform-preprocessing theorem constructs either a factor or a base satisfying (1) for every balanced semiprime in its stated range at soft O(m) cost. That construction does not supply K. Thus this extractor also applies to the previous qualified source, and its use there introduces no new source exception.

## 2. Paid small-local-order separator

Use the independently specified separator in small-order-separator.md. For any unit b and supplied bound M it takes soft O(sqrt(M)) ring operations, or soft O(sqrt(M) log N) bit operations. It returns a proper factor of N, an EXACT common local order ord_P(b)=ord_Q(b)=t, or NoHit. If both local orders are at most M, NoHit is impossible. Outside that promise any factor or exact-common-order return is still valid, and NoHit certifies that both local orders exceed ceil(sqrt(M))².

For clarity, this is the ordinary monic multipoint construction, which is valid over Z/NZ. Set H=ceil(sqrt(M)), use babies b^i (0<=i<H), the polynomial F(X)=product_i(X-b^i), and giants b^(Hj) (1<=j<=H). Each row F(b^(Hj)) tests exponents (j-1)H+1,...,jH. Scan rows in increasing j and localize the first saturated row using the retained baby product tree, visiting larger i first. A proper gcd gives a factor; a saturated leaf at exponent t, with every earlier exponent a unit, proves t=min(ord_P b,ord_Q b) and both orders divide t. Hence both equal t. NoHit means all exponents 1..H² have unit differences, so both orders exceed H².

Repeated nodes and zero divisors cause no gap: all polynomial divisions are monic, point differences are never inverted, and gcd(0,N)=N is explicitly handled. Product/remainder trees cost soft O(H), and evaluating sibling polynomials along the localization path costs O(H) by geometrically decreasing degrees. The separator does not assume an already known global order or a factorization of one.

## 3. Odd powering reduces every trial base to small local order

Remove all factors of two from |K|, obtaining the positive odd integer K_0. Because both r_P,r_Q are odd and divide K, both divide K_0. For any trial unit a, put b=a^(K_0) modulo N. If v=(P-1)/r_P, then

 b^v = a^(K_0 v) = (a^(P-1))^(K_0/r_P) = 1 modulo P.               (4)

Thus ord_P(b) divides v<m; similarly ord_Q(b) divides w=(Q-1)/r_Q<m. This direct argument also covers a common prime factor of r_P and v. No cancellation based on coprimality is used.

For either hidden prime ell, if s=ord_ell(a), then

 ord_ell(a^(K_0))=s/gcd(s,K_0).

Since K_0 is odd, this preserves the entire 2-primary part of the local order of a. Consequently every trial base can be sent to the separator with the public bound M=m, while the distinction between its two local 2-primary orders is retained. Reading, stripping, and powering by K_0 have polylogarithmic bit cost per trial base under (2).

## 4. The unconditional analytic input

Lau--Wu, On the least quadratic non-residue, Theorem 1 (printed page 2), gives the following least-character-nonresidue bound: for every nonprincipal Dirichlet character chi modulo a cubefree q and every fixed epsilon>0,

 min{n>=1: chi(n) not in {0,1}} <<_epsilon q^(c_B+epsilon),
 c_B=1/(4 sqrt(e))<5/32.                                            (5)

Primary source: https://hkumath.hku.hk/~imr/IMRPreprintSeries/2007/IMR2007-4.pdf . The pinned source was inspected at the theorem and its composite-modulus proof in Section 2. In particular (5) is a uniform cubefree-modulus theorem, not just a prime-modulus bound or an almost-all-character assertion. No GRH or quasi-RH hypothesis is used.

For odd squarefree N=P Q, the character chi_N(a)=Jacobi(a,N) is nonprincipal modulo N and N is cubefree. Thus, for all sufficiently large N, some integer a<=ceil(N^(5/32)) has Jacobi symbol -1. This follows by fixing epsilon strictly between 0 and 5/32-c_B and absorbing the implied constant using the remaining exponent margin.

For either hidden prime ell<=C sqrt(N), its Legendre character also satisfies (5). The same choice of epsilon and the fixed balance constant imply that some a<=ceil(N^(5/64)) is a quadratic nonresidue modulo ell, for all sufficiently large N. This applies to either field, regardless of which prime is numerically larger.

## 5. Find one Jacobi-minus base cheaply

Let A_1=ceil(N^(5/32)). Scan the integers a=2,...,A_1 in increasing order, using only integer gcd and Jacobi computations. A proper gcd with N immediately factors N. Skip any gcd-N value in finite exceptional cases. Stop at the first unit a with Jacobi(a,N)=-1. For sufficiently large N such a exists by (5).

Only AFTER finding this base, compute b=a^(K_0) and invoke the separator with bound m ONCE. If it returns a factor, stop. Otherwise (4) excludes NoHit, so it returns the exact common local order.

Write s_P=nu_2(P-1), s_Q=nu_2(Q-1). In a prime field with multiplicative group size 2^s u (u odd), a quadratic nonresidue has 2-primary order 2^s; a residue has 2-primary order at most 2^(s-1). This follows by writing a as a power of a primitive root for proof purposes; the algorithm does not compute that root or either Legendre symbol.

Jacobi(a,N)=-1 means the two Legendre symbols are opposite. If s_P=s_Q, the two local orders of a, and hence those of b by odd powering, have different 2-primary parts. They could not have a common exact order. Therefore a separator equality return proves

 s_P != s_Q.                                                       (6)

This phase costs soft O(N^(5/32)+sqrt(m)) bits. Running a separator for every candidate in the Jacobi scan would lose this bound; the algorithm explicitly does not do so.

## 6. Separate the unequal 2-adic fields

If phase one did not factor, let A_2=ceil(N^(5/64)). Scan all integers a=2,...,A_2. For each, first compute gcd(a,N), return a proper factor if present, and skip gcd N. For a unit, compute b=a^(K_0) and apply the separator with bound m. Return a factor whenever it is found; otherwise an exact common-order return allows continuing.

Let ell be the hidden prime with larger s_ell, whose existence and uniqueness follow from (6). By (5), some scanned a is a quadratic nonresidue modulo ell. Its local 2-primary order at ell is exactly 2^(s_ell), and at the other prime it is at most 2^(s_other), strictly smaller. Odd powering preserves this difference. At that a, the separator cannot return a common exact order, and (4) excludes NoHit. It must return a proper factor.

Each trial costs soft O(sqrt(m)) bits, with polylogarithmic powering and gcd included. Hence phase two costs soft O(N^(5/64)*sqrt(m)). With m=Theta(N^(1/6)),

 5/64+1/12=31/192<32/192=1/6,
 5/32=30/192<31/192.                                                (7)

The strict saving of 1/192 absorbs fixed logarithmic factors. Without an upper bound on m in terms of N, retain the first expression in (3); the assumptions N<=m^6 and P+Q<=3m³ alone would not justify substituting m=Theta(N^(1/6)).

## 7. Totality and acquisition boundary

The cutoffs A_1,A_2 are computable using fixed integer powers and integer roots. If either bounded phase finishes without its required success, use ordinary deterministic trial division to factor N. The same fallback can handle an unexpected NoHit. Under the promised inputs these fallback cases occur for only finitely many N by the uniform analytic theorem, so their finite cost is absorbed into the constant in (3). The algorithm need not know the threshold. Every returned factor is checked. This is an asymptotic bit-complexity theorem, not a claim of an explicit numerical Burgess threshold or a practical factoring speedup.

The old small-multiple extractor required a supplied annihilator with bounded quotient. The present theorem removes that arithmetic restriction and allows arbitrary polylogarithmic encoding length. Coupled with the paid uniform preprocessing, the remaining conditional input on every balanced semiprime is just a nonzero short global annihilator of the constructed base.

Obtaining that exponent at soft O(m) cost remains open. A short exponent exists (the local-order lcm, for example), but existence does not acquire its integer value. Neither the large-order search nor the two character scans produce it. The theorem does not obtain the original long collision query, transfer a collision-coverage theorem to a newly chosen base, or complete the all-input controller and Lean bit proof. Its separate consequence for supplied arbitrary-width explicit carrier covers is stated in wide-cover-certificate.md on the inherited qualified energy family.

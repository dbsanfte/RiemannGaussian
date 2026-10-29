# Axis short-factorial: executed cyclic-dilogarithm and smooth-order branches

26 October 2026. Scratch only. **No guaranteed softly O(k)=softly O(D^(2/5)) axis oracle is obtained.** The explicit cyclic-dilogarithm quotient retains a potentially singular weighted interior product. A deterministic target-cost smooth-order branch is executable but is known Pollard-type arithmetic and does not cover all possible native orders. The full-order fallback remains softly O(sqrt D); the familiar primorial square-root log-log gain changes no power.

## 1. Actual axis tile and what its zero asks

Use the complete original signed labels to preserve recovery. Put r=beta^k, so q=r^k. A horizontal axis (a,b)=(epsilon*k,0), lambda=tk, 0≤t<k, tested at the negative clock I=−i has exponent difference

    E−HI = k(epsilon+t+ki).

Thus, up to directly acquired powers/signs of units, its full t-tile is

    ∏_(i=1)^m ∏_(t=0)^(k−1)(1−r^(ki+t+epsilon))
      = ∏_(j=k+epsilon)^(k(m+1)+epsilon−1)(1−r^j).      (1)

Its length is D=km. The two signs have slightly shifted starts, not the same exact endpoint; retain them if the original folded axis query needs both. Vertical swaps preserve the known common-index coverage but have their N-shifted exponents; do not identify their numerical products with (1) without an actual identity. Original-row deletion and half-center metadata can remove unit or integer-zero factors; the identity here is for the displayed complete negative-clock horizontal tile. It is also the generic scalar orbit problem once an axis reduction supplies its exact start.

Both local orders d_P,d_Q of r exceed 16k² because q=r^k has that order bound. The lower endpoint A+1=k+epsilon is positive and far below either order. For an interval [A+1,B] with this start, its product is nonunit iff at least one of d_P,d_Q is ≤B, and zero iff both are ≤B: the first positive multiple of either order lies in the interval exactly in that case. This order-threshold characterization is specific to the axis factorial; it is not a way to acquire either order. Here B=Theta(D)=Theta(k^(5/2)).

## 2. Execute the finite cyclic-dilogarithm quotient, with the boundary retained

Primary source: Garoufalidis–Kashaev, *Evaluation of state integrals at rational points*, arXiv:1411.6062v2, §1.2, equations (9)–(10): https://arxiv.org/pdf/1411.6062 . Its cyclic dilogarithm is a fractional-power weighted finite product, and its short functional equation specializes to a supplied primitive root of unity. It is not a finite-field algorithm for an arbitrary native clock.

Remove fractional powers and work with the integer polynomial

    C_n(x;r)=∏_(j=1)^(n−1)(1−r^j x)^j.

A direct exponent shift proves, without assumptions on the order,

    C_n(rx;r) * ∏_(j=1)^(n−1)(1−r^j x)
       = (1−r^n x)^(n−1) C_n(x;r).                    (2)

Writing P_n(x;r)=∏_(j=0)^(n−1)(1−r^j x), the exact cleared form is

    C_n(rx;r) P_n(x;r)
       = (1−x)(1−r^n x)^(n−1) C_n(x;r).              (3)

At an acquired primitive n-th root this is compatible with P_n=1−x^n and the source's cyclic relation. At the actual r it retains both r^n and C_n. Taking x=r^(A+1), n=D targets (1) exactly.

**Paid endpoint branches.** Acquire r^(A+1), r^(A+D+1) and r^D by binary powering. For any tested nonzero integer exponent e, gcd(r^e−1,N) proper gives a factor. If it is N, beta^(ke)=1 is a nonzero O(log N)-bit global annihilator; the licensed prepared-base consumer factors in softly O(k). Otherwise 1−r^e is a unit. Hence the endpoint and would-be cyclic-specialization checks cost softly O(k), with all saturated branches handled. On the continuing branch r^D−1 is a unit, so treating r as a D-th root of unity is explicitly false.

Even when both endpoints of (3) are units, its denominator C_D(rx) need not be. At an interior hit, 1−r^(A+1+j)=0 for 1≤j<D, both weighted products in (3) may vanish. Their quotient then has no legal numerical meaning. A formal cancellation in the polynomial identity preserves the desired factors, but computing its canceled quotient is precisely the missing interior product. Neither an analytic branch of the fractional powers nor an auxiliary root-of-unity parameter acquires that quotient over R. This executes the candidate through its unit branches rather than merely noting that it has a constant-state description.

The degenerate n=0 product is 1 and n=1 is one scalar difference; use these directly. No fractional-power extension, analytic dilogarithm, or unknown-order period has been acquired.

## 3. A genuine target-cost conditional order algorithm

The following known smooth-order branch is executable in softly O(B^(2/5))=softly O(k), but is **not an all-orders solution**. Let y=ceil(B^(2/5)) and

    E_y=∏_(prime ell≤y) ell^floor(log_ell B).

Sieve the primes to y, and maintain u=r. For each prime ell in increasing order, replace

    u ← u^[ell^floor(log_ell B)],

then compute gcd(u−1,N). Each exponent is at most B. All work, including sieving and the gcd at every step, is softly O(y) ring/integer operations and softly O(y log N) bits. One need not materialize a large integer E_y.

If either actual local order ≤B has no prime factor above y, that order divides E_y and its prime is hit. If the other local order is not killed at the same step, the gcd is proper and finishes. On the prepared branch where the local orders of beta are also certified coprime, the local orders of r remain coprime. Then a first simultaneous kill is impossible: both nontrivial orders could become killed by the same newly introduced ell-power only if both contained ell. Therefore under this inherited coprimality refinement the scan factors N whenever at least one local order ≤B is y-smooth. This is an exact conditional success guarantee, not an average-case assertion.

If only the odd-order margins are supplied and cross-prime coprimality is omitted, the saturated gcd branch must not be claimed finished by the short-annihilator consumer: the accumulated exponent can have softly O(y) bits, not O(log N) bits. One may retain that case as unresolved or invoke a separately licensed general method. The above soft-k success claim explicitly uses the already available coprime-order refinement.

Primary provenance: Pollard's p−1 method, *Theorems on factorization and primality testing*, MPCPS 76 (1974), 521–528, DOI https://doi.org/10.1017/S0305004100049252 . Here the chosen base is the prepared r, and the sufficient condition concerns its actual order rather than all of p−1. The displayed guarantee and cost are directly proved above; this is not a new method or record.

On a continuing no-hit trace, any local order ≤B has a prime factor >y. Since y³>B, such an order has at most two prime factors above y, counted with multiplicity. It can still have a single prime factor almost B, or be a product of two large primes. Nothing in odd local order, the semiprime identity N=PQ, or the acquired beta establishes that these residual cases are absent. Replacing this remaining branch by a smooth-order density statement would not satisfy the guaranteed task. A stage-two scan of all remaining possible large primes reaches the original square-root scale up to logarithmic factors; no smaller exhaustive acquisition is derived here.

## 4. All-orders continuation and the actual target

For completeness, a division-free initialized all-orders fallback for P_D(x;r) is standard baby-step/giant-step. Choose b=ceil(sqrt D), acquire

    G(X)=∏_(j=0)^(b−1)(1−r^j X),

and evaluate G at x*r^(bt) for the complete blocks, multiplying the tail directly. Product trees and monic multipoint evaluation cost softly O(b+D/b). Every clock is a unit; repeated geometric points cause no division problem in monic evaluation. No target difference, 1−r^j, or unknown local order is inverted. Proper gcd and global-zero outputs are passed to the existing original-label localization. This supplies softly O(sqrt D)=softly O(k^(5/4)), not the requested exponent. Bostan–Yurkevich's primary Theorem 1 supplies the scalar q-Pochhammer square-root baseline: https://yurkevi.ch/data/Alin%20Bostan%2C%20Sergey%20Yurkevich_2020_Fast%20Computation%20of%20the%20N-th%20Term%20of%20a%20q-Holonomic%20Sequence%20and%20Applications.pdf . The monic construction above explains its collision-safe composite-ring continuation.

The already integrated primorial mask gives the familiar factor about 1/sqrt(loglog k) in the axis-dominated block scale. Costa–Harvey's *Faster deterministic integer factorization*, https://arxiv.org/abs/1201.2116 , is primary precedent for this wheel improvement. It is neither a D^(2/5) algorithm nor a new advance in this packet. A faster general factoring fallback would solve the whole problem independently and is not being counted as an axis identity.

The narrow constructive target exposed here is deterministic detection of a native local r-order in (16k²,B] after the explicit soft-k smooth-order scan, including prime and two-large-prime residual orders, or an algorithm for the singularly canceled quotient in (3) that retains every such hit. No acquired torus-knot/cyclic-dilogarithm identity inspected supplies that primitive. The unconditional all-native-instance bound remains softly O(sqrt D).
